#!/usr/bin/env python3
"""Compare sat-solver against reference CDCL solvers on SAT instances.

Runs each (solver, instance) pair under a CPU-time limit (RLIMIT_CPU) and
memory limit (RLIMIT_AS), collects verdict + CPU/wall time + peak RSS,
cross-checks verdicts across solvers to catch correctness bugs, and prints
a PAR-2 summary table. Optionally writes a CSV and a cactus-plot PNG.

Usage:
    bench/compare.py [--timeout 300] [--mem 4096] \\
                     [--instances DIR ...] [--solvers NAME ...] \\
                     [--out PATH] [--plot PATH] [--limit N] [--dry-run]

Methodology notes:
  - Resource limits enforced via setrlimit(RLIMIT_CPU) and setrlimit(RLIMIT_AS)
    in the child process immediately before exec. This is the SAT Competition
    standard; each solver gets the same hard deadline.
  - CPU time is measured via os.wait4's rusage (ru_utime + ru_stime), not
    wall time, so system load doesn't confound the comparison.
  - Wall time is captured separately as a sanity check and as a safety net
    (2x CPU limit + 10s) in case a solver hangs on signal handling.
  - PAR-2 scoring: each unsolved instance contributes 2x the timeout to the
    running total. Lower is better. This is how SAT Competition ranks solvers.
  - Verdict cross-check: if two solvers report different decisive verdicts
    (SAT vs UNSAT) on the same instance, one of them is wrong — flagged as
    a CORRECTNESS WARNING and the exit code is non-zero.

Defaults target bench/instances/uf200-860 and bench/instances/uuf200-860
with a 300s CPU limit and 4 GB memory limit, writing results to
bench/compare-results.csv and bench/compare-cactus.png.
"""

from __future__ import annotations

import argparse
import csv
import os
import resource
import select
import shutil
import signal
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent


# ---------------------------------------------------------------------------
# Solver discovery
# ---------------------------------------------------------------------------

SOLVER_CANDIDATES: Dict[str, List[Path]] = {
    "sat-solver": [
        REPO_ROOT / "zig-out" / "bin" / "sat",
    ],
    "cadical": [
        SCRIPT_DIR / "solvers" / "cadical" / "build" / "cadical",
        Path("/usr/bin/cadical"),
        Path("/usr/local/bin/cadical"),
    ],
    "kissat": [
        SCRIPT_DIR / "solvers" / "kissat" / "build" / "kissat",
        Path("/usr/bin/kissat"),
        Path("/usr/local/bin/kissat"),
    ],
    "minisat": [
        Path("/usr/bin/minisat"),
        Path("/usr/bin/minisat2"),
        Path("/usr/local/bin/minisat"),
    ],
}


def find_solver(name: str) -> Optional[Path]:
    """Locate a solver binary. Checks known paths first, then $PATH."""
    for candidate in SOLVER_CANDIDATES.get(name, []):
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    # Fall back to $PATH under the given name, then common aliases.
    for alias in (name, f"{name}2"):
        found = shutil.which(alias)
        if found:
            return Path(found)
    return None


# ---------------------------------------------------------------------------
# Result record
# ---------------------------------------------------------------------------

@dataclass
class Result:
    solver: str
    instance: str
    verdict: str  # SAT, UNSAT, UNKNOWN, TIMEOUT, ERROR
    cpu_time: float
    wall_time: float
    maxrss_kb: int
    exit_code: int
    stdout_tail: str = ""
    stderr_tail: str = ""


# ---------------------------------------------------------------------------
# Runner — fork + setrlimit + exec + wait4
# ---------------------------------------------------------------------------

STRICT_PARSER_SOLVERS = frozenset({"minisat", "cadical", "kissat"})


def sanitize_satlib_footer(instance_path: Path) -> Tuple[Path, Optional[Path]]:
    """Strip the SATLIB-style `%\\n0\\n` trailing marker if present.

    SATLIB uf/uuf .cnf files end with a legacy

        %
        0

    footer that strict DIMACS parsers reject with "expected digit or '-'"
    (MiniSat 2.2, CaDiCaL, and Kissat all bail on this — they're correct
    per the DIMACS spec, and SATLIB is technically non-conformant).
    Our Zig parser tolerates trailing garbage, but to keep the comparison
    fair we feed the stricter solvers a cleaned copy. Returns a pair of
    `(path_to_use, temp_path_to_cleanup_or_None)`. If no cleanup needed,
    the original path is returned with `None`.
    """
    # Read enough of the end of the file to detect the footer. Skip .gz
    # entirely — MiniSat wouldn't read compressed input anyway.
    if instance_path.suffix == ".gz":
        return instance_path, None
    try:
        with open(instance_path, "rb") as f:
            f.seek(max(0, f.seek(0, 2) - 16))
            tail = f.read()
    except OSError:
        return instance_path, None

    if b"%" not in tail:
        return instance_path, None

    # Read the full file, strip everything from the first `%` line onward.
    with open(instance_path, "rb") as f:
        data = f.read()
    cut = len(data)
    for idx, line in enumerate(data.splitlines(keepends=True)):
        if line.strip() == b"%":
            cut = sum(len(ln) for ln in data.splitlines(keepends=True)[:idx])
            break
    if cut == len(data):
        return instance_path, None

    fd, tmp_name = tempfile.mkstemp(
        prefix=f"{instance_path.stem}-minisat-", suffix=".cnf"
    )
    with os.fdopen(fd, "wb") as out:
        out.write(data[:cut])
    return Path(tmp_name), Path(tmp_name)


def run_one(
    solver_name: str,
    solver_bin: Path,
    instance_path: Path,
    cpu_secs: int,
    mem_kb: int,
) -> Result:
    """Run a single (solver, instance) pair under hard resource limits.

    We use raw os.fork + os.execvp + os.wait4 rather than subprocess.Popen
    because Popen.communicate() reaps the child internally, which prevents
    us from collecting rusage (CPU time, peak RSS) via wait4 afterwards.
    """
    # Strict-parser solvers (minisat, cadical, kissat) reject the SATLIB
    # `%\n0\n` footer. Strip it to a temp file for those solvers, leave
    # our Zig solver on the raw file (it tolerates trailing garbage and
    # the historical numbers in the README were measured that way).
    original_name = instance_path.name
    cleanup_path: Optional[Path] = None
    if solver_name in STRICT_PARSER_SOLVERS:
        instance_path, cleanup_path = sanitize_satlib_footer(instance_path)

    stdout_r, stdout_w = os.pipe()
    stderr_r, stderr_w = os.pipe()

    wall_start = time.monotonic()
    pid = os.fork()

    if pid == 0:
        # --- child ---
        try:
            os.close(stdout_r)
            os.close(stderr_r)
            os.dup2(stdout_w, 1)
            os.dup2(stderr_w, 2)
            os.close(stdout_w)
            os.close(stderr_w)

            # Hard CPU and memory limits. +5s soft margin on CPU so the
            # solver gets SIGXCPU first and can exit cleanly before SIGKILL.
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_secs, cpu_secs + 5))
            mem_bytes = mem_kb * 1024
            resource.setrlimit(resource.RLIMIT_AS, (mem_bytes, mem_bytes))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

            os.execvp(str(solver_bin), [str(solver_bin), str(instance_path)])
        except Exception as exc:
            os.write(2, f"child exec failed: {exc}\n".encode())
            os._exit(127)

    # --- parent ---
    os.close(stdout_w)
    os.close(stderr_w)

    stdout_buf = bytearray()
    stderr_buf = bytearray()
    fds: Dict[int, bytearray] = {stdout_r: stdout_buf, stderr_r: stderr_buf}

    # Wall-time safety net: 2x the CPU limit + 10s slack. If the solver
    # wedges on signal handling, we kill it directly.
    wall_deadline = wall_start + cpu_secs * 2 + 10
    killed_by_wall = False

    while fds:
        remaining = max(0.1, wall_deadline - time.monotonic())
        ready, _, _ = select.select(list(fds.keys()), [], [], remaining)
        if not ready:
            if time.monotonic() > wall_deadline:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                killed_by_wall = True
                break
            continue
        for fd in ready:
            chunk = os.read(fd, 65536)
            if not chunk:
                os.close(fd)
                del fds[fd]
            else:
                fds[fd].extend(chunk)

    for fd in list(fds.keys()):
        try:
            os.close(fd)
        except OSError:
            pass

    _, status, rusage = os.wait4(pid, 0)
    wall_time = time.monotonic() - wall_start
    cpu_time = rusage.ru_utime + rusage.ru_stime
    # On Linux ru_maxrss is in KB; on macOS it's in bytes. We're targeting
    # Linux (the perf harness is Linux-only anyway), so treat as KB.
    maxrss_kb = int(rusage.ru_maxrss)

    exit_code = os.WEXITSTATUS(status) if os.WIFEXITED(status) else -1
    killed_by = os.WTERMSIG(status) if os.WIFSIGNALED(status) else 0

    stdout_str = stdout_buf.decode("utf-8", errors="replace")
    stderr_str = stderr_buf.decode("utf-8", errors="replace")

    verdict = parse_verdict(stdout_str, exit_code)

    # Post-process verdict based on how the child died.
    if killed_by_wall:
        verdict = "TIMEOUT"
    elif killed_by == signal.SIGXCPU:
        verdict = "TIMEOUT"
    elif cpu_time >= cpu_secs * 0.99 and verdict == "UNKNOWN":
        verdict = "TIMEOUT"
    elif killed_by in (signal.SIGSEGV, signal.SIGABRT, signal.SIGBUS):
        verdict = "ERROR"
    elif killed_by == signal.SIGKILL and verdict == "UNKNOWN":
        # Likely OOM (RLIMIT_AS hit) or wall-time fallback.
        verdict = "ERROR"

    if cleanup_path is not None:
        try:
            cleanup_path.unlink()
        except OSError:
            pass

    return Result(
        solver=solver_name,
        instance=original_name,
        verdict=verdict,
        cpu_time=cpu_time,
        wall_time=wall_time,
        maxrss_kb=maxrss_kb,
        exit_code=exit_code,
        stdout_tail=stdout_str[-400:],
        stderr_tail=stderr_str[-400:],
    )


# ---------------------------------------------------------------------------
# Verdict parsing
# ---------------------------------------------------------------------------

def parse_verdict(stdout: str, exit_code: int) -> str:
    """Parse a SAT Competition-style verdict.

    Primary source is the exit code (10 = SAT, 20 = UNSAT, 0 = unknown)
    because every SAT-Comp-compliant solver sets it. Fallback parses the
    status line from stdout, tolerating MiniSat-style bare 'SATISFIABLE'
    output in addition to the standard 's SATISFIABLE' prefix.
    """
    if exit_code == 10:
        return "SAT"
    if exit_code == 20:
        return "UNSAT"
    for line in stdout.splitlines():
        s = line.strip()
        if s in ("s SATISFIABLE", "SATISFIABLE"):
            return "SAT"
        if s in ("s UNSATISFIABLE", "UNSATISFIABLE"):
            return "UNSAT"
        if s in ("s UNKNOWN", "UNKNOWN", "INDETERMINATE"):
            return "UNKNOWN"
    return "UNKNOWN"


# ---------------------------------------------------------------------------
# Instance discovery + cross-check + scoring
# ---------------------------------------------------------------------------

def collect_instances(dirs: List[Path], limit: Optional[int]) -> List[Path]:
    """Gather .cnf and .cnf.gz files from the given directories, sorted."""
    instances: List[Path] = []
    for d in dirs:
        if not d.is_dir():
            print(f"warning: {d} is not a directory, skipping", file=sys.stderr)
            continue
        for f in sorted(d.iterdir()):
            if f.suffix == ".cnf" or f.name.endswith(".cnf.gz"):
                instances.append(f)
    if limit is not None:
        instances = instances[:limit]
    return instances


def check_verdicts(results: List[Result]) -> List[str]:
    """Return a list of disagreement warnings across solvers on the same
    instance. Ignores UNKNOWN / TIMEOUT / ERROR (no claim made)."""
    by_instance: Dict[str, List[Result]] = {}
    for r in results:
        by_instance.setdefault(r.instance, []).append(r)

    warnings: List[str] = []
    for instance, rs in sorted(by_instance.items()):
        decisive = {r.verdict for r in rs if r.verdict in ("SAT", "UNSAT")}
        if len(decisive) > 1:
            detail = ", ".join(
                f"{r.solver}={r.verdict}"
                for r in sorted(rs, key=lambda r: r.solver)
            )
            warnings.append(f"DISAGREEMENT on {instance}: {detail}")
    return warnings


def par2(results: List[Result], timeout: float) -> float:
    """PAR-2 score: solved instances contribute cpu_time, unsolved contribute
    2 * timeout. Lower is better. This is the official SAT Competition
    summary metric."""
    total = 0.0
    for r in results:
        if r.verdict in ("SAT", "UNSAT"):
            total += r.cpu_time
        else:
            total += 2 * timeout
    return total


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def print_summary(
    results_by_solver: Dict[str, List[Result]],
    timeout: int,
) -> None:
    print()
    header = (
        f"{'solver':<14}{'solved':>10}{'timeouts':>10}{'errors':>8}"
        f"{'avg (solved)':>16}{'PAR-2':>14}"
    )
    print(header)
    print("-" * len(header))

    # Sort so the best solver (lowest PAR-2) is first — makes the table
    # easier to scan when you have >3 solvers.
    entries = sorted(
        results_by_solver.items(),
        key=lambda kv: par2(kv[1], timeout),
    )
    for solver, results in entries:
        solved = [r for r in results if r.verdict in ("SAT", "UNSAT")]
        timeouts = [r for r in results if r.verdict == "TIMEOUT"]
        errors = [r for r in results if r.verdict == "ERROR"]
        n_total = len(results)
        avg = (sum(r.cpu_time for r in solved) / len(solved)) if solved else 0.0
        p2 = par2(results, timeout)
        print(
            f"{solver:<14}{len(solved):>6}/{n_total:<3}"
            f"{len(timeouts):>10}{len(errors):>8}"
            f"{avg:>13.2f}s{p2:>12.1f}s"
        )
    print()


def write_csv(results: List[Result], path: Path) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "solver", "instance", "verdict",
            "cpu_time", "wall_time", "maxrss_kb", "exit_code",
        ])
        for r in results:
            w.writerow([
                r.solver, r.instance, r.verdict,
                f"{r.cpu_time:.3f}", f"{r.wall_time:.3f}",
                r.maxrss_kb, r.exit_code,
            ])


def plot_cactus(
    results_by_solver: Dict[str, List[Result]],
    path: Path,
) -> bool:
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print(
            "warning: matplotlib not installed — skipping cactus plot.\n"
            "  install with: pip install matplotlib\n"
            "  or:           apt install python3-matplotlib",
            file=sys.stderr,
        )
        return False

    fig, ax = plt.subplots(figsize=(9, 5.5))
    for solver, results in results_by_solver.items():
        solved_times = sorted(
            r.cpu_time for r in results if r.verdict in ("SAT", "UNSAT")
        )
        if not solved_times:
            continue
        x = list(range(1, len(solved_times) + 1))
        ax.plot(x, solved_times, label=solver, marker=".", markersize=4)

    ax.set_xlabel("Instances solved (sorted by time)")
    ax.set_ylabel("CPU time (s)")
    ax.set_yscale("log")
    ax.set_title("Cactus plot — lower / right is better")
    ax.legend(loc="upper left")
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    fig.savefig(path, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return True


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Compare sat-solver against reference CDCL solvers.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--timeout", type=int, default=300,
                    help="CPU time limit per instance, seconds (default: 300)")
    ap.add_argument("--mem", type=int, default=4096,
                    help="Memory limit per instance, MB (default: 4096)")
    ap.add_argument("--instances", nargs="+", default=[
        str(REPO_ROOT / "bench" / "instances" / "uf200-860"),
        str(REPO_ROOT / "bench" / "instances" / "uuf200-860"),
    ], help="Instance directories to benchmark")
    ap.add_argument("--solvers", nargs="+",
                    default=["sat-solver", "minisat", "cadical", "kissat"],
                    help="Solvers to compare")
    ap.add_argument("--out", type=Path,
                    default=SCRIPT_DIR / "compare-results.csv",
                    help="CSV output path")
    ap.add_argument("--plot", type=Path,
                    default=SCRIPT_DIR / "compare-cactus.png",
                    help="Cactus plot PNG output path")
    ap.add_argument("--limit", type=int, default=None,
                    help="Limit instances per directory (for quick testing)")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print what would run and exit")
    args = ap.parse_args()

    # Resolve solvers.
    solvers: Dict[str, Path] = {}
    for name in args.solvers:
        p = find_solver(name)
        if p is None:
            print(f"warning: solver {name!r} not found, skipping", file=sys.stderr)
            if name == "sat-solver":
                print("  build with: zig build -Doptimize=ReleaseFast",
                      file=sys.stderr)
            elif name in ("cadical", "kissat"):
                print("  build with: bench/build-solvers.sh", file=sys.stderr)
            elif name == "minisat":
                print("  install with: apt install minisat2  (Debian / Ubuntu)",
                      file=sys.stderr)
            continue
        solvers[name] = p

    if not solvers:
        print("error: no solvers found", file=sys.stderr)
        return 2

    instance_dirs = [Path(d) for d in args.instances]
    instances = collect_instances(instance_dirs, args.limit)
    if not instances:
        print("error: no .cnf or .cnf.gz files found", file=sys.stderr)
        return 2

    print("Plan:")
    for name, p in solvers.items():
        print(f"  {name:<12} {p}")
    print(f"  instances: {len(instances)} across {len(instance_dirs)} dirs")
    print(f"  CPU limit: {args.timeout}s   mem limit: {args.mem} MB")
    print(f"  total runs: {len(solvers) * len(instances)}")
    print()

    if args.dry_run:
        return 0

    results: List[Result] = []
    mem_kb = args.mem * 1024
    try:
        for i, instance in enumerate(instances, 1):
            for solver_name, solver_bin in solvers.items():
                sys.stdout.write(
                    f"[{i:>4}/{len(instances)}] {solver_name:<12} "
                    f"{instance.name:<42}"
                )
                sys.stdout.flush()
                r = run_one(
                    solver_name, solver_bin, instance,
                    args.timeout, mem_kb,
                )
                results.append(r)
                print(f" {r.verdict:<8} {r.cpu_time:>8.2f}s")
    except KeyboardInterrupt:
        print("\ninterrupted — writing partial results", file=sys.stderr)

    write_csv(results, args.out)
    print(f"\nresults written to {args.out}")

    results_by_solver: Dict[str, List[Result]] = {
        name: [r for r in results if r.solver == name] for name in solvers
    }

    warnings = check_verdicts(results)
    if warnings:
        print("\n!!! CORRECTNESS WARNINGS !!!", file=sys.stderr)
        for w in warnings:
            print(f"  {w}", file=sys.stderr)

    print_summary(results_by_solver, args.timeout)

    if args.plot and plot_cactus(results_by_solver, args.plot):
        print(f"cactus plot written to {args.plot}")

    return 1 if warnings else 0


if __name__ == "__main__":
    sys.exit(main())
