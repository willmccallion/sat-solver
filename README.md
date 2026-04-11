# sat-solver

A CDCL SAT solver in Zig, built from scratch with an emphasis on perf-profiled
BCP, modern clause learning, and SAT Competition-format I/O.

## Features

- **CDCL with 1-UIP conflict analysis** and recursive clause minimization
  (MiniSat 2.2 `litRedundant`)
- **Two-watched-literal BCP** with blocker optimization and in-place watcher
  list compaction
- **Literal-indexed value table** — one load + one compare per
  `valueOfLiteral` call, collapsing the 8-instruction / 3-branch chain that
  dominated earlier profiles
- **Flat clause arena** — a single `ArrayList(Literal)` backing store with
  2-slot headers; 3-literal clauses fit on one cache line
- **Glucose-style adaptive restarts** — fast / slow LBD EMAs with Adam-style
  bias correction, plus a trail-length blocker that vetoes restarts when
  the current decision stack is clearly making progress
- **LBD-based clause DB reduction** with glue (LBD ≤ 2) and locked-reason
  protection, on an independent conflict-count budget
- **VSIDS branching** with exponential activity decay and phase saving
- **DRAT proof emission** (`--proof PATH`) for UNSAT verification
- **Tournament I/O** — DIMACS CNF parsing, transparent `.gz` decompression,
  stdin input, `SIGINT` / `SIGTERM` / `SIGXCPU` + `--time-limit` handling,
  SAT Competition output format (`s SATISFIABLE` / `s UNSATISFIABLE` /
  `s UNKNOWN`, `v`-prefixed models, exit codes 10 / 20 / 0)

## Build

```sh
zig build                         # debug
zig build -Doptimize=ReleaseFast  # release
zig build test                    # unit tests + end-to-end
```

Requires Zig 0.15.2 or newer.

## Usage

```sh
# Read from a file:
./zig-out/bin/sat path/to/formula.cnf

# Read compressed input:
./zig-out/bin/sat path/to/formula.cnf.gz

# Read from stdin:
./zig-out/bin/sat < formula.cnf

# Emit a DRAT proof for UNSAT verification:
./zig-out/bin/sat --proof formula.drat formula.cnf

# With a wall-clock timeout:
./zig-out/bin/sat --time-limit 60 formula.cnf
```

Exit codes follow SAT Competition convention: **10** = SATISFIABLE,
**20** = UNSATISFIABLE, **0** = UNKNOWN (including on interrupt or timeout).

## Benchmarks

`zig build bench` runs the ReleaseFast solver on 399 random 3-SAT instances
(uf200-860, uuf200-860, uf250-1065, uuf250-1065) under `perf stat
-M TopdownL1` + `perf record --call-graph dwarf`, then prints a report
table with per-instance distribution, hardware counters, Intel Topdown L1
breakdown, call-graph hotspots, and `perf annotate` output for the hottest
function. Latest run:

```
wall time          182 003 ms  (456 ms / instance)
p50 / p90 / p99    117 ms / 1.30 s / 3.29 s

decisions           22.05 M
conflicts           18.72 M
propagations       798.36 M
restarts            17.04 k   (~1 per 1 100 conflicts)
reductions           4.01 k
peak RSS               57 MB

topdown L1
  retiring            18.7 %
  bad-speculation     53.7 %
  frontend-bound      19.6 %
  backend-bound        8.0 %

IPC                   1.12
branch-miss rate     12.0 %
L1d miss rate         4.90 %
```

`zig build bench-quick` runs the same harness on smaller uf100 / uuf100
instances (~4 s) for fast iteration during development.

Correctness is checked by `bench/run.sh`, which runs the release binary
against every downloaded SATLIB / DIMACS instance and verifies exit codes
against known verdicts. Currently passing **5067 / 5067** instances across
uf20, uf50, uf100, uuf50, uuf100, and the dimacs-{dubois, pret, bf, ii,
hanoi} families.

## Comparison against reference solvers

`bench/compare.py` runs this solver side-by-side with MiniSat, CaDiCaL,
and Kissat under hard `RLIMIT_CPU` and `RLIMIT_AS` limits, cross-checks
verdicts to catch correctness bugs, and reports per-solver PAR-2 scores
plus a cactus plot.

To reproduce:

```sh
bench/build-solvers.sh              # clones + builds CaDiCaL and Kissat
                                    # into bench/solvers/
                                    # MiniSat: apt install minisat2

zig build -Doptimize=ReleaseFast    # our solver

bench/compare.py --limit 10         # smoke run, 10 instances per dir
bench/compare.py                    # full run (300s CPU / 4 GB per instance)
```

Methodology notes (all SAT Competition standard):

- **Time limit** is enforced via `setrlimit(RLIMIT_CPU)` inside the forked
  child just before `execvp`. CPU time, not wall time, so system load and
  thermal throttling don't confound the comparison. Default 300 s.
- **Memory limit** via `setrlimit(RLIMIT_AS)`. Default 4 GB.
- **CPU time + peak RSS** collected via `os.wait4` rusage, not a
  GNU-time wrapper, so there's no extra process in the measurement path.
- **Verdict cross-check**: if any two solvers produce different decisive
  verdicts (SAT vs UNSAT) on the same instance, one of them is wrong —
  flagged as a `CORRECTNESS WARNING` and the script exits non-zero.
- **PAR-2 scoring**: solved instances contribute their CPU time, unsolved
  (timeout / error) instances contribute 2 × timeout. Lower is better.
  This is how SAT Competition ranks solvers.
- **Cactus plot**: sorted per-instance CPU times per solver, plotted on a
  log-scale y-axis. The curve that stays lower / further right wins.

Results go to `bench/compare-results.csv` and `bench/compare-cactus.png`.

*Comparison numbers will be filled in after the first full run.*

## Implementation notes

The CDCL core lives in `src/solver.zig`. Major subsystems:

- **`propagate()`** — two-watched-literal BCP with blocker + in-place
  watcher list compaction. The hot loop dominates runtime (~70 % of wall
  time); the hot instructions are the watcher store, clause-header load,
  and the `cmpb` against the literal-indexed value table.
- **`analyze()`** — 1-UIP walk backward through the trail, followed by
  recursive minimization. Each non-asserting literal in the learned clause
  is checked for self-subsuming redundancy via an iterative `litRedundant`
  with a 64-bit `abstract_levels` bitmask fast-reject.
- **`reduceDB()`** — sorts learned clauses by LBD, deletes the worst half,
  protects locked-reason and glue (LBD ≤ 2) clauses. Runs on its own
  conflict-count budget, piggybacking onto the next restart to land at
  level 0.
- **`solve()`** — main loop with the Glucose restart decision: bias-
  corrected fast / slow LBD EMAs (`α = 1/50` and `1/10 000`), restart ratio
  threshold `1.25`, trail-length blocker at `1.4 × trail_fast`.

`src/assignment.zig` holds the trail, decision levels, and the literal-
indexed `lit_values` table — updated in pairs of adjacent slots so
`valueOfLiteral(lit)` is a single load + compare on the caller side.

`src/profile.zig` is the `zig build bench` orchestrator — it spawns the
solver under `perf stat` and `perf record`, parses the output, and renders
the box-drawing report with ANSI-colored verdicts for each metric.

## Layout

```
src/
├── main.zig         CLI entry point
├── solver.zig       CDCL core — propagate, analyze, reduceDB
├── assignment.zig   trail, lit_values table, phase saving
├── cnf.zig          Literal, Clause, Formula types
├── parser.zig       DIMACS CNF parser (+ gzip handling)
├── bench.zig        batch runner driven by `zig build bench`
├── profile.zig      perf-stat + perf-record orchestrator
├── compete.zig      SAT Competition 2025 readiness checker
└── root.zig         library entry point for unit tests

bench/
├── fetch.sh         downloads SATLIB + DIMACS instance sets
├── run.sh           correctness sweep with per-set timing
└── README.md        bench directory layout + usage

tests/
├── unit.zig         unit tests
└── fixtures/        small .cnf files for round-trip tests
```

## License

MIT. See [`LICENSE`](LICENSE).
