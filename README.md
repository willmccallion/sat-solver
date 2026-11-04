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
- **Chronological backtracking** when the backjump would skip many levels
- **Focused / stable mode alternation** with **rephasing** (best, original,
  inverted and random phases)
- **Preprocessing and level-0 inprocessing**, each on a propagation budget:
  backward subsumption with self-subsuming resolution (in practice mostly
  between binary clauses; see `subsume.zig`), equivalent-literal
  substitution (SCCs of the binary implication graph), bounded variable
  elimination, failed-literal probing, and vivification of low-LBD learned
  clauses
- **Arena compaction** to reclaim the holes left by deleted clauses
- **DRAT proof emission** (`--proof PATH`) for UNSAT verification
- **Model check against the input** — eliminated variables are
  reconstructed and every SAT model is checked against every clause of the
  original formula before `s SATISFIABLE` is printed; a failure is reported
  as `s UNKNOWN`
- **Tournament I/O** — streaming DIMACS CNF parsing (no input size cap),
  transparent `.gz` decompression,
  stdin input, `SIGINT` / `SIGTERM` / `SIGXCPU` + `--time-limit` handling,
  SAT Competition output format (`s SATISFIABLE` / `s UNSATISFIABLE` /
  `s UNKNOWN`, `v`-prefixed models, exit codes 10 / 20 / 0)

## Build

```sh
zig build                         # debug
zig build -Doptimize=ReleaseFast  # release
zig build test                    # unit tests + end-to-end
```

Requires Zig 0.17. `flake.nix` provides it (with `zls`) as a dev shell, which
`direnv` loads through `.envrc`.

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

## Sudoku

`sat-sudoku` solves a 9x9 Sudoku by encoding it as CNF for the solver: one
variable per (cell, digit), exactly one digit per cell, each digit exactly
once per row, column and box, and a unit clause per given digit.

```sh
zig build sudoku -- '53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79'
./zig-out/bin/sat-sudoku < puzzle.txt   # a 9-line grid works too
```

Cells are `1`-`9`, with `.` or `0` for blanks; input over 64 KiB is refused.
Exit code **0** = solved, **1** = no solution, **2** = bad input or no answer.

## Benchmarks

`zig build bench` runs the ReleaseFast solver on 399 random 3-SAT instances
(uf200-860, uuf200-860, uf250-1065, uuf250-1065) under `perf stat
-M TopdownL1` + `perf record --call-graph dwarf`, then prints a report
table with per-instance distribution, hardware counters, Intel Topdown L1
breakdown, call-graph hotspots, and `perf annotate` output for the hottest
function. Latest run, on an Intel Core i7-14700K:

```
wall time          234 930 ms  (589 ms / instance)
p50 / p90 / p99    129 ms / 1.91 s / 3.98 s

decisions           21.69 M
conflicts           18.49 M
propagations       855.02 M
restarts             8.04 k   (~1 per 2 300 conflicts)
reductions           3.86 k
peak RSS               40 MB

topdown L1
  retiring            18.5 %
  bad-speculation     49.3 %
  frontend-bound      21.7 %
  backend-bound       10.4 %

IPC                   1.27
branch-miss rate     11.1 %
L1d miss rate         2.86 %
```

`zig build bench-quick` runs the same harness on smaller uf100 / uuf100
instances (~4 s) for fast iteration during development.

Correctness is checked by `bench/run.sh`, which runs the release binary
against the downloaded SATLIB / DIMACS instances and compares exit codes
with the known verdicts: **5067 / 5067** across uf20, uf50, uf100, uuf50,
uuf100, and the dimacs-{dubois, pret, bf, ii, hanoi} families.

A stricter sweep over all 5826 instances that `bench/fetch.sh` downloads
(60 s per instance) solves 5816; the other 10 are the par32 instances.
Every SAT model was checked against the input CNF and every UNSAT DRAT
proof was accepted by `drat-trim`.

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

bench/compare.py --limit 10         # smoke run, this solver only
bench/compare.py --solvers sat-solver minisat cadical kissat
                                    # full run (300s CPU / 4 GB per instance)
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

Default run (uf200-860 + uuf200-860, 199 instances, 300 s CPU / 4 GB):

```
solver            solved  timeouts  errors    avg (solved)         PAR-2
sat-solver       199/199         0       0         0.08s        16.9s
minisat          199/199         0       0         0.09s        18.1s
kissat           199/199         0       0         0.15s        29.4s
cadical          199/199         0       0         0.18s        35.9s
```

MiniSat 2.2.1, CaDiCaL 3.0.1, Kissat 4.0.4. These instances take well
under a second, so per-instance overhead dominates; on large industrial
instances Kissat and CaDiCaL are far ahead.

## Known limitations

- **Far behind state-of-the-art solvers on industrial instances.** The
  random 3-SAT results above don't carry over to large structured
  formulas.
- **Some hard instances stay unsolved.** The 10 par32 instances time out
  at 60 s, and `b19_1` from the SAT Competition 2025 set is not solved
  within an hour.
- **Bounded variable elimination can blow up memory.** A single
  inprocessing BVE pass has no bound on the resolvents it adds; on
  `pj2016_k100` it adds about 450 M arena slots of chained resolvents and
  peaks at 14 GiB.
- **One solve per formula.** Search is single-threaded, and there are no
  assumptions or incremental clause additions between solves, so a caller
  such as `sat-sudoku` builds a fresh solver for each formula.

## Implementation notes

The CDCL core lives in `src/search/`. Major subsystems:

- **`propagate.zig`** — two-watched-literal BCP with blocker + in-place
  watcher list compaction, and a separate fast path for binary clauses
  that never touches the arena. The hot loop dominates runtime; the hot
  instructions are the watcher store, clause-header load, and the `cmpb`
  against the literal-indexed value table.
- **`analyze.zig`** — 1-UIP walk backward through the trail, followed by
  recursive minimization. Each non-asserting literal in the learned clause
  is checked for self-subsuming redundancy via an iterative `litRedundant`
  with a 64-bit `abstract_levels` bitmask fast-reject.
- **`solve.zig`** — preprocessing, then the main loop with the Glucose
  restart decision: bias-corrected fast / slow LBD EMAs (`α = 1/50` and
  `1/10 000`), restart ratio threshold `1.25`, trail-length blocker at
  `1.4 × trail_fast`. Reductions, rephasing, mode switches and every
  inprocessing pass run at level 0 on their own conflict schedules.
- **`inprocess/`** — `reduce.zig` (LBD-based reduction, arena compaction),
  `subsume.zig`, `equiv.zig`, `bve.zig`, `probe.zig` and `vivify.zig`.
  Each emits DRAT additions before deletions so proofs stay checkable;
  BVE and equivalence substitution record witnesses that `model.zig`
  replays to extend a model to the eliminated variables.

`src/core/assignment.zig` holds the trail, decision levels, and the
literal-indexed `lit_values` table — updated in pairs of adjacent slots so
`valueOfLiteral(lit)` is a single load + compare on the caller side.

`src/tools/profile.zig` is the `zig build bench` orchestrator — it spawns
the solver under `perf stat` and `perf record`, parses the output, and
renders the box-drawing report with ANSI-colored verdicts for each metric.

## Layout

```
src/
├── main.zig         CLI entry point
├── root.zig         library entry point for unit tests
├── core/            Literal / Formula, clause arena layout, assignment trail
├── io/              streaming DIMACS parser, DRAT writer
├── heuristics/      VSIDS heap, restart / rephase / mode schedules
├── search/          CDCL loop, propagate, analyze, backtrack, model extension
│   └── inprocess/   subsume, equiv, bve, probe, vivify, reduce + compact
└── tools/           bench (batch runner), profile (perf), compete (readiness),
                     sudoku (Sudoku via CNF)

bench/
├── fetch.sh         downloads SATLIB + DIMACS instance sets
├── fetch_satcomp.sh downloads a SAT Competition 2025 subset
├── run.sh           correctness sweep with per-set timing
├── compare.py       side-by-side comparison against reference solvers
├── build-solvers.sh builds CaDiCaL and Kissat for compare.py
└── README.md        bench directory layout + usage

tests/
├── unit.zig         unit tests
└── fixtures/        small .cnf files for round-trip tests
```

## License

MIT. See [`LICENSE`](LICENSE).
