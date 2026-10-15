# bench/

Reproducible correctness + profiling harness against the SATLIB uniform-random
3-SAT sets and the DIMACS challenge families.

## Layout

```
bench/
├── fetch.sh          download + extract SATLIB / DIMACS tarballs
├── fetch_satcomp.sh  download a SAT Competition 2025 subset
├── run.sh            run solver on every instance, verify verdicts
├── compare.py        compare against MiniSat, CaDiCaL, Kissat
├── build-solvers.sh  build CaDiCaL and Kissat into solvers/
├── .cache/           downloaded .tar.gz archives (gitignored)
└── instances/        extracted, flattened .cnf files (gitignored)
    ├── uf20-91 … uf250-1065      satisfiable random 3-SAT
    │                             (1000 each up to uf100, 100 above)
    ├── uuf50-218 … uuf250-1065   unsatisfiable random 3-SAT
    │                             (1000 each up to uuf100, 100 / 99 above)
    └── dimacs-*                  aim, jnh, dubois, pret, ssa, bf, ii,
                                  hanoi, parity
```

## Usage

```sh
# one-time (or whenever you want fresh copies)
bench/fetch.sh

# build the release binary once, then run the correctness sweep
zig build -Drelease=true
bench/run.sh
```

Both scripts accept set names to limit their scope:

```sh
bench/fetch.sh uf20-91
bench/run.sh   uf20-91 uuf50-218
```

`run.sh` compares each instance's exit code (10 = SAT, 20 = UNSAT) against
its known verdict and exits non-zero on any mismatch. `main.zig` also checks
every SAT model against the input formula before emitting `s SATISFIABLE`,
so a bogus SAT answer downgrades itself to `s UNKNOWN` + exit 0 rather than
lying — which `run.sh` will flag as a mismatch, pointing at the offending
instance.

## Source

All sets come from Holger Hoos' SATLIB archive:
<https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html>
