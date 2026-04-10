# bench/

Reproducible correctness + profiling harness against the SATLIB uniform-random
3-SAT benchmark sets.

## Layout

```
bench/
├── fetch.sh        download + extract SATLIB tarballs
├── run.sh          run solver on every instance, verify verdicts
├── .cache/         downloaded .tar.gz archives (gitignored)
└── instances/      extracted, flattened .cnf files (gitignored)
    ├── uf20-91/    1000 SAT instances, 20 vars / 91 clauses
    ├── uf50-218/   1000 SAT instances, 50 vars / 218 clauses
    ├── uf100-430/  1000 SAT instances, 100 vars / 430 clauses
    ├── uuf50-218/   100 UNSAT instances, 50 vars / 218 clauses
    └── uuf100-430/  100 UNSAT instances, 100 vars / 430 clauses
```

## Usage

```sh
# one-time (or whenever you want fresh copies)
bench/fetch.sh

# build the release binary once, then run the correctness sweep
zig build -Doptimize=ReleaseFast
bench/run.sh
```

Both scripts accept set names to limit their scope:

```sh
bench/fetch.sh uf20-91
bench/run.sh   uf20-91 uuf50-218
```

`run.sh` compares each instance's exit code (10 = SAT, 20 = UNSAT) against
its known verdict and exits non-zero on any mismatch. `main.zig` also runs
`verifyModel` before emitting `s SATISFIABLE`, so a bogus SAT answer
downgrades itself to `s UNKNOWN` + exit 0 rather than lying — which
`run.sh` will flag as a mismatch, pointing at the offending instance.

## Source

All sets come from Holger Hoos' SATLIB archive:
<https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html>
