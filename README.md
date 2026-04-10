# sat

A SAT solver in Zig, targeting the annual
[SAT Competition](https://satcompetition.github.io).

## Build

```sh
zig build                        # debug
zig build -Doptimize=ReleaseFast # benchmarking
zig build test                   # unit tests + round-trip
```

## Run

```sh
./zig-out/bin/sat path/to/file.cnf
./zig-out/bin/sat < file.cnf
```

## Output

Follows the SAT Competition format on stdout:

- `s SATISFIABLE` — followed by `v <literals> 0` model lines
- `s UNSATISFIABLE`
- `s UNKNOWN`

Exit codes: `10` (SAT), `20` (UNSAT), `0` (UNKNOWN).
