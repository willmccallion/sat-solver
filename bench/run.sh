#!/usr/bin/env bash
# bench/run.sh — run ./zig-out/bin/sat against every downloaded benchmark
# instance, verify the exit code matches the expected SAT/UNSAT verdict,
# and print a per-set timing summary.
#
# Usage: bench/run.sh [set_name ...]
#
# With no arguments, runs every set that exists under bench/instances/.
# Exits non-zero if any instance disagrees with its expected verdict.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INSTANCES_DIR="$SCRIPT_DIR/instances"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
SOLVER="$REPO_DIR/zig-out/bin/sat"

if [[ ! -x "$SOLVER" ]]; then
    printf 'error: %s not found. build first with:\n  zig build -Drelease=true\n' "$SOLVER" >&2
    exit 2
fi

# set_name -> expected exit code (10 = SAT, 20 = UNSAT)
declare -A EXPECTED=(
    [uf20-91]=10
    [uf50-218]=10
    [uf100-430]=10
    [uf150-645]=10
    [uf200-860]=10
    [uf250-1065]=10
    [uuf50-218]=20
    [uuf100-430]=20
    [uuf150-645]=20
    [uuf200-860]=20
    [uuf250-1065]=20
    # DIMACS stress families with a single known verdict.
    # Mixed-verdict families (aim, jnh, ssa) and solver-killers
    # (parity — times out) aren't listed here and are skipped.
    [dimacs-dubois]=20
    [dimacs-pret]=20
    [dimacs-bf]=20
    [dimacs-ii]=10
    [dimacs-hanoi]=10
)

if [[ $# -gt 0 ]]; then
    SETS_TO_RUN=("$@")
else
    SETS_TO_RUN=(
        uf20-91 uf50-218 uuf50-218 uf100-430 uuf100-430
        dimacs-dubois dimacs-pret dimacs-bf dimacs-ii dimacs-hanoi
    )
fi

total=0
mismatches=0
declare -a FAILED

for set_name in "${SETS_TO_RUN[@]}"; do
    expected="${EXPECTED[$set_name]-}"
    if [[ -z "$expected" ]]; then
        printf 'skip: unknown set %s\n' "$set_name" >&2
        continue
    fi
    dir="$INSTANCES_DIR/$set_name"
    if [[ ! -d "$dir" ]]; then
        printf 'skip: %s not downloaded (run bench/fetch.sh)\n' "$set_name" >&2
        continue
    fi

    set_total=0
    set_mismatches=0
    start=$(date +%s.%N)

    for cnf in "$dir"/*.cnf; do
        [[ -e "$cnf" ]] || continue
        set_total=$((set_total + 1))
        total=$((total + 1))
        set +e
        "$SOLVER" "$cnf" > /dev/null 2>&1
        rc=$?
        set -e
        if [[ "$rc" != "$expected" ]]; then
            set_mismatches=$((set_mismatches + 1))
            mismatches=$((mismatches + 1))
            FAILED+=("$(basename "$cnf") [$set_name]: got $rc, expected $expected")
        fi
    done

    end=$(date +%s.%N)
    elapsed=$(awk "BEGIN{printf \"%.2f\", $end - $start}")
    ok=$((set_total - set_mismatches))
    if [[ $set_total -eq 0 ]]; then
        avg="—"
    else
        avg=$(awk "BEGIN{printf \"%.1f\", ($end - $start) * 1000 / $set_total}")
    fi
    printf '%-12s  %5d/%-5d ok  %8ss total  %7s ms/inst\n' \
        "$set_name" "$ok" "$set_total" "$elapsed" "$avg"
done

printf '\n'
if [[ $mismatches -eq 0 ]]; then
    printf 'all %d instances correct\n' "$total"
    exit 0
else
    printf '%d/%d mismatches:\n' "$mismatches" "$total"
    for f in "${FAILED[@]:0:20}"; do
        printf '  %s\n' "$f"
    done
    if [[ ${#FAILED[@]} -gt 20 ]]; then
        printf '  ... and %d more\n' "$((${#FAILED[@]} - 20))"
    fi
    exit 1
fi
