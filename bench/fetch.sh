#!/usr/bin/env bash
# bench/fetch.sh — reproducibly download SATLIB uniform-random 3-SAT benchmark
# sets into bench/instances/. Idempotent: cached archives are reused.
#
# Usage: bench/fetch.sh [set_name ...]
#
# With no arguments, fetches every set listed in SETS below. With arguments,
# only the named sets are fetched.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INSTANCES_DIR="$SCRIPT_DIR/instances"
CACHE_DIR="$SCRIPT_DIR/.cache"
SATLIB_BASE="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT"

# Each row: set_name  expected_instance_count  expected_verdict  subpath
SETS=(
    "uf20-91     1000  SAT    RND3SAT/uf20-91.tar.gz"
    "uf50-218    1000  SAT    RND3SAT/uf50-218.tar.gz"
    "uf100-430   1000  SAT    RND3SAT/uf100-430.tar.gz"
    "uuf50-218   1000  UNSAT  RND3SAT/uuf50-218.tar.gz"
    "uuf100-430  1000  UNSAT  RND3SAT/uuf100-430.tar.gz"
    "uf150-645    100  SAT    RND3SAT/uf150-645.tar.gz"
    "uuf150-645   100  UNSAT  RND3SAT/uuf150-645.tar.gz"
    "uf200-860    100  SAT    RND3SAT/uf200-860.tar.gz"
    "uuf200-860    99  UNSAT  RND3SAT/uuf200-860.tar.gz"
    "uf250-1065   100  SAT    RND3SAT/uf250-1065.tar.gz"
    "uuf250-1065  100  UNSAT  RND3SAT/uuf250-1065.tar.gz"
    "dimacs-aim      72  MIXED  DIMACS/AIM/aim.tar.gz"
    "dimacs-jnh      50  MIXED  DIMACS/JNH/jnh.tar.gz"
    "dimacs-dubois   12  UNSAT  DIMACS/DUBOIS/dubois.tar.gz"
    "dimacs-pret      8  UNSAT  DIMACS/PRET/pret.tar.gz"
    "dimacs-ssa       8  MIXED  DIMACS/SSA/ssa.tar.gz"
    "dimacs-bf        4  UNSAT  DIMACS/BF/bf.tar.gz"
    "dimacs-ii       41  SAT    DIMACS/II/inductive-inference.tar.gz"
    "dimacs-hanoi     2  SAT    DIMACS/HANOI/hanoi.tar.gz"
    "dimacs-parity   30  SAT    DIMACS/PARITY/parity.tar.gz"
)

filter_sets() {
    if [[ $# -eq 0 ]]; then
        printf '%s\n' "${SETS[@]}"
        return
    fi
    for row in "${SETS[@]}"; do
        for arg in "$@"; do
            if [[ "$row" == "$arg "* ]]; then
                printf '%s\n' "$row"
            fi
        done
    done
}

mkdir -p "$INSTANCES_DIR" "$CACHE_DIR"

exit_code=0
while IFS= read -r row; do
    read -r name expected_count expected_verdict subpath <<< "$row"
    archive="$CACHE_DIR/$name.tar.gz"
    target="$INSTANCES_DIR/$name"
    extract_tmp="$CACHE_DIR/$name.extract"

    if [[ ! -f "$archive" ]]; then
        printf 'fetching %s from SATLIB...\n' "$name"
        curl -fsSL --retry 3 "$SATLIB_BASE/$subpath" -o "$archive.tmp"
        mv "$archive.tmp" "$archive"
    else
        printf 'cached   %s\n' "$name"
    fi

    rm -rf "$extract_tmp" "$target"
    mkdir -p "$extract_tmp" "$target"
    tar -xzf "$archive" -C "$extract_tmp"

    # SATLIB tarballs embed their path structure differently across sets, so
    # flatten: copy every .cnf found anywhere under extract_tmp into target/.
    find "$extract_tmp" -type f -name '*.cnf' -exec mv -t "$target" {} +
    rm -rf "$extract_tmp"

    # SATLIB dubois100.cnf is genuinely malformed: declares 800 clauses
    # but only has 598 zero terminators. A strict DIMACS parser (correctly)
    # reads the file as a handful of giant clauses containing both a
    # literal and its negation (tautologies), which are trivially SAT.
    # Drop it to avoid the bogus verdict.
    if [[ "$name" == "dimacs-dubois" ]]; then
        rm -f "$target/dubois100.cnf"
    fi

    count=$(find "$target" -maxdepth 1 -type f -name '*.cnf' | wc -l)
    if [[ "$count" != "$expected_count" ]]; then
        printf '  WARN: %s has %s instances, expected %s\n' "$name" "$count" "$expected_count"
        exit_code=1
    else
        printf '  %-12s %4s instances (%s)\n' "$name" "$count" "$expected_verdict"
    fi
done < <(filter_sets "$@")

printf '\nbenchmarks ready at %s\n' "$INSTANCES_DIR"
exit "$exit_code"
