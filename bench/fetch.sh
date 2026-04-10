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
SATLIB_BASE="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT"

# Each row: set_name  expected_instance_count  expected_verdict
SETS=(
    "uf20-91     1000  SAT"
    "uf50-218    1000  SAT"
    "uf100-430   1000  SAT"
    "uuf50-218   1000  UNSAT"
    "uuf100-430  1000  UNSAT"
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
    read -r name expected_count expected_verdict <<< "$row"
    archive="$CACHE_DIR/$name.tar.gz"
    target="$INSTANCES_DIR/$name"
    extract_tmp="$CACHE_DIR/$name.extract"

    if [[ ! -f "$archive" ]]; then
        printf 'fetching %s from SATLIB...\n' "$name"
        curl -fsSL --retry 3 "$SATLIB_BASE/$name.tar.gz" -o "$archive.tmp"
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
