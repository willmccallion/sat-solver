#!/usr/bin/env bash
# bench/build-solvers.sh — clone and build reference CDCL solvers into
# bench/solvers/{cadical,kissat}/ so bench/compare.py can find them.
#
# MiniSat is not built from source here — the upstream is unmaintained and
# has build issues with modern compilers. Install it system-wide instead:
#
#     apt install minisat2     (Debian / Ubuntu)
#     brew install minisat     (macOS)
#     pacman -S minisat        (Arch)
#
# Usage: bench/build-solvers.sh [cadical|kissat]
#   With no arguments, builds both. With one argument, builds only that one.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOLVERS_DIR="$SCRIPT_DIR/solvers"
mkdir -p "$SOLVERS_DIR"

build_cadical() {
    local dir="$SOLVERS_DIR/cadical"
    printf '==> cadical\n'
    if [[ ! -d "$dir" ]]; then
        git clone --depth=1 https://github.com/arminbiere/cadical.git "$dir"
    else
        printf '    (already cloned at %s)\n' "$dir"
    fi
    (
        cd "$dir"
        if [[ ! -f build/makefile ]]; then
            ./configure
        fi
        make -j
    )
    if [[ -x "$dir/build/cadical" ]]; then
        printf '    ok: %s\n' "$dir/build/cadical"
    else
        printf '    FAIL: cadical binary not found at %s/build/cadical\n' "$dir" >&2
        return 1
    fi
}

build_kissat() {
    local dir="$SOLVERS_DIR/kissat"
    printf '==> kissat\n'
    if [[ ! -d "$dir" ]]; then
        git clone --depth=1 https://github.com/arminbiere/kissat.git "$dir"
    else
        printf '    (already cloned at %s)\n' "$dir"
    fi
    (
        cd "$dir"
        if [[ ! -f build/makefile ]]; then
            ./configure
        fi
        make -j
    )
    if [[ -x "$dir/build/kissat" ]]; then
        printf '    ok: %s\n' "$dir/build/kissat"
    else
        printf '    FAIL: kissat binary not found at %s/build/kissat\n' "$dir" >&2
        return 1
    fi
}

check_minisat() {
    printf '==> minisat\n'
    if command -v minisat >/dev/null 2>&1; then
        printf '    ok: %s\n' "$(command -v minisat)"
    elif command -v minisat2 >/dev/null 2>&1; then
        printf '    ok: %s\n' "$(command -v minisat2)"
    else
        printf '    not installed. install with:\n'
        printf '      apt install minisat2     (Debian / Ubuntu)\n'
        printf '      brew install minisat     (macOS)\n'
        printf '      pacman -S minisat        (Arch)\n'
    fi
}

case "${1:-all}" in
    cadical)  build_cadical ;;
    kissat)   build_kissat ;;
    minisat)  check_minisat ;;
    all|'')
        build_cadical
        build_kissat
        check_minisat
        ;;
    *)
        printf 'usage: %s [cadical|kissat|minisat]\n' "$0" >&2
        exit 2
        ;;
esac

printf '\ndone. run `bench/compare.py --dry-run` to verify discovery.\n'
