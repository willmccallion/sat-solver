#!/usr/bin/env bash
# Fetches a subset of SAT Competition 2025 main-track benchmarks into
# bench/instances/satcomp2025/. The 2025 competition hosts each of its
# 400 instances individually (xz-compressed) at benchmark-database.de;
# we download a URI list, take the first N, and decompress in place.
#
# Usage:
#   bench/fetch_satcomp.sh            # default: 20 instances (~100 MB)
#   bench/fetch_satcomp.sh 40         # first 40 instances
#   bench/fetch_satcomp.sh all        # full 400 (~several GB decompressed)
#
# Run again with a larger N to top up — existing .cnf files are kept.

set -euo pipefail

N="${1:-20}"
URI_URL="https://benchmark-database.de/getinstances?track=main_2025&context=cnf"
OUT_DIR="bench/instances/satcomp2025"

if [[ ! -d .git ]]; then
  echo "fetch_satcomp.sh: run from the repo root (no .git here)." >&2
  exit 1
fi

mkdir -p "$OUT_DIR"
cd "$OUT_DIR"

echo "→ fetching URI list"
curl -sfL "$URI_URL" -o track_main_2025.uri

total="$(wc -l < track_main_2025.uri)"
if [[ "$N" == "all" ]]; then
  take="$total"
else
  take="$N"
fi
echo "→ will download $take / $total instances"

# Slice URIs, fetch with content-disposition so filenames come from
# the server (instance IDs + descriptive suffix). -nc skips files we
# already have; failures on individual instances do not abort the run.
head -n "$take" track_main_2025.uri > .slice.uri
wget -q --show-progress --content-disposition -nc -i .slice.uri || true
rm -f .slice.uri

echo "→ decompressing .xz → .cnf (keeping .xz so re-run is a no-op)"
shopt -s nullglob
for f in *.cnf.xz; do
  plain="${f%.xz}"
  if [[ ! -s "$plain" ]]; then
    xz -dk -- "$f"
  fi
done

rm -f *.cnf.xz  # the bench runner only looks at .cnf; save disk

count="$(find . -maxdepth 1 -name '*.cnf' | wc -l)"
echo "✓ $count .cnf files ready in $OUT_DIR"
