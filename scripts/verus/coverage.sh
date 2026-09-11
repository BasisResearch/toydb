#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# Coverage of verified code: how much of toyDB's verified exec code is
# statically reachable from a real toyDB executable.
#
#   1. `cargo verus focus --lib --bins -- --reach DIR --no-verify` compiles the
#      library and the four binaries through Verus and writes one reachability
#      report per crate (`<crate>.<lib|bin>.json`). `--no-verify` skips the SMT
#      solver: reachability only needs the typed call graph, which Verus has
#      before verification starts. Whether the code *verifies* is the
#      verus-gate job's business.
#   2. `verus-reach` (tools/verus-reach in the BasisResearch/verus fork) joins
#      the reports into one graph rooted at the binaries' `main` functions and
#      prints the summary (`summary.txt`), an LCOV trace of the verified exec
#      functions (`coverage.lcov`), and, when `genhtml` from the `lcov` package
#      is on PATH, a browsable HTML report (`html/index.html`).
#
# The gate itself is `verus-reach --fail-under N`, run by --fail-under here or
# by the verus-coverage workflow (see COVERAGE_MIN_PERCENT there).
#
# Roots: by default every binary's `main`, i.e. "used by toydb, toysql, toydump
# or workload". To measure against the library's public API instead, feed
# verus-reach only the lib report (`verus-reach $OUT/reach/toydb.lib.json`).
#
# Usage: scripts/verus/coverage.sh [--out DIR] [--fail-under PCT]
#   --out DIR         output directory (default .verus-out/coverage)
#   --fail-under PCT  exit 1 if fewer than PCT% of verified exec functions are
#                     reachable (verus-reach's own check)
#
# Requires `cargo-verus` and `verus-reach` on PATH, built from the same
# BasisResearch/verus commit (the upstream Verus releases have no `--reach`);
# `scripts/verus/setup-verus.sh resolve && scripts/verus/setup-verus.sh
# install --reach` installs exactly what CI uses.

set -euo pipefail

out=".verus-out/coverage"
fail_under=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out) out="$2"; shift 2 ;;
    --fail-under) fail_under="$2"; shift 2 ;;
    -h|--help) sed -n '/^# Usage:/,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "coverage.sh: unknown argument: $1" >&2; exit 2 ;;
  esac
done

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

for tool in cargo-verus verus-reach; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: $tool not found on PATH (see the header of this script)." >&2
    exit 127
  fi
done

reach_dir="$out/reach"
# Stale reports from renamed or removed crates are never overwritten.
rm -rf "$reach_dir"
mkdir -p "$reach_dir"

# Cargo options (--target-dir, --lib, --bins) must precede `--`; everything
# after `--` goes to Verus. Cargo-relevant options like --manifest-path or
# --features would have to go before --lib/--bins (cargo-verus rejects the
# other order).
# Cargo's freshness check is content-based under cargo-verus and ignores the
# args after `--`: after a previous build of the same sources it would replay
# the cached result, Verus would never run, and $reach_dir would stay empty.
# Drop toydb's own artifacts from the directory `cargo verus focus` builds
# into (`<target dir>/verus-partial`); dependencies stay cached.
target_dir="$(cargo metadata --no-deps --format-version 1 \
  | python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')"
cargo clean --quiet --package toydb --target-dir "$target_dir/verus-partial"
echo "verus: writing reachability reports to $reach_dir" >&2
cargo verus focus --lib --bins -- --reach "$reach_dir" --no-verify
if [[ ! -f "$reach_dir/toydb.lib.json" ]]; then
  echo "error: no reachability report for the library in $reach_dir" >&2
  echo "       (cargo replayed a cached build, or verus lacks --reach)" >&2
  exit 1
fi

verus-reach "$reach_dir" | tee "$out/summary.txt"
verus-reach --lcov --only-verified-exec "$reach_dir" > "$out/coverage.lcov"
echo "verus-reach: wrote $out/summary.txt and $out/coverage.lcov" >&2

if command -v genhtml >/dev/null 2>&1; then
  rm -rf "$out/html"
  # Paths in the trace are repo-relative, so genhtml runs from the repo root.
  genhtml --quiet --output-directory "$out/html" \
    --title "toyDB: verified exec code reachable from the binaries" \
    "$out/coverage.lcov"
  echo "genhtml: wrote $out/html/index.html" >&2
else
  echo "genhtml not on PATH (apt/pacman package lcov); skipping the HTML report" >&2
fi

if [[ -n "$fail_under" ]]; then
  verus-reach --fail-under "$fail_under" "$reach_dir" > /dev/null
fi
