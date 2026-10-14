#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# Dynamic coverage of verified code: which verified exec functions actually
# run, with their preconditions holding, on toyDB's own unit and integration
# tests.
#
#   1. `cargo verus build --lib --bins -- --reach DIR --dyncov --no-verify`
#      compiles the library and binaries through Verus with contracts lowered
#      to run-time checks (see source/docs/dyncov.md in the verus fork) and
#      writes the static reachability reports.
#   2. `cargo verus build --tests -- --reach DIR --dyncov --no-verify` builds
#      the test binaries the same way, with their own reports.
#   3. The library's unit-test binary runs with VERUS_DYNCOV_OUT set; it
#      writes one profile per process into `$OUT/profiles`.
#   4. `verus-reach --dynamic` joins the profiles with the static reports:
#      `summary.txt`, `diff.txt`, `spec.txt`, `coverage.lcov`, and
#      `verus-reach --html` renders `html/index.html` (all workloads) and
#      `html-integration/index.html` (the cluster tests alone).
#
#   3b. The integration tests (tests/tests.rs) run against clusters of the
#      instrumented `toydb` binary (TOYDB_BIN); the servers' profiles join
#      the pool.
#
# Usage: scripts/verus/dyncov.sh [--out DIR] [--fail-under PCT]
#
# Requires `cargo-verus`, `verus` and `verus-reach` on PATH, built from a
# BasisResearch/verus commit with `--dyncov`. The instrumentation lives in
# that commit's `verus!` macro and vstd (`vstd::dyncov`), so the build
# replaces the crates.io vstd pin with the fork's through cargo `--config`
# patches, leaving Cargo.toml alone (Cargo.lock is restored afterwards):
#   VERUS_SRC=<checkout>   path patches into that checkout (default: the
#                          checkout the `verus` on PATH was built in);
#   VERUS_REV=<sha>        otherwise, git patches at that fork commit.

set -euo pipefail

out=".verus-out/dyncov"
fail_under=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out) out="$2"; shift 2 ;;
    --fail-under) fail_under="$2"; shift 2 ;;
    -h|--help) sed -n '/^# Usage:/,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "dyncov.sh: unknown argument: $1" >&2; exit 2 ;;
  esac
done

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

for tool in cargo-verus verus verus-reach; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: $tool not found on PATH (see the header of this script)." >&2
    exit 127
  fi
done

# The fork's vstd and `verus!` macro in place of the crates.io pin, for this
# build only. (vstd re-exports the dyncov run-time, so nothing else is
# needed.)
verus_src="${VERUS_SRC:-}"
if [[ -z "$verus_src" && -z "${VERUS_REV:-}" ]]; then
  # vargo installs `verus` at <checkout>/source/target-verus/<profile>/verus
  candidate="$(cd "$(dirname "$(command -v verus)")/../../.." 2>/dev/null && pwd || true)"
  if [[ -n "$candidate" && -f "$candidate/source/vstd/Cargo.toml" ]]; then
    verus_src="$candidate"
  fi
fi
patch_config=()
for crate in vstd:vstd verus_builtin:builtin verus_builtin_macros:builtin_macros \
             verus_state_machines_macros:state_machines_macros; do
  name="${crate%%:*}"; dir="${crate##*:}"
  if [[ -n "$verus_src" ]]; then
    patch_config+=(--config "patch.crates-io.${name}.path=\"${verus_src}/source/${dir}\"")
  elif [[ -n "${VERUS_REV:-}" ]]; then
    patch_config+=(--config "patch.crates-io.${name}.git=\"https://github.com/BasisResearch/verus\"")
    patch_config+=(--config "patch.crates-io.${name}.rev=\"${VERUS_REV}\"")
  else
    echo "error: set VERUS_SRC to a BasisResearch/verus checkout or VERUS_REV to a commit (see the header of this script)." >&2
    exit 2
  fi
done
echo "verus: vstd and verus! from ${verus_src:-BasisResearch/verus@$VERUS_REV}" >&2
# The patches re-resolve the lock file; put it back when done
lock_backup="$(mktemp)"
cp Cargo.lock "$lock_backup"
trap 'cp "$lock_backup" Cargo.lock; rm -f "$lock_backup"' EXIT

# Browsable pages (verus-reach --html): the files with verified code and
# their sources, where a verified exec function counts as reachable only
# when it is true verified reachable on the workload.
render_html() {
  local profiles="$1" dir="$2" title="$3"; shift 3
  rm -rf "$dir"
  verus-reach --dynamic "$profiles" --html "$dir" --src . --title "$title" "$@"
}

target_dir="target/dyncov"
reach_dir="$out/reach"
rm -rf "$out"
mkdir -p "$reach_dir" "$out/profiles" "$out/llvm"
# Every instrumented process (the tests, but also anything cargo runs during
# the build) writes its LLVM profile here rather than default_*.profraw in cwd
export LLVM_PROFILE_FILE="$repo_root/$out/llvm/%p-%m.profraw"

# Cargo's freshness check ignores the args after `--`: a cached build would
# replay without running Verus, and no report would be written. Drop toydb's
# own artifacts; dependencies stay cached.
cargo clean --quiet --package toydb --target-dir "$target_dir"
echo "verus: building instrumented binaries into $target_dir" >&2
cargo verus build --fwd-verus-args-to roots "${patch_config[@]}" --target-dir "$target_dir" --lib --bins \
  -- --reach "$repo_root/$reach_dir" --dyncov --no-verify
# The test crates get reports too (`<crate>.test-<root stem>.json`), so that
# the static graph is rooted at the tests as well as the binaries: the
# workload below is the unit tests, and D ⊆ S should hold for it.
cargo verus build --fwd-verus-args-to roots "${patch_config[@]}" --target-dir "$target_dir" --tests \
  -- --reach "$repo_root/$reach_dir" --dyncov --no-verify

# The library's unit-test binary: the one test executable named after the
# package that lists tests
lib_tests=""
for exe in "$target_dir"/debug/deps/toydb-*; do
  [[ -x "$exe" && ! "$exe" == *.d ]] || continue
  # (no grep -q: with pipefail an early exit would fail the pipeline)
  if "$exe" --list 2>/dev/null | grep ': test$' > /dev/null; then
    lib_tests="$exe"
  fi
done
if [[ -z "$lib_tests" ]]; then
  echo "error: no unit-test binary found in $target_dir/debug/deps" >&2
  exit 1
fi

echo "verus: running $lib_tests" >&2
VERUS_DYNCOV_OUT="$repo_root/$out/profiles" "$lib_tests"

# The integration tests (tests/tests.rs): goldenscripts against real clusters
# of the instrumented `toydb` binary (TOYDB_BIN, see tests/testcluster.rs).
# The servers inherit VERUS_DYNCOV_OUT and flush their profiles every two
# seconds; they are killed at the end of each script.
integration=""
for exe in "$target_dir"/debug/deps/tests-*; do
  [[ -x "$exe" && ! "$exe" == *.d ]] || continue
  integration="$exe"
done
if [[ -n "$integration" ]]; then
  echo "verus: running $integration against $target_dir/debug/toydb" >&2
  mkdir -p "$out/profiles-integration"
  TOYDB_BIN="$repo_root/$target_dir/debug/toydb" \
  VERUS_DYNCOV_OUT="$repo_root/$out/profiles-integration" "$integration" --test-threads=1
  cp "$out"/profiles-integration/*.json "$out/profiles/"
fi

verus-reach --dynamic "$out/profiles" "$reach_dir" | tee "$out/summary.txt"
if [[ -d "$out/profiles-integration" ]]; then
  # The integration workload on its own, rooted at the binaries only
  verus-reach --dynamic "$out/profiles-integration" "$reach_dir"/*.bin.json "$reach_dir"/toydb.lib.json \
    > "$out/summary-integration.txt"
  verus-reach --dynamic "$out/profiles-integration" --lcov --only-verified-exec \
    "$reach_dir"/*.bin.json "$reach_dir"/toydb.lib.json > "$out/coverage-integration.lcov"
  render_html "$out/profiles-integration" "$out/html-integration" \
    "toyDB: dynamic verified coverage (integration tests, real clusters)" \
    "$reach_dir"/*.bin.json "$reach_dir"/toydb.lib.json
fi
verus-reach --dynamic "$out/profiles" --diff "$reach_dir" > "$out/diff.txt"
verus-reach --dynamic "$out/profiles" --spec-report "$reach_dir" > "$out/spec.txt"
verus-reach --dynamic "$out/profiles" --lcov --only-verified-exec "$reach_dir" > "$out/coverage.lcov"
echo "verus-reach: wrote $out/{summary,diff,spec}.txt and $out/coverage.lcov" >&2

render_html "$out/profiles" "$out/html" "toyDB: dynamic verified coverage (unit + integration tests)" "$reach_dir"

if [[ -n "$fail_under" ]]; then
  verus-reach --dynamic "$out/profiles" --fail-under "$fail_under" "$reach_dir" > /dev/null
fi
