#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research.
# Install official upstream Verus and solvers for the independent proof gate.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
source scripts/verus/pins.env
solver="${1:?usage: setup-upstream-verus.sh z3|cvc5}"
case "$solver" in
  z3|cvc5) ;;
  *) echo "::error::unsupported upstream solver: $solver" >&2; exit 2 ;;
esac
dest="${VERUS_UPSTREAM_CI_DIR:-$HOME/.verus-ci/upstream}"
mkdir -p "$dest"

setenv() {
  echo "$1=$2"
  [[ -z "${GITHUB_ENV:-}" ]] || echo "$1=$2" >> "$GITHUB_ENV"
  export "$1=$2"
}
out() {
  echo "$1=$2"
  [[ -z "${GITHUB_OUTPUT:-}" ]] || echo "$1=$2" >> "$GITHUB_OUTPUT"
}
download() {
  echo "Downloading $1" >&2
  curl -fsSL -o "$2" "$1"
  echo "$3  $2" | sha256sum -c -
}

download "https://github.com/verus-lang/verus/releases/download/${UPSTREAM_VERUS_TAG}/verus-${UPSTREAM_VERUS_TAG#release/}-x86-linux.zip" \
  "$dest/verus.zip" "$UPSTREAM_VERUS_SHA256"
# A fresh directory prevents stale files from another release being reused.
install_dir="$(mktemp -d "$dest/install.XXXXXX")"
unzip -q "$dest/verus.zip" -d "$install_dir"
bin="$install_dir/verus-x86-linux"
metadata="$(python3 - "$bin/version.json" "$bin/vstd/Cargo.toml" <<'PY'
import json, sys, tomllib
with open(sys.argv[1]) as f:
    v = json.load(f)["verus"]
with open(sys.argv[2], "rb") as f:
    shipped = tomllib.load(f)["package"]["version"]
with open("Cargo.lock", "rb") as f:
    pinned = next(p["version"] for p in tomllib.load(f)["package"] if p["name"] == "vstd")
if shipped != pinned:
    sys.exit(f"upstream vstd {shipped} differs from Cargo.lock {pinned}; update the upstream release and crate pins together")
print(v["commit"], v["version"], v["toolchain"], shipped)
PY
)"
read -r commit version toolchain vstd_version <<< "$metadata"
rustup toolchain install "$toolchain" --profile minimal --component rustc-dev --component llvm-tools
setenv RUSTUP_TOOLCHAIN "$toolchain"
# Use the official release's Z3, including when cargo-verus builds dependencies.
setenv VERUS_Z3_PATH "$bin/z3"
if [[ "$solver" == cvc5 ]]; then
  download "https://github.com/cvc5/cvc5/releases/download/${UPSTREAM_CVC5_TAG}/cvc5-Linux-static.zip" \
    "$dest/cvc5.zip" "$UPSTREAM_CVC5_SHA256"
  unzip -q "$dest/cvc5.zip" -d "$install_dir"
  setenv VERUS_CVC5_PATH "$install_dir/cvc5-Linux-static/bin/cvc5"
fi
[[ -z "${GITHUB_PATH:-}" ]] || echo "$bin" >> "$GITHUB_PATH"
out verus_tag "$UPSTREAM_VERUS_TAG"
out verus_commit "$commit"
out verus_version "$version"
out rust_toolchain "$toolchain"
out vstd_version "$vstd_version"
echo "Upstream Verus ${version} (${commit}), solver ${solver}"
