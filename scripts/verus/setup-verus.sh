#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# Install the Basis Verus toolchain that CI runs against, from the refs in
# scripts/verus/pins.env. Used by .github/actions/setup-verus; runnable by
# hand (needs gh, curl, unzip, sha256sum, rustup, python3).
#
#   setup-verus.sh resolve           resolve the Verus ref, pick the
#                                    basis-build release
#   setup-verus.sh install [--reach] download + hash-check the release, install
#                                    its Rust toolchain and pinned solvers, export
#                                    PATH / RUSTUP_TOOLCHAIN / VERUS_Z3_PATH /
#                                    VERUS_MCP_ENABLED; --reach also builds
#                                    verus-reach from the same commit
#
# `resolve` hands its results to `install` through the environment (or
# $GITHUB_ENV under Actions), so the action can put a cache step in between.
# Results go to $GITHUB_OUTPUT / $GITHUB_ENV / $GITHUB_PATH when set, and are
# always echoed. Everything lands under $VERUS_CI_DIR (default ~/.verus-ci).

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
# shellcheck source=pins.env
source scripts/verus/pins.env

dest="${VERUS_CI_DIR:-$HOME/.verus-ci}"
verus_repo="BasisResearch/verus"

out() {  # step output
  echo "$1=$2"
  [[ -n "${GITHUB_OUTPUT:-}" ]] && echo "$1=$2" >> "$GITHUB_OUTPUT"
  return 0
}
setenv() {  # environment for later steps (and this shell)
  echo "$1=$2"
  [[ -n "${GITHUB_ENV:-}" ]] && echo "$1=$2" >> "$GITHUB_ENV"
  export "$1=$2"
}
addpath() {
  echo "PATH+=$1"
  [[ -n "${GITHUB_PATH:-}" ]] && echo "$1" >> "$GITHUB_PATH"
  export PATH="$1:$PATH"
}
warn() { echo "::warning::$*"; echo "warning: $*" >&2; }

resolve() {
  local verus_sha tag latest
  echo "Resolving ${verus_repo}@${VERUS_REF}" >&2
  verus_sha="$(gh api "repos/${verus_repo}/commits/${VERUS_REF}" --jq .sha)" || {
    echo "::error::Could not resolve ${verus_repo}@${VERUS_REF}; check the ref and repository access." >&2
    return 1
  }
  tag="basis-${verus_sha:0:10}"
  # basis-build publishes one release per main commit, a few minutes after
  # the push. If that build is still in flight, fall back to the newest one.
  if ! gh release view "$tag" -R "$verus_repo" --json tagName > /dev/null 2>&1; then
    latest="$(gh api "repos/${verus_repo}/releases/latest" --jq .tag_name)"
    warn "no basis-build release for ${verus_repo}@${verus_sha:0:10} (VERUS_REF=${VERUS_REF}) yet; using ${latest}"
    tag="$latest"
  fi
  setenv VERUS_TAG "$tag"
  out verus_tag "$tag"
}

install() {
  local with_reach="${1:-}"
  local tag="${VERUS_TAG:?run 'setup-verus.sh resolve' first}"
  local base="https://github.com/${verus_repo}/releases/download/${tag}"
  local bin="$dest/verus-x86-linux"

  mkdir -p "$dest"
  ( cd "$dest" \
    && curl -fsSL -O "${base}/verus-x86-linux.zip" \
    && curl -fsSL -O "${base}/verus-x86-linux.zip.sha256" \
    && sha256sum -c verus-x86-linux.zip.sha256 \
    && rm -rf verus-x86-linux \
    && unzip -q verus-x86-linux.zip )

  # version.json: the commit and version this build is, its Rust toolchain,
  # and solver pins the MCP server installs. The fork verifies with cvc5;
  # z3 is also needed for vstd. Install both from this exact release's pins.
  local metadata commit version toolchain z3_repo z3_tag z3_asset z3_sha
  local cvc5_repo cvc5_tag cvc5_asset cvc5_sha
  metadata="$(python3 - "$bin/version.json" <<'PY'
import json, sys
v = json.load(open(sys.argv[1]))["verus"]
z3 = v["solvers"]["z3"]
cvc5 = v["solvers"]["cvc5"]
print(v["commit"], v["version"], v["toolchain"].split("-", 1)[0],
      z3["repo"], z3["tag"], z3["asset_x86_linux"], z3["sha256_x86_linux"],
      cvc5["repo"], cvc5["tag"], cvc5["asset_x86_linux"], cvc5["sha256_x86_linux"])
PY
)"
  read -r commit version toolchain z3_repo z3_tag z3_asset z3_sha \
    cvc5_repo cvc5_tag cvc5_asset cvc5_sha <<< "$metadata"

  rustup toolchain install "$toolchain" --profile minimal \
    --component rustc-dev --component llvm-tools
  setenv RUSTUP_TOOLCHAIN "$toolchain"

  curl -fsSL -o "$dest/z3" "https://github.com/${z3_repo}/releases/download/${z3_tag}/${z3_asset}"
  echo "${z3_sha}  $dest/z3" | sha256sum -c
  chmod +x "$dest/z3"
  setenv VERUS_Z3_PATH "$dest/z3"

  curl -fsSL -o "$dest/cvc5" "https://github.com/${cvc5_repo}/releases/download/${cvc5_tag}/${cvc5_asset}"
  echo "${cvc5_sha}  $dest/cvc5" | sha256sum -c
  chmod +x "$dest/cvc5"
  setenv VERUS_CVC5_PATH "$dest/cvc5"

  addpath "$bin"
  # The fork's verus/cargo-verus run only for the MCP server or with this
  # set; CI is the other pinned caller (see scripts/verus/coverage.sh).
  setenv VERUS_MCP_ENABLED 1

  local vstd_shipped vstd_pinned
  vstd_shipped="$(awk -F'"' '/^version *=/ { print $2; exit }' "$bin/vstd/Cargo.toml")"
  vstd_pinned="$(awk '/^name = "vstd"$/ { getline; print }' Cargo.lock | awk -F'"' '{ print $2 }')"
  if [[ "$vstd_shipped" != "$vstd_pinned" ]]; then
    warn "Cargo.toml pins vstd ${vstd_pinned} but Verus ${version} ships vstd ${vstd_shipped}; bump the pin in Cargo.toml"
  fi

  if [[ "$with_reach" == "--reach" ]]; then
    if [[ ! -x "$dest/reach/bin/verus-reach" ]]; then
      cargo install --locked --git "https://github.com/${verus_repo}" --rev "$commit" \
        verus-reach --root "$dest/reach"
    fi
    addpath "$dest/reach/bin"
  fi

  out verus_commit "$commit"
  out verus_version "$version"
  out rust_toolchain "$toolchain"
  out vstd_version "$vstd_shipped"
  echo "Verus ${version} (${commit:0:10}) from ${tag}; rust ${toolchain}; z3 ${z3_tag}; cvc5 ${cvc5_tag}"
}

case "${1:-}" in
  resolve) resolve ;;
  install) shift; install "${1:-}" ;;
  *) echo "usage: $0 resolve | install [--reach]" >&2; exit 2 ;;
esac
