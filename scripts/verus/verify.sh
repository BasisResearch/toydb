#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
#
# Progressive Verus verification for toyDB.
#
# Runs `cargo verus focus` over the library target, verifying only the modules
# listed in VERIFY_MODULES below. Verus is external-by-default: code outside a
# `verus!` block (i.e. almost all of toyDB) is ignored, so this stays green as
# the codebase evolves and only fails when an opted-in module stops verifying.
#
# To verify a newly annotated module, add its path here (e.g. `encoding::bincode`).
# This list is the source of truth for "what toyDB has verified so far"; the
# verus-gate CI job runs exactly this script.
#
# Requires `cargo-verus` on PATH (shipped in the Verus release zip alongside
# `verus`). Locally: `export PATH="$HOME/.local/verus/verus-<arch>:$PATH"`.

set -euo pipefail

# Modules opted in to verification, as `--verify-module` accepts them
# (crate-relative, `::`-separated). Grows one line at a time.
VERIFY_MODULES=(
  encoding::keycode
  raft::log
  sql::types::value
)

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if ! command -v cargo-verus >/dev/null 2>&1; then
  echo "error: cargo-verus not found on PATH." >&2
  echo "       Install the pinned Verus release and add its dir to PATH." >&2
  exit 127
fi

module_args=()
for m in "${VERIFY_MODULES[@]}"; do
  module_args+=(--verify-module "$m")
done

# To stderr: stdout carries the --output-json payload that the telemetry
# pipeline parses, so it must stay pure JSON.
echo "verus: verifying ${#VERIFY_MODULES[@]} module(s): ${VERIFY_MODULES[*]}" >&2
# `--lib` scopes to the library target; the four binaries carry no verified
# modules and would otherwise fail `--verify-module`. Pass-through args ("$@",
# e.g. --output-json) go AFTER `--` so they reach Verus, not `cargo check`
# (which rejects unknown flags).
exec cargo verus focus --lib -- "${module_args[@]}" "$@"
