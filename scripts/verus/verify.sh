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
  sql::types::value
  sql::parser::ast
  sql::parser::float_trust
  sql::parser::lexer
  sql::parser::printer
  sql::parser::unicode_trust
  sql::parser::verified
  sql::parser::verified_expression
  sql::parser::verified_lexer
  sql::parser::verified_function_list
  sql::parser::verified_integer
  sql::parser::verified_lists
  sql::parser::verified_production
  sql::parser::verified_roundtrip
  sql::parser::verified_simple_statement
  sql::parser::verified_statements
  sql::parser::verified_stmt
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

# SMT query capture: by default every run logs the full Verus diagnostics
# (--log-all: .smt2 queries, .smt_transcript solver exchanges, AIR, VIR,
# triggers, call graphs — NOT the gigantic Z3 trace profiles) into a fresh
# directory. The `verus-smt-log-dir:` stderr marker is how the capture layer
# (.claude/hooks/smt_capture.py on the agent side, the CI workflow on the CI
# side) finds the directory to key, compress, and upload to the dashboard.
# Logging costs little (~1s on a full run); the artifacts are zstd'd in place
# after the run (~25x smaller, ~20 MB) so the directory is inert and cheap if
# nothing collects it. Opt out: VERUS_SMT_LOG_DISABLE=1.
# Override the parent dir with VERUS_SMT_LOG_ROOT (CI does).
smt_log_args=()
if [[ "${VERUS_SMT_LOG_DISABLE:-0}" != "1" ]]; then
  smt_root="${VERUS_SMT_LOG_ROOT:-$HOME/.verus-trace/smt/pending}"
  if mkdir -p "$smt_root" 2>/dev/null       && smt_dir="$(mktemp -d "$smt_root/$(date -u +%Y%m%dT%H%M%SZ).XXXXXX" 2>/dev/null)"; then
    smt_log_args=(--log-all --log-dir "$smt_dir")
    echo "verus-smt-log-dir: $smt_dir" >&2
  else
    echo "verus: smt log dir creation failed; running without --log-all" >&2
  fi
fi

# `--lib` scopes to the library target; the four binaries carry no verified
# modules and would otherwise fail `--verify-module`. Pass-through args ("$@",
# e.g. --output-json) go AFTER `--` so they reach Verus, not `cargo check`
# (which rejects unknown flags). Caller args come last so they can override
# the defaults (e.g. a different --log-dir).
rc=0
cargo verus focus --lib -- "${module_args[@]}" "${smt_log_args[@]}" "$@" || rc=$?
# Compress the artifacts in place (x -> x.zst); no zstd on PATH leaves them raw.
if [[ -n "${smt_dir:-}" ]] && command -v zstd >/dev/null 2>&1; then
  zstd -q --rm -T0 -r "$smt_dir" 2>/dev/null || true
fi
exit "$rc"
