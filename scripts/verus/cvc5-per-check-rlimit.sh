#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research.
#
# The pinned upstream Verus release launches cvc5 with `--rlimit 1666666`.
# cvc5 applies that option cumulatively to the entire long-lived process, so
# later verification conditions immediately return resourceout once earlier
# conditions consume the budget. Translate it to cvc5's per-check limit and
# leave every other upstream-selected argument unchanged.
set -euo pipefail

real_cvc5="${VERUS_CVC5_REAL_PATH:?VERUS_CVC5_REAL_PATH must name the pinned cvc5 binary}"
rewritten=()
while (( $# > 0 )); do
  case "$1" in
    --rlimit)
      if (( $# < 2 )); then
        echo "error: upstream Verus passed --rlimit without a value" >&2
        exit 2
      fi
      rewritten+=("--rlimit-per=$2")
      shift 2
      ;;
    --rlimit=*)
      rewritten+=("--rlimit-per=${1#--rlimit=}")
      shift
      ;;
    *)
      rewritten+=("$1")
      shift
      ;;
  esac
done

exec "$real_cvc5" "${rewritten[@]}"
