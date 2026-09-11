#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research.
# Run after best-effort telemetry collection; missing results must fail closed.
set -euo pipefail
if [[ "${SETUP_OUTCOME:-}" != success ]]; then
  echo "::error::Verus setup failed or was skipped (${SETUP_OUTCOME:-missing})."
  exit 1
fi
if [[ "${VERIFY_OUTCOME:-}" != success || "${VERUS_RAN:-}" != true || "${VERUS_RC:-}" != 0 ]]; then
  echo "::error::Verus verification did not succeed (step=${VERIFY_OUTCOME:-missing}, ran=${VERUS_RAN:-missing}, exit=${VERUS_RC:-missing})."
  exit 1
fi
