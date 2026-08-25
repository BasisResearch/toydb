#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code `SessionStart` hook: the fail-closed MCP gate.
#
# Probes the Verus MCP server's `version` tool. On ANYTHING other than a clean
# success it exits non-zero and emits a JSON block with "decision": "block" and
# a message telling the user the Verus MCP server is required. FAIL-CLOSED: a
# probe error, timeout, missing binary, or malformed response all deny the
# session — never allow-on-doubt.
#
# An escape hatch (VERUS_GATE_DISABLE=1) exists only for local development of
# the telemetry itself; it is off by default so a fresh clone is gated.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

BLOCK_MESSAGE = (
    "Verus MCP server is required to work on toyDB. The `verus-tools-mcp` "
    "server did not respond to a `version` probe, so this session is blocked "
    "(fail-closed gate). Ensure `verus-tools-mcp` is installed and on PATH; the "
    "repo's committed .mcp.json registers it. Reason: %s"
)


def _emit_block(reason):
    payload = {
        "decision": "block",
        "reason": BLOCK_MESSAGE % reason,
        "hookSpecificOutput": {
            "hookEventName": "SessionStart",
            "additionalContext": BLOCK_MESSAGE % reason,
        },
    }
    sys.stdout.write(json.dumps(payload))
    sys.stdout.write("\n")


def main():
    if str(os.environ.get("VERUS_GATE_DISABLE", "")).lower() in ("1", "true", "yes"):
        sys.stderr.write("[verus-gate] gate disabled via VERUS_GATE_DISABLE\n")
        return 0

    try:
        from verus_trace import mcp_probe

        result = mcp_probe.probe_version()
    except Exception as exc:
        _emit_block("probe raised %s" % exc)
        return 2

    if not result.healthy:
        _emit_block(result.error or "server not healthy")
        return 2

    sys.stderr.write(
        "[verus-gate] Verus MCP healthy: %s\n"
        % json.dumps(result.version)
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
