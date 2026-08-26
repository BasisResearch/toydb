#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code `SessionStart` hook: the fail-closed MCP gate with drift warning.
#
# Probes the Verus MCP server's `version` tool (HTTP dev-default or stdio pinned;
# see mcp_probe.py). Policy:
#
#   * Server unreachable / unhealthy  -> BLOCK (fail-closed). Emit a "block"
#     decision with a helpful message: start the dev HTTP server, or switch to
#     the pinned .mcp.prod.json.
#   * Server healthy but git_dirty / mcp_version has `.dirty` or `+unknown`
#     -> ALLOW, but WARN the user that this is a dev / non-release build, that
#     the session is tagged with that mcp_version, and that it will be excluded
#     from release comparisons on the dashboard. Do NOT block.
#   * Server healthy and clean -> ALLOW silently.
#
# An escape hatch (VERUS_GATE_DISABLE=1) exists only for local development of
# the telemetry itself; it is off by default so a fresh clone is gated.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

BLOCK_MESSAGE = (
    "Verus MCP server is required to work on toyDB, but the `version` probe "
    "failed, so this session is blocked (fail-closed gate).\n"
    "Reason: %s\n\n"
    "The team default (.mcp.json) expects the dev hot-reload HTTP server. Start "
    "it with:\n"
    "    cd ../verus-tools-mcp && ./scripts/dev-http.sh\n"
    "(it serves http://127.0.0.1:8765/mcp under `cargo watch`).\n\n"
    "If you do not hack on the server, switch to the pinned stdio launcher: make "
    ".mcp.prod.json the active config, e.g. `ln -sf .mcp.prod.json .mcp.json` "
    "(it self-installs a pinned verus-tools-mcp build). See "
    ".claude/hooks/README.md."
)

WARN_MESSAGE = (
    "[verus-gate] WARNING: the Verus MCP server is a DEV / NON-RELEASE build "
    "(mcp_version=%s). This session is tagged with that version and will be "
    "EXCLUDED from release comparisons on the /verus dashboard. This is fine for "
    "development; use a pinned release build (.mcp.prod.json) for comparable "
    "numbers."
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


def _emit_warn_context(mcp_version):
    """Surface the dev-build warning to the user without blocking."""
    msg = WARN_MESSAGE % (mcp_version or "unknown")
    sys.stderr.write(msg + "\n")
    payload = {
        "hookSpecificOutput": {
            "hookEventName": "SessionStart",
            "additionalContext": msg,
        }
    }
    sys.stdout.write(json.dumps(payload))
    sys.stdout.write("\n")


def main():
    # Self-provision the branch-discipline git hooks (core.hooksPath ->
    # .githooks) so the agent-agnostic backstop is active in this clone.
    # Fail-soft: never blocks the session.
    try:
        import branch_guard

        branch_guard.ensure_hooks_path()
    except Exception:
        pass

    if str(os.environ.get("VERUS_GATE_DISABLE", "")).lower() in ("1", "true", "yes"):
        sys.stderr.write("[verus-gate] gate disabled via VERUS_GATE_DISABLE\n")
        return 0

    try:
        from verus_trace import mcp_probe

        result = mcp_probe.probe_version()
    except Exception as exc:
        _emit_block("probe raised %s" % exc)
        return 2

    # Fail-closed: unreachable / unhealthy server blocks the session.
    if not result.healthy:
        _emit_block(result.error or "server not healthy")
        return 2

    # Healthy. Warn (but allow) on a dev / non-release build.
    try:
        dirty = mcp_probe.is_dirty_version(result.version)
    except Exception:
        dirty = False

    if dirty:
        _emit_warn_context(result.version.get("mcp_version"))
        return 0

    sys.stderr.write(
        "[verus-gate] Verus MCP healthy (%s): %s\n"
        % (result.transport, json.dumps(result.version))
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
