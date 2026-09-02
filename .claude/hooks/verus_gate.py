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
#     decision with a helpful message: the server is launched per session from
#     .claude/bin/verus-mcp (stdio, the .mcp.json default), or over HTTP when
#     .mcp.dev.json is active.
#   * Server reachable but its Verus toolchain is NOT runnable (`toolchain_ok`
#     false: no verus / no cargo-verus) -> BLOCK. The tools would fail on
#     every call, so this is exactly the situation the gate exists for; the
#     server's own `toolchain_error` says how to fix it. Builds that do not
#     report the field are treated as healthy (backwards compatible).
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
    "The default (.mcp.json) launches one server per session over stdio via "
    ".claude/bin/verus-mcp, which points it at this checkout. Diagnose it with:\n"
    "    .claude/bin/verus-mcp --check\n"
    "If it says the server is not installed, provision it once (this takes a\n"
    "few minutes and is deliberately NOT done inside the gate probe):\n"
    "    .claude/bin/verus-mcp --install\n\n"
    "To hack on the server instead, make .mcp.dev.json active "
    "(`ln -sf .mcp.dev.json .mcp.json`) and run the hot-reload HTTP server:\n"
    "    cd ../verus-tools-mcp && ./scripts/dev-http.sh --workspace \"$PWD\"\n"
    "See .claude/hooks/README.md."
)

TOOLCHAIN_MESSAGE = (
    "The Verus MCP server is running, but it cannot run Verus, so every "
    "`check` / `verify` / `profile` call would fail. This session is blocked "
    "(fail-closed gate).\n"
    "Server said: %s\n\n"
    "The server inherits its environment from whatever launched it. With the "
    "default stdio config, .claude/bin/verus-mcp locates a Verus install "
    "(VERUS_PROJECT_ROOT, a sibling verus checkout, or verus on PATH) and "
    "exports it; run `.claude/bin/verus-mcp --check` to see what it found. "
    "With the HTTP dev server, restart it with the Verus release directory on "
    "PATH (or VERUS_PROJECT_ROOT set)."
)

WARN_MESSAGE = (
    "[verus-gate] WARNING: the Verus MCP server is a DEV / NON-RELEASE build "
    "(mcp_version=%s). This session is tagged with that version and will be "
    "EXCLUDED from release comparisons on the /verus dashboard. This is fine for "
    "development; use a pinned release build (.mcp.prod.json) for comparable "
    "numbers."
)


def _block(message):
    """Emit a SessionStart block both ways.

    The caller exits 2, which surfaces STDERR; the stdout JSON is honoured on
    exit 0. Writing only one of them means whichever path the harness takes,
    the user may see a blank hook failure with no reason and no remedy."""
    sys.stderr.write(message + "\n")
    payload = {
        "decision": "block",
        "reason": message,
        "hookSpecificOutput": {
            "hookEventName": "SessionStart",
            "additionalContext": message,
        },
    }
    sys.stdout.write(json.dumps(payload))
    sys.stdout.write("\n")


def _emit_block(reason):
    _block(BLOCK_MESSAGE % reason)


def _workspace_drift(workspace):
    """A warning when the server's resolved workspace (reported by the
    `version` tool of verus-tools-mcp builds that carry the field) is not this
    checkout; None when it matches or the server does not report it."""
    if not workspace:
        return None
    try:
        import subprocess

        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, timeout=5,
        )
        root = out.stdout.strip() if out.returncode == 0 else ""
    except Exception:
        root = ""
    if not root:
        return None
    if os.path.realpath(str(workspace)) == os.path.realpath(root):
        return None
    return (
        "[verus-gate] WARNING: the Verus MCP server's workspace is %s, not this "
        "checkout (%s). Its proof index covers that directory and `check` "
        "defaults to it: pass crate_name=\"%s\" to `check`/`profile`, or "
        "restart the server from this checkout (`dev-http.sh --workspace %s`)."
        % (workspace, root, root, root)
    )


def _emit_warn_context(msg):
    """Surface a warning to the user (stderr) and the agent (additionalContext)
    without blocking."""
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

    # Fail-closed: a server that cannot run Verus is useless for toyDB work.
    # `toolchain_ok` is absent on older server builds -> treated as healthy.
    if result.version.get("toolchain_ok") is False:
        detail = result.version.get("toolchain_error") or "no detail reported"
        _block(TOOLCHAIN_MESSAGE % detail)
        return 2

    # Healthy. Warn (but allow) on a dev / non-release build.
    try:
        dirty = mcp_probe.is_dirty_version(result.version)
    except Exception:
        dirty = False

    # Workspace drift: the server verifies/indexes ONE workspace. If it is not
    # this checkout (a shared dev server started elsewhere, another worktree),
    # tell the agent to pass crate_name explicitly. Warn only, never block.
    drift = _workspace_drift(result.version.get("workspace"))

    if dirty or drift:
        parts = []
        if dirty:
            parts.append(WARN_MESSAGE % (result.version.get("mcp_version") or "unknown"))
        if drift:
            parts.append(drift)
        _emit_warn_context("\n\n".join(parts))
        return 0

    sys.stderr.write(
        "[verus-gate] Verus MCP healthy (%s): %s\n"
        % (result.transport, json.dumps(result.version))
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
