#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Solver guard, shared across agents (like branch_guard):
#
#   verus, z3, and cvc4/cvc5 are NEVER run manually from the shell in this
#   repo. All verification goes through the Verus MCP server
#   (verus-tools-mcp), which runs pinned, hash-verified solver builds from the
#   BasisResearch forks and emits the telemetry every session depends on. A
#   manual `verus`/`z3`/`cvc5` invocation would bypass version pinning AND
#   drop the run from the dashboard, so it is blocked, not discouraged.
#
# Entry points (one script, three modes):
#
#   solver_guard.py                    Claude Code / Codex PreToolUse hook:
#                                      reads the hook JSON on stdin, inspects
#                                      shell commands. Codex >= 0.152 fires
#                                      PreToolUse with the same JSON shape
#                                      (tool_name / tool_input); shell
#                                      commands that arrive as argv lists are
#                                      handled.
#   solver_guard.py check --command C  Agent-agnostic: check one shell command
#                                      (used by the opencode plugin's
#                                      tool.execute.before handler).
#
# Blocks by exiting 2 with the reason on stderr (fed back to the agent so it
# can correct itself). FAIL-OPEN: unparseable input exits 0 — the guard must
# never brick the Bash tool.

import json
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from branch_guard import (  # noqa: E402
    SHELL_TOOL_NAMES,
    _segments,
    _strip_heredocs,
    command_from_tool_input,
)

# Program basenames that are managed by the MCP server. `verus-tools-mcp`
# itself is NOT blocked: launching/probing the server is how sessions gate.
BLOCKED = {
    "verus": "verus",
    "rust_verify": "verus",  # the underlying Verus driver binary
    "z3": "z3",
    "cvc5": "cvc5",
    "cvc4": "cvc5",
    "cargo-verus": "verus",
}

# Wrappers whose next token is the real command; `timeout` also skips its
# duration argument, and leading VAR=... assignments are stripped first.
WRAPPERS = {"env", "command", "exec", "time", "nice", "nohup", "sudo", "xargs", "caffeinate"}

POLICY = (
    "Solver policy: verus, z3 and cvc5 are never run manually in this repo - "
    "use the Verus MCP tools instead (verify / profile / version, etc.). The "
    "MCP server runs pinned, hash-verified solver builds from the "
    "BasisResearch forks and records the telemetry this project's evaluation "
    "depends on; a manual run bypasses both. If an MCP tool is missing for "
    "what you need, say so rather than shelling out."
)


def _blocked_prog(seg):
    """The policy name violated by one simple-command segment, or None."""
    toks = list(seg)
    # Strip leading VAR=value assignments.
    while toks and "=" in toks[0] and not toks[0].startswith(("/", ".")):
        name = toks[0].split("=", 1)[0]
        if name.isidentifier():
            toks = toks[1:]
        else:
            break
    # Unwrap common wrappers (`env -i`, `timeout 5 z3`, `xargs z3`, ...).
    while toks:
        prog = os.path.basename(toks[0])
        if prog in WRAPPERS:
            toks = toks[1:]
            # Skip the wrapper's own leading options (e.g. `env -i`, `xargs -n1`).
            while toks and toks[0].startswith("-"):
                toks = toks[1:]
            continue
        if prog == "timeout":
            # Skip options and numeric tokens (option values and the duration,
            # e.g. `timeout -k 5 30 cvc5` -> skip `-k`, `5`, `30`).
            toks = toks[1:]
            while toks and (
                toks[0].startswith("-")
                or toks[0].rstrip("smhd").isdigit()
            ):
                toks = toks[1:]
            continue
        break
    if not toks:
        return None
    prog = os.path.basename(toks[0])
    if prog in BLOCKED:
        return BLOCKED[prog]
    # `cargo verus ...` runs the verifier through cargo.
    if prog == "cargo" and len(toks) > 1 and toks[1] == "verus":
        return "verus"
    return None


def violations(command):
    probs = []
    for seg in _segments(_strip_heredocs(command)):
        if not seg:
            continue
        hit = _blocked_prog(seg)
        if hit:
            probs.append(
                "manual `%s` invocation is forbidden (in: %s)"
                % (hit, " ".join(seg[:6]) + (" ..." if len(seg) > 6 else ""))
            )
    return probs


def _block(probs):
    sys.stderr.write(
        "[solver-guard] BLOCKED:\n"
        + "".join("  - %s\n" % p for p in probs)
        + POLICY
        + "\n"
    )
    return 2


def cmd_hook():
    """Default mode: PreToolUse hook JSON on stdin (Claude Code and Codex)."""
    try:
        raw = sys.stdin.read()
        data = json.loads(raw) if raw.strip() else {}
    except Exception:
        return 0
    if str(data.get("tool_name") or "").lower() not in SHELL_TOOL_NAMES:
        return 0
    command = command_from_tool_input(data.get("tool_input"))
    if not command:
        return 0
    probs = violations(command)
    if probs:
        return _block(probs)
    return 0


def cmd_check(argv):
    """`check --command <cmd>` (or `check <cmd>`): agent-agnostic single-
    command check, used by the opencode plugin."""
    command = ""
    if len(argv) >= 2 and argv[0] == "--command":
        command = argv[1]
    elif argv:
        command = argv[0]
    probs = violations(command)
    if probs:
        return _block(probs)
    return 0


def main(argv):
    if argv and argv[0] == "check":
        return cmd_check(argv[1:])
    return cmd_hook()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
