#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Verus command-line guard, shared across agents (like branch_guard):
#
#   Agents run Verus through the MCP server (`mcp__verus__check`, `profile`,
#   `verify`), never from the shell. Every MCP call emits a trace record and a
#   keyed SMT-log capture; a `cargo verus` / `verus` / `scripts/verus/verify.sh`
#   run from Bash is invisible to the dashboard (and, via cargo's freshness
#   check, may silently replay a stale result). The gate at SessionStart already
#   requires the server to be connected, so the shell path is never needed.
#
# What is blocked (per simple-command segment, after unwrapping `time`,
# `timeout`, `env`, `nice`, `nohup`, `exec`, `command`, leading VAR=val
# assignments, `bash/sh -c "..."` and `bash <script>`):
#
#   verus <args>                    the bare verifier (any path to the binary)
#   rust_verify <args>              the driver behind it
#   cargo verus ... / cargo-verus   cargo-verus (any subcommand, any toolchain)
#   scripts/verus/verify.sh ...     the CI verification script
#
# Allowed: `--help` / `-h` / `--version` / `-V` invocations (no verification
# runs, and there is no MCP equivalent for `--help`), `command -v verus`,
# `which`, and anything that merely mentions verus (grep, cat, echo, heredoc
# bodies).
#
# Entry points (one script, two modes):
#
#   verus_cli_guard.py                    Claude Code PreToolUse hook: reads the
#                                         hook JSON on stdin, inspects Bash
#                                         commands.
#   verus_cli_guard.py check --command C  Agent-agnostic: check one shell
#                                         command (opencode plugin's
#                                         tool.execute.before handler).
#
# Blocks by exiting 2 with the reason on stderr (fed back to the agent so it
# can switch to the MCP tool). FAIL-OPEN: unparseable input exits 0 — the guard
# must never brick the Bash tool. Escape hatch for humans debugging the
# toolchain: VERUS_CLI_GUARD_DISABLE=1.

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import branch_guard  # noqa: E402  (shared tokenizer + repo-root helper)

# Program basenames that run Verus.
VERUS_PROGRAMS = {"verus", "rust_verify", "cargo-verus"}
# Shells whose first positional (or `-c` string) is the real command.
SHELLS = {"bash", "sh", "zsh", "dash", "ksh", "fish"}
# Wrappers that take no argument of their own.
BARE_WRAPPERS = {"time", "nohup", "exec", "nice", "stdbuf", "caffeinate"}
# Flags an invocation may carry that make it informational, not a run.
INFO_FLAGS = {"--help", "-h", "--version", "-V"}
# Pattern for a leading VAR=value assignment word.
ASSIGN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
# Command substitutions: their body is a command, not data.
SUBST_RE = re.compile(r"\$\(([^()]*)\)|`([^`]*)`")

DISABLE_ENV = "VERUS_CLI_GUARD_DISABLE"


def _unwrap(seg):
    """Strip wrapper programs and env assignments so seg[0] is the program
    that actually runs. Returns the reduced segment (possibly empty), or a
    string when a `sh -c "..."` body must be scanned recursively."""
    seg = list(seg)
    while seg:
        prog = os.path.basename(seg[0])
        if ASSIGN_RE.match(seg[0]):
            seg = seg[1:]
        elif prog == "env":
            seg = seg[1:]
            while seg and (
                ASSIGN_RE.match(seg[0]) or seg[0] in ("-i", "--ignore-environment")
            ):
                seg = seg[1:]
            if seg and seg[0] in ("-u", "--unset"):
                seg = seg[2:]
        elif prog == "timeout":
            seg = seg[1:]
            while seg and seg[0].startswith("-"):
                if seg[0] in ("-k", "-s", "--kill-after", "--signal"):
                    seg = seg[2:]
                else:
                    seg = seg[1:]
            seg = seg[1:]  # the DURATION
        elif prog == "nice" and len(seg) > 1 and seg[1] == "-n":
            seg = seg[3:]
        elif prog == "command":
            seg = seg[1:]
            if seg and seg[0] in ("-v", "-V"):
                return []  # `command -v verus`: a lookup, not a run
            while seg and seg[0].startswith("-"):
                seg = seg[1:]
        elif prog in BARE_WRAPPERS:
            seg = seg[1:]
            while seg and seg[0].startswith("-"):
                seg = seg[1:]
        elif prog in SHELLS:
            rest = seg[1:]
            while rest and rest[0].startswith("-"):
                if rest[0] == "-c":
                    return rest[1] if len(rest) > 1 else []
                rest = rest[1:]
            seg = rest  # `bash scripts/verus/verify.sh ...`
        else:
            break
    return seg


def _is_verify_script(path):
    norm = path.replace("\\", "/")
    return os.path.basename(norm) == "verify.sh" and "verus" in norm.split("/")[:-1]


def _cargo_subcommand(args):
    """First non-option word after `cargo` (skips `+toolchain` and flags)."""
    for a in args:
        if a.startswith("+") or a.startswith("-"):
            continue
        return a
    return ""


def _segment_violation(seg):
    """Return a short description of the Verus run in this segment, or None."""
    seg = _unwrap(seg)
    if isinstance(seg, str):
        return _first_violation(seg)
    if not seg:
        return None
    if any(a in INFO_FLAGS for a in seg[1:]):
        return None
    prog = os.path.basename(seg[0])
    if prog in VERUS_PROGRAMS or _is_verify_script(seg[0]):
        return " ".join(seg[:4])
    if prog == "cargo" and _cargo_subcommand(seg[1:]) == "verus":
        return " ".join(seg[:5])
    return None


def _first_violation(command):
    # Heredoc bodies are data (README text, Python source, ...): strip them
    # before both the segment scan and the substitution scan, or a
    # "`cargo verus focus`" in prose would read as a backtick substitution.
    command = branch_guard._strip_heredocs(command)
    for seg in branch_guard._segments(command):
        v = _segment_violation(seg)
        if v:
            return v
    for m in SUBST_RE.finditer(command):
        inner = m.group(1) if m.group(1) is not None else m.group(2)
        v = _first_violation(inner)
        if v:
            return v
    return None


def violations(command):
    """Blocking problems for one shell command (list of strings)."""
    if os.environ.get(DISABLE_ENV) == "1":
        return []
    try:
        v = _first_violation(command)
    except Exception:
        return []  # fail open
    return ["`%s` runs Verus from the shell" % v] if v else []


def _crate_hint():
    root = branch_guard._repo_root()
    return root or "<absolute path of this checkout>"


def _block(probs):
    sys.stderr.write(
        "[verus-guard] BLOCKED:\n"
        + "".join("  - %s\n" % p for p in probs)
        + "Verus runs go through the verus MCP server, never the shell, so every\n"
        "verification is traced and its SMT logs captured. Use the MCP tools:\n"
        "  - check: cargo-verus verification of this crate.\n"
        "    modules=[\"sql::parser::lexer\", \"src/raft/log.rs\"] verifies several\n"
        "    modules in one run (module=\"...\" for one); omit both for the full\n"
        "    crate. Verus flags (--rlimit 60, --triggers-mode silent,\n"
        "    --multiple-errors 20, --verify-function f) go in extra_args, cargo\n"
        "    flags in cargo_args; --lib is added automatically. raw=true returns\n"
        "    the unparsed output; max_errors caps the diagnostics.\n"
        "    crate_name is usually unnecessary (one server per session, pinned to\n"
        "    this checkout); pass crate_name=\"%s\"\n"
        "    if `version` reports a different workspace.\n"
        "    Long runs: background=true, then check_result(job_id) (waits up to\n"
        "    50 s per call); check_cancel(job_id) stops one.\n"
        "  - profile: per-function SMT time / rlimit breakdown (crate_name + module).\n"
        "  - verify: bare `verus` on a standalone file (scratch models, no cargo deps).\n"
        "  - version: reports workspace and toolchain_ok — call it if runs fail oddly.\n"
        "Humans debugging the toolchain can set %s=1 to bypass this guard.\n"
        % (_crate_hint(), DISABLE_ENV)
    )
    return 2


def cmd_claude_hook():
    """Default mode: Claude Code PreToolUse hook (hook JSON on stdin)."""
    try:
        raw = sys.stdin.read()
        data = json.loads(raw) if raw.strip() else {}
    except Exception:
        return 0
    if data.get("tool_name") != "Bash":
        return 0
    command = (data.get("tool_input") or {}).get("command") or ""
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


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        return cmd_claude_hook()
    if argv[0] == "check":
        return cmd_check(argv[1:])
    # Unknown mode: fail open — the guard must never brick a hook chain.
    sys.stderr.write("[verus-guard] unknown mode '%s' (ignored)\n" % argv[0])
    return 0


if __name__ == "__main__":
    sys.exit(main())
