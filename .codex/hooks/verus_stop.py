#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Codex `[[hooks.Stop]]` command hook: capture the session trace and upload it.
#
# Codex fires this as a turn ends. It does not pass a transcript path the way
# Claude Code does, so this hook locates the current rollout log under
# ~/.codex/sessions/YYYY/MM/DD/rollout-<ts>-<uuid>.jsonl. Codex may provide the
# session id / rollout path via env (CODEX_SESSION_ID / CODEX_ROLLOUT_PATH) or
# on stdin as JSON; we honour those and fall back to the newest rollout for the
# current working directory.
#
# Because Codex exposes no pre-run event, it cannot hard-gate. This hook checks
# whether the Verus MCP tools were actually available in the rollout and sets
# gate_violation=true if not, so an ungated Codex run is recorded and visible on
# the dashboard rather than silently counted.
#
# FAIL-SOFT on capture: never disrupts the user's Codex session.

import glob
import json
import os
import sys

# Locate the committed verus_trace package. It lives under the toyDB repo's
# .claude/hooks/. The hook is committed at .codex/hooks/ in the same repo, so we
# resolve the package relative to this file, then fall back to env override.
_HERE = os.path.dirname(os.path.abspath(__file__))
_CANDIDATES = [
    os.environ.get("VERUS_TRACE_PKG_DIR", ""),
    os.path.join(_HERE, "..", "..", ".claude", "hooks"),
    os.path.join(_HERE, "..", "..", "verus_trace_pkg"),
]
for _c in _CANDIDATES:
    if _c and os.path.isdir(os.path.join(_c, "verus_trace")):
        sys.path.insert(0, os.path.abspath(_c))
        break


def _sessions_root():
    override = os.environ.get("CODEX_SESSIONS_DIR")
    if override:
        return os.path.expanduser(override)
    return os.path.expanduser("~/.codex/sessions")


def _find_rollout(hook_input):
    # 1. Explicit path from env or stdin.
    for key in ("rollout_path", "rolloutPath", "transcript_path"):
        val = hook_input.get(key)
        if val and os.path.exists(os.path.expanduser(val)):
            return os.path.expanduser(val)
    env_path = os.environ.get("CODEX_ROLLOUT_PATH")
    if env_path and os.path.exists(os.path.expanduser(env_path)):
        return os.path.expanduser(env_path)

    # 2. By session id anywhere under the sessions root.
    sid = (
        hook_input.get("session_id")
        or hook_input.get("sessionId")
        or os.environ.get("CODEX_SESSION_ID")
    )
    root = _sessions_root()
    if sid:
        matches = glob.glob(
            os.path.join(root, "**", "rollout-*%s*.jsonl" % sid), recursive=True
        )
        if matches:
            return max(matches, key=os.path.getmtime)

    # 3. Newest rollout overall.
    matches = glob.glob(os.path.join(root, "**", "rollout-*.jsonl"), recursive=True)
    if matches:
        return max(matches, key=os.path.getmtime)
    return None


def main():
    # Codex has no pre-tool event, so its branch-discipline enforcement is the
    # committed git hooks (.githooks). Self-provision core.hooksPath here —
    # the only per-session Codex entry point we have. Fail-soft.
    try:
        import branch_guard

        branch_guard.ensure_hooks_path()
    except Exception:
        pass

    try:
        raw = sys.stdin.read()
        hook_input = json.loads(raw) if raw.strip() else {}
    except Exception:
        hook_input = {}

    rollout = _find_rollout(hook_input)
    if not rollout:
        sys.stderr.write("[verus-trace] no Codex rollout found\n")
        return 0

    # Local archive first: the rollout is kept next to this session's SMT
    # captures whatever happens to the upload below; the envelope joins it
    # once built.
    from verus_trace import smt_capture

    session_id = hook_input.get("session_id") or hook_input.get("sessionId") or ""
    if session_id:
        smt_capture.archive_session(session_id, transcript_path=rollout)

    try:
        from verus_trace import codex_adapter, envelope, mcp_probe

        # Codex has no session-start event, so we probe at Stop time to stamp the
        # PRECISE mcp_version (e.g. 0.1.0+g1b40a7d.dirty) onto the envelope; this
        # is what the dashboard keys on and how dev builds are bucketed apart.
        mcp_version = ""
        verus_version = ""
        try:
            res = mcp_probe.probe_version()
            if res.healthy:
                mcp_version = (
                    res.version.get("mcp_version")
                    or res.version.get("server_version")
                    or ""
                )
                verus_version = res.version.get("verus_version", "")
        except Exception:
            pass

        env_doc = codex_adapter.build_from_rollout(
            rollout,
            mcp_version=mcp_version,
            verus_version=verus_version,
        )
        smt_capture.archive_session(
            session_id or env_doc.get("session_id"), env_doc,
            None if session_id else rollout,
        )
        envelope.post_envelope(env_doc)
    except Exception as exc:
        sys.stderr.write("[verus-trace] Codex capture failed (fail-soft): %s\n" % exc)
    return 0


if __name__ == "__main__":
    sys.exit(main())
