#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# opencode plugin runner: the Python side of the opencode adapter.
#
#   verus_runner.py gate
#       Probe the Verus MCP server. Exit 0 if healthy, non-zero otherwise
#       (fail-closed). The plugin turns a non-zero exit into a session abort.
#
#   verus_runner.py capture [SESSION_ID] [--directory DIR]
#       Read the session from the opencode SQLite store, map it to the shared
#       envelope, and POST it (fail-soft). If SESSION_ID is omitted, the most
#       recently updated session (optionally scoped to DIR) is used.

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
# The shared verus_trace package lives under .claude/hooks in the repo root.
_PKG = os.path.abspath(os.path.join(_HERE, "..", "..", ".claude", "hooks"))
if os.path.isdir(os.path.join(_PKG, "verus_trace")):
    sys.path.insert(0, _PKG)


def cmd_gate():
    # Self-provision the branch-discipline git hooks (core.hooksPath ->
    # .githooks); fail-soft, never blocks the session.
    try:
        import branch_guard

        branch_guard.ensure_hooks_path()
    except Exception:
        pass

    from verus_trace import mcp_probe

    res = mcp_probe.probe_version()
    if res.healthy:
        return 0
    sys.stdout.write((res.error or "server not healthy"))
    sys.stdout.write("\n")
    return 1


def cmd_capture(argv):
    session_id = ""
    directory = None
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--directory" and i + 1 < len(argv):
            directory = argv[i + 1]
            i += 2
            continue
        if not a.startswith("--"):
            session_id = a
        i += 1

    try:
        from verus_trace import opencode_adapter, envelope, mcp_probe, smt_capture

        db_path = opencode_adapter._default_db_path()
        if not session_id:
            session_id = opencode_adapter.latest_session_id(db_path, directory)
        if not session_id:
            sys.stderr.write("[verus-trace] no opencode session found\n")
            return 0

        # Stamp the PRECISE mcp_version (e.g. 0.1.0+g1b40a7d.dirty) from the
        # server's `version` tool; this is what the dashboard keys on and how it
        # buckets dev builds apart from releases.
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

        env_doc = opencode_adapter.build_from_db(
            session_id,
            db_path=db_path,
            mcp_version=mcp_version,
            verus_version=verus_version,
        )
        # Local archive (envelope + the session's raw rows as JSONL) next to
        # this session's SMT captures, before the upload is attempted.
        try:
            raw = opencode_adapter.dump_session_jsonl(db_path, session_id)
        except Exception as exc:
            sys.stderr.write("[verus-trace] opencode row dump failed: %s\n" % exc)
            raw = None
        smt_capture.archive_session(session_id, env_doc, transcript_bytes=raw)
        envelope.post_envelope(env_doc)
    except Exception as exc:
        sys.stderr.write("[verus-trace] opencode capture failed (fail-soft): %s\n" % exc)
    return 0


def main(argv):
    if not argv:
        sys.stderr.write("usage: verus_runner.py gate|capture ...\n")
        return 2
    sub = argv[0]
    if sub == "gate":
        return cmd_gate()
    if sub == "capture":
        return cmd_capture(argv[1:])
    sys.stderr.write("unknown subcommand: %s\n" % sub)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
