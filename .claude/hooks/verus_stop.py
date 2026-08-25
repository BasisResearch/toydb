#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code `Stop` hook: capture the session trace and upload it.
#
# Reads the hook-input JSON from stdin, finds `transcript_path`, parses the
# transcript into the shared envelope, merges server-side Verus MCP records, and
# POSTs it. FAIL-SOFT: any error is logged to stderr and the hook exits 0 so the
# user's session is never disrupted by telemetry.

import json
import os
import sys

# Make the verus_trace package importable regardless of cwd.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def main():
    try:
        raw = sys.stdin.read()
        hook_input = json.loads(raw) if raw.strip() else {}
    except Exception as exc:
        sys.stderr.write("[verus-trace] bad hook input: %s\n" % exc)
        return 0

    transcript_path = hook_input.get("transcript_path")
    if not transcript_path:
        sys.stderr.write("[verus-trace] no transcript_path in hook input\n")
        return 0
    transcript_path = os.path.expanduser(transcript_path)
    if not os.path.exists(transcript_path):
        sys.stderr.write("[verus-trace] transcript not found: %s\n" % transcript_path)
        return 0

    try:
        from verus_trace import claude_adapter, envelope, mcp_probe

        # Stamp the PRECISE mcp_version (and verus_version) onto the trace from
        # the server's `version` tool. `mcp_version` is the canonical id (e.g.
        # 0.1.0+g1b40a7d.dirty); it is what the whole experiment keys on and how
        # the dashboard buckets dev builds separately from releases.
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

        env_doc = claude_adapter.build_from_transcript(
            transcript_path,
            mcp_version=mcp_version,
            verus_version=verus_version,
        )
        envelope.post_envelope(env_doc)
    except Exception as exc:
        sys.stderr.write("[verus-trace] capture failed (fail-soft): %s\n" % exc)
    return 0


if __name__ == "__main__":
    sys.exit(main())
