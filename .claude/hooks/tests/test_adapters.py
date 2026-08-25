# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Adapter tests for the Verus trace-capture system (Component 2). Stdlib only.
#
# Each test drives one agent adapter against a checked-in fixture and asserts
# the produced envelope conforms to the CONTRACTS.md session-trace schema
# (field names, nesting, is_mcp flagging, gate_violation, totals) and that the
# server-side MCP trace merge folds subprocess detail onto the matching call.
#
# No network: the adapters build envelopes in-process; the POST path is
# exercised separately via VERUS_INGEST_DRY_RUN.
#
# Run:  python3 .claude/hooks/tests/test_adapters.py

import json
import os
import sqlite3
import sys
import tempfile
import unittest

# Make the hooks dir importable so `verus_trace` resolves.
HOOKS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HOOKS_DIR)

from verus_trace import envelope as env  # noqa: E402
from verus_trace import claude_adapter  # noqa: E402
from verus_trace import codex_adapter  # noqa: E402
from verus_trace import opencode_adapter  # noqa: E402
from verus_trace import mcp_probe  # noqa: E402

FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")

# CONTRACTS.md session-trace envelope: required top-level keys.
ENVELOPE_KEYS = {
    "session_id", "agent", "agent_version", "author_email", "machine", "repo",
    "branch", "commit_sha", "mcp_version", "verus_version", "rust_toolchain",
    "gate_violation", "started_at", "ended_at", "totals", "turns", "tool_calls",
}
TOTALS_KEYS = {
    "tokens_in", "tokens_out", "cache_read", "tool_calls", "mcp_tool_calls",
    "turns",
}
TURN_KEYS = {"idx", "role", "text", "tokens_in", "tokens_out", "ts"}
TOOLCALL_KEYS = {"turn_idx", "name", "is_mcp", "args", "result", "duration_ms", "ts"}


def assert_envelope_shape(tc, envelope):
    """Assert an envelope matches the CONTRACTS schema (keys + types)."""
    tc.assertEqual(ENVELOPE_KEYS, set(envelope.keys()), "top-level keys")
    tc.assertIn(envelope["agent"], ("claude", "codex", "opencode"))
    tc.assertEqual(envelope["repo"], "BasisResearch/toydb")
    tc.assertIsInstance(envelope["gate_violation"], bool)

    totals = envelope["totals"]
    tc.assertTrue(TOTALS_KEYS <= set(totals.keys()), "totals keys")
    for k in TOTALS_KEYS:
        tc.assertIsInstance(totals[k], int, "totals.%s int" % k)

    tc.assertEqual(totals["turns"], len(envelope["turns"]))
    tc.assertEqual(totals["tool_calls"], len(envelope["tool_calls"]))
    tc.assertEqual(
        totals["mcp_tool_calls"],
        sum(1 for c in envelope["tool_calls"] if c.get("is_mcp")),
    )

    for turn in envelope["turns"]:
        tc.assertTrue(TURN_KEYS <= set(turn.keys()), "turn keys: %r" % turn)
        tc.assertIn(turn["role"], ("user", "assistant"))
    for call in envelope["tool_calls"]:
        tc.assertTrue(TOOLCALL_KEYS <= set(call.keys()), "tool_call keys: %r" % call)
        tc.assertIsInstance(call["is_mcp"], bool)

    # Must serialize to JSON (the POST body).
    json.dumps(envelope, default=str)


class ClaudeAdapterTest(unittest.TestCase):
    def test_envelope_shape_and_mcp_flag(self):
        path = os.path.join(FIXTURES, "claude_transcript.jsonl")
        # No server merge here (point the trace dir at an empty temp dir).
        with tempfile.TemporaryDirectory() as empty:
            os.environ["VERUS_MCP_LOG_DIR"] = empty
            envelope = claude_adapter.build_from_transcript(
                path, mcp_version="0.1.0", verus_version="0.2026.08.23"
            )
        assert_envelope_shape(self, envelope)
        self.assertEqual(envelope["agent"], "claude")
        self.assertEqual(envelope["session_id"], "claude-sess-1")
        self.assertEqual(envelope["agent_version"], "1.2.3")

        # Two tool calls: mcp__verus__verify (MCP) and Bash (not MCP). The
        # adapter preserves the agent-native name; is_mcp is the classifier.
        by_name = {c["name"]: c["is_mcp"] for c in envelope["tool_calls"]}
        self.assertTrue(by_name.get("mcp__verus__verify"))
        self.assertFalse(by_name.get("Bash"))
        self.assertEqual(envelope["totals"]["mcp_tool_calls"], 1)
        self.assertEqual(envelope["totals"]["tool_calls"], 2)

        # Token totals summed across assistant turns.
        self.assertEqual(envelope["totals"]["tokens_in"], 1000 + 1200 + 1300)
        self.assertEqual(envelope["totals"]["tokens_out"], 50 + 30 + 80)
        self.assertEqual(envelope["totals"]["cache_read"], 200 + 900 + 1000)

    def test_server_record_merge(self):
        path = os.path.join(FIXTURES, "claude_transcript.jsonl")
        os.environ["VERUS_MCP_LOG_DIR"] = FIXTURES  # contains server_trace.jsonl
        try:
            envelope = claude_adapter.build_from_transcript(path, mcp_version="0.1.0")
        finally:
            os.environ.pop("VERUS_MCP_LOG_DIR", None)

        verify_calls = [c for c in envelope["tool_calls"] if c.get("is_mcp")]
        self.assertEqual(len(verify_calls), 1)
        call = verify_calls[0]
        # Server detail folded in by tool-name + timestamp-window merge.
        self.assertEqual(call.get("connection_id"), "conn-1")
        self.assertEqual(call.get("duration_ms"), 4200)
        self.assertIsInstance(call.get("subprocess"), dict)
        self.assertEqual(call["subprocess"]["z3_time_ms"], 3800)


class CodexAdapterTest(unittest.TestCase):
    def test_gated_session(self):
        path = os.path.join(FIXTURES, "codex_rollout.jsonl")
        with tempfile.TemporaryDirectory() as empty:
            os.environ["VERUS_MCP_LOG_DIR"] = empty
            envelope = codex_adapter.build_from_rollout(path, mcp_version="0.1.0")
        assert_envelope_shape(self, envelope)
        self.assertEqual(envelope["agent"], "codex")
        self.assertEqual(envelope["session_id"], "codex-sess-1")
        # A Verus MCP tool was available -> not a gate violation.
        self.assertFalse(envelope["gate_violation"])
        self.assertEqual(envelope["totals"]["mcp_tool_calls"], 1)
        # Cumulative token totals folded onto the last assistant turn.
        self.assertEqual(envelope["totals"]["tokens_in"], 3200)
        self.assertEqual(envelope["totals"]["tokens_out"], 140)
        self.assertEqual(envelope["totals"]["cache_read"], 800)

    def test_ungated_session_marks_violation(self):
        path = os.path.join(FIXTURES, "codex_rollout_ungated.jsonl")
        with tempfile.TemporaryDirectory() as empty:
            os.environ["VERUS_MCP_LOG_DIR"] = empty
            envelope = codex_adapter.build_from_rollout(path, mcp_version="0.1.0")
        assert_envelope_shape(self, envelope)
        # No Verus MCP tool ever available -> gate_violation True (best-effort).
        self.assertTrue(envelope["gate_violation"])
        self.assertEqual(envelope["totals"]["mcp_tool_calls"], 0)


class OpencodeAdapterTest(unittest.TestCase):
    def _build_db(self, path):
        conn = sqlite3.connect(path)
        conn.executescript(
            """
            CREATE TABLE session (id TEXT PRIMARY KEY, directory TEXT,
                version TEXT, time_created INTEGER, time_updated INTEGER);
            CREATE TABLE message (id TEXT PRIMARY KEY, session_id TEXT,
                time_created INTEGER, data TEXT);
            CREATE TABLE part (id TEXT PRIMARY KEY, message_id TEXT,
                time_created INTEGER, data TEXT);
            """
        )
        conn.execute(
            "INSERT INTO session VALUES (?,?,?,?,?)",
            ("oc-sess-1", "/repo", "0.3.0", 1000, 2000),
        )
        # user message
        conn.execute(
            "INSERT INTO message VALUES (?,?,?,?)",
            ("m1", "oc-sess-1", 1000, json.dumps({"role": "user", "tokens": {}})),
        )
        conn.execute(
            "INSERT INTO part VALUES (?,?,?,?)",
            ("p1", "m1", 1000, json.dumps({"type": "text", "text": "Verify storage"})),
        )
        # assistant message with tokens + an MCP tool call
        conn.execute(
            "INSERT INTO message VALUES (?,?,?,?)",
            ("m2", "oc-sess-1", 1500, json.dumps({
                "role": "assistant",
                "tokens": {"input": 2000, "output": 90, "cache": {"read": 400}},
            })),
        )
        conn.execute(
            "INSERT INTO part VALUES (?,?,?,?)",
            ("p2", "m2", 1500, json.dumps({"type": "text", "text": "Running verify."})),
        )
        conn.execute(
            "INSERT INTO part VALUES (?,?,?,?)",
            ("p3", "m2", 1501, json.dumps({
                "type": "tool", "tool": "verus_verify",
                "state": {"input": {"path": "src/storage.rs"},
                          "output": "verified: 3, errors: 0",
                          "time": {"start": 1500, "end": 5700}},
            })),
        )
        conn.commit()
        conn.close()

    def test_envelope_shape_and_mcp_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            db = os.path.join(tmp, "opencode.db")
            self._build_db(db)
            os.environ["VERUS_MCP_LOG_DIR"] = tmp  # no server records here
            sid = opencode_adapter.latest_session_id(db)
            self.assertEqual(sid, "oc-sess-1")
            envelope = opencode_adapter.build_from_db(
                sid, db_path=db, mcp_version="0.1.0"
            )
        assert_envelope_shape(self, envelope)
        self.assertEqual(envelope["agent"], "opencode")
        self.assertEqual(envelope["totals"]["mcp_tool_calls"], 1)
        self.assertEqual(envelope["totals"]["tokens_in"], 2000)
        self.assertEqual(envelope["totals"]["tokens_out"], 90)
        self.assertEqual(envelope["totals"]["cache_read"], 400)
        call = envelope["tool_calls"][0]
        self.assertTrue(call["is_mcp"])
        self.assertEqual(call["name"], "verify")   # bare name after prefix strip
        self.assertEqual(call["duration_ms"], 4200)


class McpVersionThreadingTest(unittest.TestCase):
    """The whole experiment keys on the precise mcp_version. A dirty (dev-build)
    mcp_version probed from the `version` tool must land on the envelope's
    mcp_version field so the dashboard buckets dev sessions apart. We inject the
    probed version rather than requiring a live server."""

    DIRTY = {
        "server_name": "verus-tools-mcp",
        "server_version": "0.1.0",
        "git_commit": "1b40a7d",
        "git_dirty": True,
        "mcp_version": "0.1.0+g1b40a7d.dirty",
        "verus_version": "0.2026.08.23",
        "rust_toolchain": "1.97.1",
        "protocol": "mcp",
    }

    def test_dirty_mcp_version_flows_into_envelope(self):
        path = os.path.join(FIXTURES, "claude_transcript.jsonl")
        # Mirror what the Stop hooks do: prefer the precise mcp_version.
        mcp_version = self.DIRTY.get("mcp_version") or self.DIRTY.get("server_version")
        verus_version = self.DIRTY.get("verus_version")
        with tempfile.TemporaryDirectory() as empty:
            os.environ["VERUS_MCP_LOG_DIR"] = empty
            try:
                envelope = claude_adapter.build_from_transcript(
                    path, mcp_version=mcp_version, verus_version=verus_version
                )
            finally:
                os.environ.pop("VERUS_MCP_LOG_DIR", None)
        assert_envelope_shape(self, envelope)
        self.assertEqual(envelope["mcp_version"], "0.1.0+g1b40a7d.dirty")
        self.assertIn(".dirty", envelope["mcp_version"])
        self.assertEqual(envelope["verus_version"], "0.2026.08.23")

    def test_is_dirty_version_classifier(self):
        self.assertTrue(mcp_probe.is_dirty_version(self.DIRTY))
        self.assertTrue(
            mcp_probe.is_dirty_version({"mcp_version": "0.1.0+unknown"})
        )
        self.assertFalse(
            mcp_probe.is_dirty_version(
                {"mcp_version": "0.1.0+g1b40a7d", "git_dirty": False}
            )
        )
        self.assertFalse(mcp_probe.is_dirty_version({}))


class PostDryRunTest(unittest.TestCase):
    def test_dry_run_post_never_raises(self):
        os.environ["VERUS_INGEST_DRY_RUN"] = "1"
        try:
            ok = env.post_envelope({"session_id": "x", "turns": [], "tool_calls": []})
        finally:
            os.environ.pop("VERUS_INGEST_DRY_RUN", None)
        self.assertTrue(ok)


if __name__ == "__main__":
    unittest.main(verbosity=2)
