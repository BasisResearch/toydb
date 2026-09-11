#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Tests for the SMT query capture layer: the verus_trace.smt_capture library
# (kind mapping, marker parsing, collect, batched upload, catch-up) and the
# PostToolUse hook entry (.claude/hooks/smt_capture.py) end to end against a
# stub HTTP server on localhost. No real network, no verus binary.

import base64
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from http.server import BaseHTTPRequestHandler, HTTPServer

HOOKS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HOOKS_DIR)

from verus_trace import claude_adapter  # noqa: E402
from verus_trace import smt_capture as smt  # noqa: E402

FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")
TOKEN = "smt-test-token"


class _Capture(BaseHTTPRequestHandler):
    posts = []
    reject_next = False

    def do_POST(self):
        length = int(self.headers.get("Content-Length", "0"))
        body = json.loads(self.rfile.read(length).decode("utf-8"))
        _Capture.posts.append(
            {"path": self.path, "auth": self.headers.get("Authorization"), "body": body}
        )
        if _Capture.reject_next:
            _Capture.reject_next = False
            resp = {"ok": True, "stored": 0, "indexed_queries": 0,
                    "rejected": [{"filename": f["filename"], "error": "sha256 mismatch"}
                                 for f in body.get("files", [])]}
        else:
            resp = {"ok": True, "stored": len(body.get("files", [])),
                    "indexed_queries": 0, "rejected": []}
        out = json.dumps(resp).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(out)))
        self.end_headers()
        self.wfile.write(out)

    def log_message(self, fmt, *args):  # quiet
        pass


class SmtCaptureLibTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = HTTPServer(("127.0.0.1", 0), _Capture)
        cls.url = "http://127.0.0.1:%d/verus/ingest/smt" % cls.server.server_port
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()

    def setUp(self):
        _Capture.posts = []
        _Capture.reject_next = False
        self.tmp = tempfile.mkdtemp(prefix="smt-capture-test-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        os.environ.pop("VERUS_INGEST_DRY_RUN", None)

    def _producer_dir(self, files):
        d = tempfile.mkdtemp(prefix="prod-", dir=self.tmp)
        for name, content in files.items():
            with open(os.path.join(d, name), "w", encoding="utf-8") as fh:
                fh.write(content)
        return d

    # -- pure helpers ------------------------------------------------------
    def test_kind_mapping(self):
        for name, kind in (
            ("root.smt2", "smt2"),
            ("root.smt_transcript", "smt_transcript"),
            ("root-final.air", "air_final"),
            ("root.air", "air"),
            ("crate.vir", "vir"),
            ("crate-simple.vir", "vir_simple"),
            ("root-poly.vir", "vir_poly"),
            ("root-sst.vir", "vir_sst"),
            ("crate.triggers", "triggers"),
            ("crate-call-graph-nostd-initial.dot", "call_graph"),
            ("sql__parser__float_trust.interp", "interp"),
            ("crate.impl_names", "impl_names"),
            ("crate-trait-conflicts.rs", "trait_conflicts"),
            ("mystery.bin", "other"),
        ):
            self.assertEqual(smt.kind_of(name), kind, name)

    def test_find_log_dir_last_marker_wins(self):
        text = ("verus: verifying 18 module(s)\n"
                "verus-smt-log-dir: /tmp/a\nnoise\n"
                "  verus-smt-log-dir: /tmp/b  \n")
        self.assertEqual(smt.find_log_dir(text), "/tmp/b")
        self.assertIsNone(smt.find_log_dir("no marker here"))
        self.assertIsNone(smt.find_log_dir(""))

    def test_smt_url_derived_from_ingest_url(self):
        os.environ["VERUS_INGEST_URL"] = "http://127.0.0.1:8090/verus/ingest/session"
        try:
            self.assertEqual(smt.smt_url(), "http://127.0.0.1:8090/verus/ingest/smt")
        finally:
            del os.environ["VERUS_INGEST_URL"]

    # -- collect -----------------------------------------------------------
    def test_collect_moves_and_stamps_meta(self):
        prod = self._producer_dir({"m.smt2": ";; Function-Def t::f\n", "m.smt_transcript": "x"})
        dest = smt.collect(prod, "sess-1", "tu_9", {"branch": "yl/x"}, root=self.tmp)
        self.assertTrue(dest and os.path.isdir(dest))
        self.assertFalse(os.path.exists(prod))
        self.assertEqual(smt.artifact_files(dest), ["m.smt2", "m.smt_transcript"])
        with open(os.path.join(dest, "meta.json")) as fh:
            meta = json.load(fh)
        self.assertEqual(meta["session_id"], "sess-1")
        self.assertEqual(meta["tool_use_id"], "tu_9")
        self.assertEqual(meta["branch"], "yl/x")

    def test_collect_empty_dir_is_dropped(self):
        prod = self._producer_dir({})
        self.assertIsNone(smt.collect(prod, "s", "t", {}, root=self.tmp))
        self.assertFalse(os.path.exists(prod))

    # -- upload ------------------------------------------------------------
    def _collected(self, tuid="tu_1", content="Q" * 100):
        prod = self._producer_dir({"m.smt2": content, "m.smt_transcript": content})
        return smt.collect(prod, "sess-up", tuid,
                           {"branch": "yl/x", "commit_sha": "cafe", "source": "agent",
                            "success": False, "verified": 5, "errors": 1},
                           root=self.tmp)

    def test_upload_posts_and_marks(self):
        dest = self._collected()
        ok = smt.upload(dest, url=self.url, token=TOKEN)
        self.assertTrue(ok)
        self.assertTrue(os.path.exists(os.path.join(dest, ".uploaded")))
        (post,) = _Capture.posts
        self.assertEqual(post["auth"], "Bearer " + TOKEN)
        body = post["body"]
        self.assertEqual(body["session_id"], "sess-up")
        self.assertEqual(body["tool_use_id"], "tu_1")
        self.assertEqual(body["source"], "agent")
        self.assertEqual(body["branch"], "yl/x")
        self.assertIs(body["success"], False)
        self.assertEqual(body["verified"], 5)
        self.assertEqual(len(body["files"]), 2)
        f = body["files"][0]
        raw = gzip.decompress(base64.b64decode(f["data_b64"]))
        self.assertEqual(f["sha256"], hashlib.sha256(raw).hexdigest())
        self.assertEqual(f["encoding"], "gzip")
        # transcripts/smt2 first
        self.assertEqual({x["kind"] for x in body["files"]}, {"smt2", "smt_transcript"})

    def test_upload_reads_zstd_artifacts(self):
        from compression.zstd import compress

        dest = self._collected()
        path = os.path.join(dest, "m.smt2")
        with open(path, "rb") as fh:
            raw = fh.read()
        with open(path + ".zst", "wb") as fh:
            fh.write(compress(raw))
        os.remove(path)
        self.assertTrue(smt.upload(dest, url=self.url, token=TOKEN))
        (post,) = _Capture.posts
        f = [x for x in post["body"]["files"] if x["filename"] == "m.smt2"][0]
        self.assertEqual(f["kind"], "smt2")
        self.assertEqual(gzip.decompress(base64.b64decode(f["data_b64"])), raw)
        self.assertEqual(f["sha256"], hashlib.sha256(raw).hexdigest())

    def test_archive_session_writes_transcript_and_envelope(self):
        from compression.zstd import decompress

        tr = os.path.join(self.tmp, "t.jsonl")
        with open(tr, "w", encoding="utf-8") as fh:
            fh.write('{"type":"user"}\n' * 50)
        env_doc = {"session_id": "sess-arc", "tool_calls": [{"tool_use_id": "tu_1"}]}
        dest = smt.archive_session("sess-arc", env_doc, tr, root=self.tmp)
        self.assertEqual(dest, os.path.join(self.tmp, "sess-arc"))
        with open(os.path.join(dest, "transcript.jsonl.zst"), "rb") as fh:
            self.assertEqual(decompress(fh.read()), open(tr, "rb").read())
        with open(os.path.join(dest, "session.json.zst"), "rb") as fh:
            self.assertEqual(json.loads(decompress(fh.read())), env_doc)
        # Session files never show up as pending captures.
        self.assertEqual(smt.pending(root=self.tmp), [])
        # Raw bytes (opencode) take the place of a transcript file.
        dest = smt.archive_session("sess-arc", None, transcript_bytes=b"{}\n", root=self.tmp)
        with open(os.path.join(dest, "transcript.jsonl.zst"), "rb") as fh:
            self.assertEqual(decompress(fh.read()), b"{}\n")
        # Missing transcript / no envelope is fail-soft, not an error.
        self.assertIsNotNone(smt.archive_session("sess-arc", None, "/nonexistent", root=self.tmp))

    def test_upload_batches_large_captures(self):
        old = smt.BATCH_GZ_BYTES
        smt.BATCH_GZ_BYTES = 64  # force one file per batch
        try:
            dest = self._collected(tuid="tu_batch", content=os.urandom(400).hex())
            ok = smt.upload(dest, url=self.url, token=TOKEN)
        finally:
            smt.BATCH_GZ_BYTES = old
        self.assertTrue(ok)
        self.assertEqual(len(_Capture.posts), 2)
        for p in _Capture.posts:
            self.assertEqual(p["body"]["tool_use_id"], "tu_batch")
            self.assertEqual(len(p["body"]["files"]), 1)

    def test_rejected_files_leave_capture_pending(self):
        dest = self._collected(tuid="tu_rej")
        _Capture.reject_next = True
        ok = smt.upload(dest, url=self.url, token=TOKEN)
        self.assertFalse(ok)
        self.assertFalse(os.path.exists(os.path.join(dest, ".uploaded")))
        # catch-up retries it
        self.assertIn(dest, smt.pending(root=self.tmp))
        up, failed = smt.upload_pending(root=self.tmp, url=self.url, token=TOKEN)
        self.assertEqual((up, failed), (1, 0))
        self.assertEqual(smt.pending(root=self.tmp), [])

    def test_no_token_stays_pending(self):
        dest = self._collected(tuid="tu_tok")
        os.environ.pop("VERUS_INGEST_TOKEN", None)
        self.assertFalse(smt.upload(dest, url=self.url, token=None))
        self.assertFalse(os.path.exists(os.path.join(dest, ".uploaded")))

    def test_dry_run_prints_no_post(self):
        dest = self._collected(tuid="tu_dry")
        os.environ["VERUS_INGEST_DRY_RUN"] = "1"
        try:
            self.assertTrue(smt.upload(dest, url=self.url, token=TOKEN))
        finally:
            del os.environ["VERUS_INGEST_DRY_RUN"]
        self.assertEqual(_Capture.posts, [])

    def test_prune_pending_scratch(self):
        pend = os.path.join(self.tmp, "pending")
        old_dir = os.path.join(pend, "20260101T000000Z.abc")
        new_dir = os.path.join(pend, "fresh")
        os.makedirs(old_dir)
        os.makedirs(new_dir)
        past = time.time() - 30 * 86400
        os.utime(old_dir, (past, past))
        smt.prune_pending_scratch(root=self.tmp)
        self.assertFalse(os.path.exists(old_dir))
        self.assertTrue(os.path.exists(new_dir))


class SmtHookTest(unittest.TestCase):
    """The PostToolUse hook script end to end (subprocess, stdin JSON)."""

    HOOK = os.path.join(HOOKS_DIR, "smt_capture.py")

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="smt-hook-test-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.env = dict(os.environ)
        self.env["VERUS_SMT_CAPTURE_ROOT"] = self.tmp
        # Background upload prints instead of POSTing.
        self.env["VERUS_INGEST_DRY_RUN"] = "1"

    def _run_hook(self, hook_input):
        return subprocess.run(
            [sys.executable, self.HOOK],
            input=json.dumps(hook_input),
            capture_output=True,
            text=True,
            env=self.env,
            timeout=30,
        )

    def _producer(self, files):
        d = tempfile.mkdtemp(prefix="prod-", dir=self.tmp)
        for name, content in files.items():
            with open(os.path.join(d, name), "w", encoding="utf-8") as fh:
                fh.write(content)
        return d

    def test_bash_marker_capture(self):
        prod = self._producer({"m.smt2": "q", "m.smt_transcript": "t"})
        r = self._run_hook({
            "session_id": "sess-hook",
            "tool_use_id": "toolu_ABC",
            "tool_name": "Bash",
            "tool_input": {"command": "./scripts/verus/verify.sh --output-json"},
            "tool_response": {
                "stdout": "{}",
                "stderr": "verus: verifying...\nverus-smt-log-dir: %s\n" % prod,
            },
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        dest = os.path.join(self.tmp, "sess-hook", "toolu_ABC")
        self.assertTrue(os.path.isdir(dest), r.stderr)
        self.assertEqual(smt.artifact_files(dest), ["m.smt2", "m.smt_transcript"])
        with open(os.path.join(dest, "meta.json")) as fh:
            meta = json.load(fh)
        self.assertEqual(meta["invocation"], "./scripts/verus/verify.sh --output-json")
        self.assertEqual(meta["tool_name"], "Bash")
        self.assertFalse(os.path.exists(prod))

    def test_mcp_structured_field_capture(self):
        prod = self._producer({"m.smt2": "q"})
        r = self._run_hook({
            "session_id": "sess-hook",
            "tool_use_id": "toolu_MCP",
            "tool_name": "mcp__verus__verify",
            "tool_input": {"path": "src/lib.rs"},
            "tool_response": {"content": [{"type": "text", "text": "..."}],
                              "structuredContent": {"success": True,
                                                    "smt_log_dir": prod}},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(os.path.isdir(os.path.join(self.tmp, "sess-hook", "toolu_MCP")))

    def test_mcp_json_string_response_capture(self):
        # The REAL wire shape (observed in a live session transcript): the
        # MCP result reaches PostToolUse serialized as JSON text inside a
        # content block, NOT as a structured dict.
        prod = self._producer({"m.smt2": "q"})
        payload = json.dumps({
            "duration_ms": 713, "errors": [],
            "raw_stdout_tail": "verification results:: 17 verified, 0 errors",
            "smt_log_dir": prod, "success": True,
            "summary": {"errors": 0, "verified": 17},
            "verus_version": "0.2026.08.23",
        })
        r = self._run_hook({
            "session_id": "sjson", "tool_use_id": "tj1",
            "tool_name": "mcp__verus__verify",
            "tool_input": {"path": "src/x.rs"},
            "tool_response": [{"type": "tool_result", "content": payload}],
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        dest = os.path.join(self.tmp, "sjson", "tj1")
        self.assertTrue(os.path.isdir(dest), r.stderr)
        with open(os.path.join(dest, "meta.json")) as fh:
            meta = json.load(fh)
        self.assertIs(meta["success"], True)
        self.assertEqual(meta["verified"], 17)

    def test_mcp_bare_string_response_capture(self):
        prod = self._producer({"m.smt2": "q"})
        payload = json.dumps({"success": False, "summary": {"verified": 1, "errors": 2},
                              "smt_log_dir": prod})
        r = self._run_hook({
            "session_id": "sjson", "tool_use_id": "tj2",
            "tool_name": "mcp__verus__verify",
            "tool_input": {"path": "src/x.rs"},
            "tool_response": payload,
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(os.path.isdir(os.path.join(self.tmp, "sjson", "tj2")), r.stderr)

    def test_mcp_truncated_json_regex_fallback(self):
        prod = self._producer({"m.smt2": "q"})
        # Valid JSON up to a cut: json.loads fails, the regex still finds it.
        text = '{"errors": [], "smt_log_dir": "%s", "raw_stdout_tail": "veri' % prod
        r = self._run_hook({
            "session_id": "sjson", "tool_use_id": "tj3",
            "tool_name": "mcp__verus__verify",
            "tool_input": {"path": "src/x.rs"},
            "tool_response": text,
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(os.path.isdir(os.path.join(self.tmp, "sjson", "tj3")), r.stderr)

    def test_non_verus_bash_is_ignored(self):
        r = self._run_hook({
            "session_id": "s", "tool_use_id": "t", "tool_name": "Bash",
            "tool_input": {"command": "ls"},
            "tool_response": {"stdout": "files", "stderr": ""},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0)
        self.assertEqual(
            [d for d in os.listdir(self.tmp) if not d.startswith("prod-")], []
        )

    def test_empty_producer_dir_skipped(self):
        prod = self._producer({})
        r = self._run_hook({
            "session_id": "s2", "tool_use_id": "t2", "tool_name": "Bash",
            "tool_input": {"command": "./scripts/verus/verify.sh"},
            "tool_response": {"stderr": "verus-smt-log-dir: %s\n" % prod},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "s2")))
        self.assertFalse(os.path.exists(prod))

    def test_disable_env(self):
        prod = self._producer({"m.smt2": "q"})
        env = dict(self.env)
        env["VERUS_SMT_LOG_DISABLE"] = "1"
        r = subprocess.run(
            [sys.executable, self.HOOK],
            input=json.dumps({
                "session_id": "s3", "tool_use_id": "t3", "tool_name": "Bash",
                "tool_input": {"command": "./scripts/verus/verify.sh"},
                "tool_response": {"stderr": "verus-smt-log-dir: %s\n" % prod},
                "cwd": HOOKS_DIR,
            }),
            capture_output=True, text=True, env=env, timeout=30,
        )
        self.assertEqual(r.returncode, 0)
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "s3")))
        self.assertTrue(os.path.exists(prod))  # untouched

    def test_bash_verdict_from_output_json(self):
        prod = self._producer({"m.smt2": "q"})
        stdout = json.dumps({
            "func-details": {},
            "verification-results": {
                "success": False, "verified": 2, "errors": 1,
                "encountered-error": True,
            },
        })
        r = self._run_hook({
            "session_id": "sv", "tool_use_id": "tv1", "tool_name": "Bash",
            "tool_input": {"command": "./scripts/verus/verify.sh --output-json"},
            "tool_response": {"stdout": stdout, "exitCode": 0,
                              "stderr": "verus-smt-log-dir: %s\n" % prod},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        with open(os.path.join(self.tmp, "sv", "tv1", "meta.json")) as fh:
            meta = json.load(fh)
        self.assertIs(meta["success"], False)
        self.assertEqual(meta["verified"], 2)
        self.assertEqual(meta["errors"], 1)
        self.assertEqual(meta["exit_code"], 0)  # 0 must survive extraction

    def test_mcp_verdict_from_structured_result(self):
        prod = self._producer({"m.smt2": "q"})
        r = self._run_hook({
            "session_id": "sv", "tool_use_id": "tv2",
            "tool_name": "mcp__verus__verify",
            "tool_input": {"path": "t.rs"},
            "tool_response": {"structuredContent": {
                "success": True, "summary": {"verified": 558, "errors": 0},
                "smt_log_dir": prod, "verus_version": "0.2026"}},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        with open(os.path.join(self.tmp, "sv", "tv2", "meta.json")) as fh:
            meta = json.load(fh)
        self.assertIs(meta["success"], True)
        self.assertEqual(meta["verified"], 558)
        self.assertEqual(meta["errors"], 0)

    def test_no_verdict_means_absent_not_failed(self):
        prod = self._producer({"m.smt2": "q"})
        r = self._run_hook({
            "session_id": "sv", "tool_use_id": "tv3", "tool_name": "Bash",
            "tool_input": {"command": "./scripts/verus/verify.sh"},
            "tool_response": {"stdout": "truncated garbage",
                              "stderr": "verus-smt-log-dir: %s\n" % prod},
            "cwd": HOOKS_DIR,
        })
        self.assertEqual(r.returncode, 0, r.stderr)
        with open(os.path.join(self.tmp, "sv", "tv3", "meta.json")) as fh:
            meta = json.load(fh)
        self.assertNotIn("success", meta)
        self.assertNotIn("verified", meta)

    def test_malformed_stdin_fails_soft(self):
        r = subprocess.run(
            [sys.executable, self.HOOK], input="not json",
            capture_output=True, text=True, env=self.env, timeout=30,
        )
        self.assertEqual(r.returncode, 0)


class AdapterToolUseIdTest(unittest.TestCase):
    """The Claude adapter must persist tool_use_id — the SMT-capture join key."""

    def test_transcript_tool_use_ids_survive(self):
        path = os.path.join(FIXTURES, "claude_transcript.jsonl")
        _turns, tool_calls, _meta = claude_adapter.parse_transcript(path)
        ids = [c.get("tool_use_id") for c in tool_calls]
        self.assertTrue(all(ids), "every tool_call carries its transcript id: %r" % ids)
        self.assertIn("tu_1", ids)


if __name__ == "__main__":
    unittest.main(verbosity=2)
