# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Tests for the branch-outcome mark path (verus_trace.branch_mark +
# mark_branch.py). No network: the POST is exercised via VERUS_INGEST_DRY_RUN
# and a stub HTTP server on localhost.
#
# Run:  python3 .claude/hooks/tests/test_branch_mark.py

import json
import os
import subprocess
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, HTTPServer

HOOKS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HOOKS_DIR)

from verus_trace import branch_mark as bm  # noqa: E402

CLI = os.path.join(HOOKS_DIR, "mark_branch.py")


def _git(repo, *args):
    subprocess.run(["git", "-C", repo] + list(args), check=True,
                   capture_output=True, text=True)


def _make_repo(branch="yl/doomed"):
    repo = tempfile.mkdtemp(prefix="verus-mark-")
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "tester@basis.ai")
    _git(repo, "config", "user.name", "Tester")
    with open(os.path.join(repo, "f.txt"), "w") as fh:
        fh.write("x\n")
    _git(repo, "add", "f.txt")
    _git(repo, "commit", "-q", "-m", "init")
    _git(repo, "checkout", "-q", "-b", branch)
    return repo


class _Capture(BaseHTTPRequestHandler):
    received = []
    status = 200

    def do_POST(self):
        n = int(self.headers.get("Content-Length", "0") or "0")
        body = json.loads(self.rfile.read(n).decode("utf-8"))
        _Capture.received.append(
            {"path": self.path, "auth": self.headers.get("Authorization"), "body": body}
        )
        out = json.dumps({"ok": _Capture.status == 200}).encode("utf-8")
        self.send_response(_Capture.status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(out)))
        self.end_headers()
        self.wfile.write(out)

    def log_message(self, *a):
        pass


class BranchMarkTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.repo = _make_repo()
        cls.server = HTTPServer(("127.0.0.1", 0), _Capture)
        cls.port = cls.server.server_address[1]
        threading.Thread(target=cls.server.serve_forever, daemon=True).start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()

    def setUp(self):
        _Capture.received = []
        _Capture.status = 200
        self.log = os.path.join(tempfile.mkdtemp(prefix="verus-marklog-"), "m.jsonl")
        self.env = dict(os.environ)
        for k in list(self.env):
            if k.startswith(("CODEX_", "OPENCODE", "VERUS_")) or k == "CLAUDECODE":
                self.env.pop(k)
        self.env.update({
            "VERUS_INGEST_URL": "http://127.0.0.1:%d/verus/ingest/session" % self.port,
            "VERUS_INGEST_TOKEN": "tok",
            "VERUS_MARK_LOG": self.log,
        })

    def _run(self, *args, env=None):
        return subprocess.run(
            [sys.executable, CLI] + list(args), cwd=self.repo,
            env=env or self.env, capture_output=True, text=True,
        )

    # -- unit --------------------------------------------------------------
    def test_mark_url_derived_from_ingest_url(self):
        os.environ["VERUS_INGEST_URL"] = "https://x/verus/ingest/session"
        os.environ.pop("VERUS_MARK_URL", None)
        try:
            self.assertEqual(bm.mark_url(), "https://x/verus/ingest/branch_mark")
        finally:
            os.environ.pop("VERUS_INGEST_URL")

    def test_detect_agent(self):
        self.assertEqual(bm.detect_agent({}), "human")
        self.assertEqual(bm.detect_agent({"CLAUDECODE": "1"}), "claude")
        self.assertEqual(bm.detect_agent({"OPENCODE_CONFIG": "x"}), "opencode")
        self.assertEqual(bm.detect_agent({"CODEX_SANDBOX": "x"}), "codex")
        self.assertEqual(bm.detect_agent({"VERUS_MARK_AGENT": "codex", "CLAUDECODE": "1"}), "codex")

    def test_build_mark_fields(self):
        m = bm.build_mark("Z3 timed out", category="Verus Timeout", cwd=self.repo, agent="claude")
        self.assertEqual(m["branch"], "yl/doomed")
        self.assertEqual(m["status"], "failed")
        self.assertEqual(m["category"], "verus-timeout")
        self.assertEqual(m["author_email"], "tester@basis.ai")
        self.assertEqual(m["agent"], "claude")
        self.assertEqual(len(m["commit_sha"]), 40)
        self.assertTrue(m["marked_at"])

    def test_build_mark_validation(self):
        with self.assertRaises(ValueError):
            bm.build_mark("", cwd=self.repo)  # reason required for failed
        with self.assertRaises(ValueError):
            bm.build_mark("x", branch="main", cwd=self.repo)  # never main
        m = bm.build_mark("", status="cleared", cwd=self.repo)  # reason optional
        self.assertEqual(m["status"], "cleared")

    # -- CLI ---------------------------------------------------------------
    def test_cli_failed_uploads_and_logs(self):
        r = self._run("failed", "--category", "missing-lemma", "--agent", "codex",
                      "could", "not", "prove", "the", "sort", "invariant")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("marked FAILED yl/doomed", r.stderr)
        self.assertEqual(len(_Capture.received), 1)
        rec = _Capture.received[0]
        self.assertEqual(rec["path"], "/verus/ingest/branch_mark")
        self.assertEqual(rec["auth"], "Bearer tok")
        self.assertEqual(rec["body"]["reason"], "could not prove the sort invariant")
        self.assertEqual(rec["body"]["category"], "missing-lemma")
        self.assertEqual(rec["body"]["agent"], "codex")
        with open(self.log) as fh:
            logged = [json.loads(l) for l in fh if l.strip()]
        self.assertEqual(len(logged), 1)
        self.assertTrue(logged[0]["uploaded"])

    def test_cli_clear(self):
        r = self._run("clear", "retrying", "with", "a", "smaller", "spec")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(_Capture.received[0]["body"]["status"], "cleared")

    def test_cli_upload_failure_exit_2_and_local_log(self):
        _Capture.status = 500
        r = self._run("failed", "-c", "other", "boom")
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertIn("UPLOAD FAILED", r.stderr)
        with open(self.log) as fh:
            logged = [json.loads(l) for l in fh if l.strip()]
        self.assertFalse(logged[0]["uploaded"])

    def test_cli_missing_token_exit_2(self):
        env = dict(self.env)
        env.pop("VERUS_INGEST_TOKEN")
        r = self._run("failed", "-c", "other", "boom", env=env)
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertIn("VERUS_INGEST_TOKEN", r.stderr)
        self.assertEqual(_Capture.received, [])

    def test_cli_dry_run_prints_payload(self):
        env = dict(self.env)
        env["VERUS_INGEST_DRY_RUN"] = "1"
        r = self._run("failed", "-c", "other", "boom", env=env)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads(r.stdout)["branch"], "yl/doomed")
        self.assertEqual(_Capture.received, [])

    def test_cli_usage_errors(self):
        r = self._run("failed", "-c", "other", "x", "--branch", "main")
        self.assertEqual(r.returncode, 1)
        r = self._run("categories")
        self.assertEqual(r.returncode, 0)
        self.assertIn("verus-timeout", r.stdout)


if __name__ == "__main__":
    unittest.main()
