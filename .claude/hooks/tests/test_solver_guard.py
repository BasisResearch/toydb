#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Unit tests for solver_guard.py (PreToolUse manual-solver-run hook).

Run: python3 .claude/hooks/tests/test_solver_guard.py
"""

import io
import json
import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import solver_guard  # noqa: E402


class ViolationsTest(unittest.TestCase):
    def v(self, cmd):
        return solver_guard.violations(cmd)

    # -- direct invocations ------------------------------------------------
    def test_bare_solvers_blocked(self):
        for cmd in (
            "verus src/main.rs",
            "z3 -smt2 query.smt2",
            "cvc5 --stats query.smt2",
            "cvc4 query.smt2",
            "rust_verify foo.rs",
        ):
            self.assertTrue(self.v(cmd), cmd)

    def test_path_invocations_blocked(self):
        for cmd in (
            "./z3 query.smt2",
            "/usr/local/bin/cvc5 query.smt2",
            "~/verus-bin/verus lib.rs",
            "../verus/source/target-verus/release/verus x.rs",
        ):
            self.assertTrue(self.v(cmd), cmd)

    def test_cargo_verus_blocked(self):
        self.assertTrue(self.v("cargo verus verify --manifest-path Cargo.toml"))
        self.assertTrue(self.v("cargo-verus verify"))

    def test_wrapped_invocations_blocked(self):
        for cmd in (
            "env VERUS_Z3_PATH=/tmp/z3 verus x.rs",
            "RUST_LOG=debug z3 q.smt2",
            "timeout 30 z3 q.smt2",
            "timeout -k 5 30 cvc5 q.smt2",
            "nohup verus x.rs &",
            "time ./z3 q.smt2",
            "find . -name '*.smt2' | xargs z3",
        ):
            self.assertTrue(self.v(cmd), cmd)

    def test_compound_commands_blocked(self):
        self.assertTrue(self.v("echo hi && z3 q.smt2"))
        self.assertTrue(self.v("ls; verus x.rs | tee out.log"))

    # -- things that must stay allowed -------------------------------------
    def test_ordinary_commands_allowed(self):
        for cmd in (
            "cargo build",
            "cargo test",
            "ls -la",
            "git status",
            "cargo verify",  # not `cargo verus`
            "python3 scripts/z3_stats.py",  # z3 in an argument, not command
            "echo z3 is managed by the MCP server",
            "grep -rn cvc5 src/",
            "cat z3.log",
        ):
            self.assertFalse(self.v(cmd), cmd)

    def test_mcp_server_itself_allowed(self):
        self.assertFalse(self.v("verus-tools-mcp stdio"))
        self.assertFalse(self.v("curl -s http://127.0.0.1:8765/mcp"))

    def test_solver_named_data_files_allowed(self):
        self.assertFalse(self.v("shasum -a 256 ~/.verus-tools-mcp/solvers/basis-x/z3-arm64-macos"))

    def test_heredoc_mentions_allowed(self):
        cmd = 'gh pr create --repo BasisResearch/toydb --body "$(cat <<\'EOF\'\nrun z3 q.smt2 to reproduce\nEOF\n)"'
        self.assertFalse(self.v(cmd), cmd)


class HookModeTest(unittest.TestCase):
    def run_hook(self, payload):
        stdin = io.StringIO(json.dumps(payload))
        with mock.patch.object(sys, "stdin", stdin):
            return solver_guard.cmd_hook()

    def test_claude_shape_blocked(self):
        rc = self.run_hook({"tool_name": "Bash", "tool_input": {"command": "z3 q.smt2"}})
        self.assertEqual(rc, 2)

    def test_claude_shape_allowed(self):
        rc = self.run_hook({"tool_name": "Bash", "tool_input": {"command": "cargo test"}})
        self.assertEqual(rc, 0)

    def test_codex_argv_shape_blocked(self):
        rc = self.run_hook(
            {"tool_name": "shell", "tool_input": {"command": ["bash", "-lc", "cvc5 --stats q.smt2"]}}
        )
        self.assertEqual(rc, 2)

    def test_non_shell_tools_ignored(self):
        rc = self.run_hook({"tool_name": "Read", "tool_input": {"file_path": "/tmp/z3"}})
        self.assertEqual(rc, 0)

    def test_garbage_input_fails_open(self):
        stdin = io.StringIO("not json{")
        with mock.patch.object(sys, "stdin", stdin):
            self.assertEqual(solver_guard.cmd_hook(), 0)


class CheckModeTest(unittest.TestCase):
    def test_check_blocked(self):
        self.assertEqual(solver_guard.cmd_check(["--command", "verus x.rs"]), 2)

    def test_check_allowed(self):
        self.assertEqual(solver_guard.cmd_check(["--command", "cargo build"]), 0)


if __name__ == "__main__":
    unittest.main()
