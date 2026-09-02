#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Tests for the SessionStart gate and the transport-resolving MCP probe.

Run: python3 .claude/hooks/tests/test_gate.py
"""

import io
import json
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock

HOOKS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, HOOKS)

import verus_gate  # noqa: E402
from verus_trace import mcp_probe  # noqa: E402


def write_config(root, entry):
    with open(os.path.join(root, ".mcp.json"), "w") as fh:
        json.dump({"mcpServers": {"verus": entry}}, fh)


class TransportResolutionTest(unittest.TestCase):
    """The gate must probe whatever `.mcp.json` actually selects, or it
    reports a healthy server while Claude talks to a different one."""

    def setUp(self):
        self.root = tempfile.mkdtemp(prefix="verus-gate-cfg-")
        patcher = mock.patch.object(mcp_probe, "repo_root", lambda: self.root)
        patcher.start()
        self.addCleanup(patcher.stop)
        # A clean environment: the config, not leftover env, decides.
        for var in ("VERUS_MCP_TRANSPORT", "VERUS_MCP_URL", "VERUS_MCP_COMMAND"):
            os.environ.pop(var, None)

    def test_stdio_config_selects_stdio_and_resolves_the_launcher(self):
        write_config(self.root, {"type": "stdio", "command": ".claude/bin/verus-mcp",
                                 "args": ["stdio"]})
        launcher = os.path.join(self.root, ".claude", "bin")
        os.makedirs(launcher)
        open(os.path.join(launcher, "verus-mcp"), "w").close()
        self.assertIsNone(mcp_probe._http_url())
        self.assertEqual(
            mcp_probe._server_command(),
            [os.path.join(self.root, ".claude/bin/verus-mcp"), "stdio"],
        )

    def test_relative_command_that_does_not_exist_is_left_alone(self):
        write_config(self.root, {"type": "stdio", "command": "verus-tools-mcp",
                                 "args": ["stdio"]})
        self.assertEqual(mcp_probe._server_command(), ["verus-tools-mcp", "stdio"])

    def test_stdio_command_without_args_still_gets_a_subcommand(self):
        write_config(self.root, {"type": "stdio", "command": "verus-tools-mcp"})
        self.assertEqual(mcp_probe._server_command(), ["verus-tools-mcp", "stdio"])

    def test_http_config_selects_its_url(self):
        write_config(self.root, {"type": "http", "url": "http://127.0.0.1:9999/mcp"})
        self.assertEqual(mcp_probe._http_url(), "http://127.0.0.1:9999/mcp")

    def test_env_overrides_beat_the_config(self):
        write_config(self.root, {"type": "http", "url": "http://127.0.0.1:9999/mcp"})
        with mock.patch.dict(os.environ, {"VERUS_MCP_TRANSPORT": "stdio"}):
            self.assertIsNone(mcp_probe._http_url())
        with mock.patch.dict(os.environ, {"VERUS_MCP_COMMAND": "my-server go"}):
            self.assertEqual(mcp_probe._server_command(), ["my-server", "go"])

    def test_missing_or_broken_config_falls_back_to_defaults(self):
        self.assertEqual(mcp_probe.active_mcp_config(), {})
        self.assertEqual(mcp_probe._http_url(), mcp_probe.DEFAULT_MCP_URL)
        with open(os.path.join(self.root, ".mcp.json"), "w") as fh:
            fh.write("{not json")
        self.assertEqual(mcp_probe.active_mcp_config(), {})
        self.assertEqual(mcp_probe._http_url(), mcp_probe.DEFAULT_MCP_URL)


class ToolchainGateTest(unittest.TestCase):
    """A reachable server whose Verus cannot run is blocked: every check /
    verify / profile call would fail, which is what the gate exists for."""

    HEALTHY = {
        "server_name": "verus-tools-mcp",
        "mcp_version": "0.1.0+gabc1234",
        "git_dirty": False,
        "workspace": None,  # filled per test
        "toolchain_ok": True,
    }

    def run_gate(self, version):
        result = mock.Mock(healthy=True, version=version, transport="stdio", error=None)
        buf = io.StringIO()
        with mock.patch.dict(os.environ, {"VERUS_GATE_DISABLE": ""}), \
                mock.patch.object(verus_gate, "_workspace_drift", lambda w: None), \
                mock.patch("verus_trace.mcp_probe.probe_version", return_value=result), \
                redirect_stdout(buf):
            code = verus_gate.main()
        out = buf.getvalue().strip()
        return code, (json.loads(out) if out else {})

    def test_broken_toolchain_blocks_with_the_servers_reason(self):
        version = dict(self.HEALTHY, toolchain_ok=False,
                       toolchain_error="the `verus` binary was not found")
        code, payload = self.run_gate(version)
        self.assertEqual(code, 2)
        self.assertEqual(payload["decision"], "block")
        self.assertIn("cannot run Verus", payload["reason"])
        self.assertIn("verus` binary was not found", payload["reason"])
        # The agent sees it too, not just the user.
        self.assertIn("cannot run Verus",
                      payload["hookSpecificOutput"]["additionalContext"])

    def test_healthy_toolchain_allows_silently(self):
        code, payload = self.run_gate(dict(self.HEALTHY))
        self.assertEqual(code, 0)
        self.assertEqual(payload, {})

    def test_missing_field_is_backwards_compatible(self):
        """Older server builds do not report toolchain_ok; they must not be
        blocked on a field they never send."""
        version = dict(self.HEALTHY)
        del version["toolchain_ok"]
        code, payload = self.run_gate(version)
        self.assertEqual(code, 0)
        self.assertEqual(payload, {})

    def test_unreachable_server_still_blocks(self):
        result = mock.Mock(healthy=False, version={}, transport="stdio",
                           error="connection refused")
        buf = io.StringIO()
        with mock.patch.dict(os.environ, {"VERUS_GATE_DISABLE": ""}), \
                mock.patch("verus_trace.mcp_probe.probe_version", return_value=result), \
                redirect_stdout(buf):
            code = verus_gate.main()
        payload = json.loads(buf.getvalue())
        self.assertEqual(code, 2)
        self.assertEqual(payload["decision"], "block")
        self.assertIn("connection refused", payload["reason"])


class WorkspaceDriftTest(unittest.TestCase):
    def test_drift_detected_and_suppressed_correctly(self):
        repo = os.path.realpath(os.path.join(HOOKS, "..", ".."))
        self.assertIsNone(verus_gate._workspace_drift(repo))
        self.assertIsNone(verus_gate._workspace_drift(None))
        drift = verus_gate._workspace_drift("/somewhere/else")
        self.assertIn("/somewhere/else", drift)
        self.assertIn("crate_name", drift)


if __name__ == "__main__":
    unittest.main()
