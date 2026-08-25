# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Verus MCP server probe, shared by the fail-closed gate hooks.
#
# Speaks just enough of the MCP stdio JSON-RPC protocol to launch the
# `verus-tools-mcp` server, initialize, and call its `version` tool. Returns a
# structured result the gate hooks translate into an allow/block decision.
#
# The check is FAIL-CLOSED: any error, timeout, missing binary, or malformed
# response is reported as "not healthy", never as an allow-on-doubt.
#
# The `version` tool output shape (per CONTRACTS.md) is:
#   { server_name, server_version, verus_version, rust_toolchain, protocol }

import json
import os
import shutil
import subprocess
import sys

PROBE_TIMEOUT_S = 20
PROTOCOL_VERSION = "2025-06-18"


def _server_command():
    """How the Verus MCP binary is launched.

    Mirrors the repo-committed .mcp.json: command `verus-tools-mcp` with the
    `stdio` transport arg. Overridable via VERUS_MCP_COMMAND for tests.
    """
    override = os.environ.get("VERUS_MCP_COMMAND")
    if override:
        return override.split()
    return ["verus-tools-mcp", "stdio"]


class ProbeResult(object):
    def __init__(self, healthy, version=None, error=None):
        self.healthy = healthy
        self.version = version or {}
        self.error = error

    def as_dict(self):
        return {"healthy": self.healthy, "version": self.version, "error": self.error}


def _rpc_line(obj):
    return (json.dumps(obj) + "\n").encode("utf-8")


def probe_version():
    """Launch the server over stdio, initialize, call `version`.

    Returns a ProbeResult. Fail-closed on every failure path.
    """
    cmd = _server_command()
    binary = cmd[0]

    if shutil.which(binary) is None and not os.path.exists(binary):
        return ProbeResult(
            False, error="verus-tools-mcp binary not found on PATH (%s)" % binary
        )

    try:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            bufsize=0,
        )
    except Exception as exc:
        return ProbeResult(False, error="failed to launch server: %s" % exc)

    init = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {},
            "clientInfo": {"name": "verus-gate-probe", "version": "0.1.0"},
        },
    }
    initialized = {"jsonrpc": "2.0", "method": "notifications/initialized"}
    call = {
        "jsonrpc": "2.0",
        "id": 2,
        "method": "tools/call",
        "params": {"name": "version", "arguments": {}},
    }

    payload = _rpc_line(init) + _rpc_line(initialized) + _rpc_line(call)

    try:
        out, _ = proc.communicate(input=payload, timeout=PROBE_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        proc.kill()
        try:
            proc.communicate(timeout=2)
        except Exception:
            pass
        return ProbeResult(False, error="probe timed out after %ss" % PROBE_TIMEOUT_S)
    except Exception as exc:
        try:
            proc.kill()
        except Exception:
            pass
        return ProbeResult(False, error="probe I/O error: %s" % exc)

    version = _extract_version(out)
    if version is None:
        return ProbeResult(
            False, error="no valid `version` tool result from server"
        )
    # Sanity: confirm it is actually the Verus server.
    if version.get("server_name") != "verus-tools-mcp":
        return ProbeResult(
            False,
            version=version,
            error="server identity mismatch (got %r)" % version.get("server_name"),
        )
    return ProbeResult(True, version=version)


def _extract_version(out):
    """Parse the stdout stream for the tools/call (id=2) result.

    Returns the parsed `version` tool structured content dict, or None.
    """
    if not out:
        return None
    text = out.decode("utf-8", "replace")
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("id") != 2:
            continue
        result = msg.get("result")
        if not isinstance(result, dict):
            return None
        # Prefer structuredContent; fall back to a JSON text content block.
        sc = result.get("structuredContent")
        if isinstance(sc, dict) and sc.get("server_name"):
            return sc
        for block in result.get("content", []) or []:
            if isinstance(block, dict) and block.get("type") == "text":
                try:
                    parsed = json.loads(block.get("text", ""))
                except (json.JSONDecodeError, TypeError):
                    continue
                if isinstance(parsed, dict) and parsed.get("server_name"):
                    return parsed
        return None
    return None


if __name__ == "__main__":
    res = probe_version()
    json.dump(res.as_dict(), sys.stdout)
    sys.stdout.write("\n")
    sys.exit(0 if res.healthy else 1)
