# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Verus MCP server probe, shared by the gate and capture hooks.
#
# Speaks just enough of the MCP JSON-RPC protocol to initialize the
# `verus-tools-mcp` server and call its `version` tool. Supports BOTH transports:
#
#   * HTTP (default, the team dev-hot-reload server): streamable-HTTP at
#     $VERUS_MCP_URL (default http://127.0.0.1:8765/mcp), spoken with stdlib
#     urllib only (no dependencies).
#   * stdio (the pinned .mcp.prod.json launcher): spawn the binary and speak
#     line-delimited JSON-RPC over its stdin/stdout.
#
# Selection: if $VERUS_MCP_URL is set (or unset — it defaults to the dev
# endpoint) probe HTTP. Set $VERUS_MCP_URL="" (empty) or $VERUS_MCP_TRANSPORT=
# stdio to force the stdio path.
#
# The check is FAIL-CLOSED for gating: any error, timeout, missing binary,
# unreachable endpoint, or malformed response is reported as "not healthy",
# never as an allow-on-doubt. (The gate then applies its own warn-vs-block
# policy on a HEALTHY-but-dirty server; see verus_gate.py.)
#
# The `version` tool output shape (this is the CONTRACT the server guarantees):
#   { server_name, server_version, git_commit, git_dirty, mcp_version,
#     verus_version, rust_toolchain, protocol }
# `mcp_version` is the canonical precise id; a `.dirty` suffix (or `+unknown`)
# marks a dev / non-release build.

import json
import os
import shutil
import signal
import subprocess
import sys
import urllib.error
import urllib.request

PROBE_TIMEOUT_S = 20
PROTOCOL_VERSION = "2025-06-18"
DEFAULT_MCP_URL = "http://127.0.0.1:8765/mcp"


def repo_root():
    """The clone this probe belongs to (…/.claude/hooks/verus_trace/ -> root)."""
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.dirname(os.path.dirname(os.path.dirname(here)))


def active_mcp_config():
    """The `verus` server entry of the clone's active `.mcp.json`, or {}.

    The gate must probe what Claude Code actually connects to: whichever
    transport `.mcp.json` selects (stdio launcher by default, HTTP for the
    dev hot-reload server). Unreadable/absent config -> {} and the built-in
    defaults apply.
    """
    path = os.path.join(repo_root(), ".mcp.json")
    try:
        with open(path) as fh:
            data = json.load(fh)
    except Exception:
        return {}
    servers = data.get("mcpServers")
    if not isinstance(servers, dict):
        return {}
    entry = servers.get("verus")
    return entry if isinstance(entry, dict) else {}


def _server_command():
    """How the Verus MCP binary is launched over stdio.

    `VERUS_MCP_COMMAND` (space-separated) wins, then the active `.mcp.json`
    stdio entry (its command is resolved relative to the clone, as Claude
    Code resolves it), then the bare binary.
    """
    override = os.environ.get("VERUS_MCP_COMMAND")
    if override:
        return override.split()
    entry = active_mcp_config()
    command = entry.get("command")
    if isinstance(command, str) and command:
        args = entry.get("args") or []
        if not isinstance(args, list):
            args = []
        if not os.path.isabs(command):
            candidate = os.path.join(repo_root(), command)
            if os.path.exists(candidate):
                command = candidate
        cmd = [command] + [str(a) for a in args]
        return cmd if len(cmd) > 1 else cmd + ["stdio"]
    return ["verus-tools-mcp", "stdio"]


def _http_url():
    """The HTTP endpoint to probe, or None to use the stdio path.

    `VERUS_MCP_TRANSPORT=stdio` / an empty `VERUS_MCP_URL` force stdio and an
    explicit `VERUS_MCP_URL` forces HTTP; otherwise the active `.mcp.json`
    decides (a stdio entry -> stdio), falling back to the dev endpoint.
    """
    if str(os.environ.get("VERUS_MCP_TRANSPORT", "")).strip().lower() == "stdio":
        return None
    if "VERUS_MCP_URL" in os.environ:
        val = os.environ["VERUS_MCP_URL"].strip()
        return val or None
    entry = active_mcp_config()
    kind = str(entry.get("type") or "").strip().lower()
    if kind == "stdio" or (not kind and entry.get("command")):
        return None
    url = entry.get("url")
    if isinstance(url, str) and url.strip():
        return url.strip()
    return DEFAULT_MCP_URL


class ProbeResult(object):
    def __init__(self, healthy, version=None, error=None, transport=None):
        self.healthy = healthy
        self.version = version or {}
        self.error = error
        self.transport = transport

    def as_dict(self):
        return {
            "healthy": self.healthy,
            "version": self.version,
            "error": self.error,
            "transport": self.transport,
        }


def is_dirty_version(version):
    """True when the probed version denotes a dev / non-release build.

    Per the contract: git_dirty==true, or mcp_version containing `.dirty` or
    `+unknown`. Returns False for a clean released build (and defensively for a
    missing/empty version dict, since that path is handled as unhealthy first).
    """
    if not isinstance(version, dict):
        return False
    if version.get("git_dirty") is True:
        return True
    mv = str(version.get("mcp_version") or "")
    return (".dirty" in mv) or ("+unknown" in mv)


# ---------------------------------------------------------------------------
# Version-dict extraction (shared by both transports)
# ---------------------------------------------------------------------------

def _version_from_result(result):
    """Pull the `version` tool structured content dict out of a tools/call
    result object. Returns the dict or None."""
    if not isinstance(result, dict):
        return None
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


def _finalize(version, transport):
    """Turn a parsed version dict into a ProbeResult with identity check."""
    if version is None:
        return ProbeResult(
            False, error="no valid `version` tool result from server",
            transport=transport,
        )
    if version.get("server_name") != "verus-tools-mcp":
        return ProbeResult(
            False, version=version, transport=transport,
            error="server identity mismatch (got %r)" % version.get("server_name"),
        )
    return ProbeResult(True, version=version, transport=transport)


# ---------------------------------------------------------------------------
# HTTP (streamable-HTTP) transport
# ---------------------------------------------------------------------------

def _http_post(url, payload, session_id=None):
    """POST one JSON-RPC message to the streamable-HTTP endpoint.

    Returns (status, headers, parsed_message_or_None). Accepts either a JSON
    body or an SSE (text/event-stream) body and extracts the first JSON data
    frame. Raises on network error.
    """
    body = (json.dumps(payload) + "\n").encode("utf-8")
    headers = {
        "Content-Type": "application/json",
        # Streamable-HTTP servers may answer with SSE; accept both.
        "Accept": "application/json, text/event-stream",
    }
    if session_id:
        headers["Mcp-Session-Id"] = session_id
    req = urllib.request.Request(url, data=body, method="POST", headers=headers)
    with urllib.request.urlopen(req, timeout=PROBE_TIMEOUT_S) as resp:
        raw = resp.read().decode("utf-8", "replace")
        resp_headers = dict(resp.headers.items())
        status = resp.status
    msg = _parse_http_body(raw)
    return status, resp_headers, msg


def _parse_http_body(raw):
    """Parse a JSON or SSE response body into the first JSON-RPC message."""
    raw = (raw or "").strip()
    if not raw:
        return None
    # Plain JSON.
    if raw[0] in "{[":
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass
    # SSE frames: lines like `data: {...}`.
    for line in raw.splitlines():
        line = line.strip()
        if not line.lower().startswith("data:"):
            continue
        data = line[5:].strip()
        if not data or data == "[DONE]":
            continue
        try:
            return json.loads(data)
        except json.JSONDecodeError:
            continue
    return None


def probe_version_http(url):
    """MCP initialize + call `version` over streamable-HTTP. Fail-closed."""
    init = {
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {},
            "clientInfo": {"name": "verus-gate-probe", "version": "0.1.0"},
        },
    }
    try:
        _status, headers, _msg = _http_post(url, init)
    except urllib.error.URLError as exc:
        return ProbeResult(
            False, transport="http",
            error="HTTP endpoint unreachable (%s): %s" % (url, getattr(exc, "reason", exc)),
        )
    except Exception as exc:
        return ProbeResult(False, transport="http",
                           error="HTTP initialize failed (%s): %s" % (url, exc))

    # Carry the negotiated session id if the server issued one.
    session_id = headers.get("Mcp-Session-Id") or headers.get("mcp-session-id")

    # Best-effort: send the initialized notification (some servers require it
    # before tools/call). Ignore its (notification -> no) response.
    try:
        _http_post(url, {"jsonrpc": "2.0", "method": "notifications/initialized"},
                   session_id=session_id)
    except Exception:
        pass

    call = {
        "jsonrpc": "2.0", "id": 2, "method": "tools/call",
        "params": {"name": "version", "arguments": {}},
    }
    try:
        _status, _headers, msg = _http_post(url, call, session_id=session_id)
    except Exception as exc:
        return ProbeResult(False, transport="http",
                           error="HTTP `version` call failed (%s): %s" % (url, exc))

    if not isinstance(msg, dict):
        return ProbeResult(False, transport="http",
                           error="no JSON-RPC response to `version` from %s" % url)
    version = _version_from_result(msg.get("result"))
    return _finalize(version, "http")


# ---------------------------------------------------------------------------
# stdio transport
# ---------------------------------------------------------------------------

def _rpc_line(obj):
    return (json.dumps(obj) + "\n").encode("utf-8")


def _kill_group(proc):
    """Kill the probe's whole process group. `proc` may be a shell launcher
    that spawned the real server; killing only the direct child orphans the
    rest."""
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except Exception:
        try:
            proc.kill()
        except Exception:
            pass


def probe_version_stdio():
    """Launch the server over stdio, initialize, call `version`. Fail-closed."""
    cmd = _server_command()
    binary = cmd[0]

    if shutil.which(binary) is None and not os.path.exists(binary):
        return ProbeResult(
            False, transport="stdio",
            error="verus-tools-mcp binary not found on PATH (%s)" % binary,
        )

    try:
        env = dict(os.environ)
        # The probe has a PROBE_TIMEOUT_S budget; provisioning the server takes
        # minutes. Without this the launcher would start a `cargo install`
        # underneath us, the probe would time out, and the session would be
        # blocked with "probe timed out" instead of "not installed yet".
        env.setdefault("VERUS_MCP_NO_INSTALL", "1")
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            # Claude Code launches the server with the project as its cwd; the
            # server resolves its workspace from there, so the probe must too.
            cwd=repo_root(),
            env=env,
            # Own process group, so a timeout can take down the launcher AND
            # anything it started, not just the shell wrapper.
            start_new_session=True,
        )
    except Exception as exc:
        return ProbeResult(False, transport="stdio",
                           error="failed to launch server: %s" % exc)

    init = {
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {
            "protocolVersion": PROTOCOL_VERSION,
            "capabilities": {},
            "clientInfo": {"name": "verus-gate-probe", "version": "0.1.0"},
        },
    }
    initialized = {"jsonrpc": "2.0", "method": "notifications/initialized"}
    call = {
        "jsonrpc": "2.0", "id": 2, "method": "tools/call",
        "params": {"name": "version", "arguments": {}},
    }
    payload = _rpc_line(init) + _rpc_line(initialized) + _rpc_line(call)

    try:
        out, err = proc.communicate(input=payload, timeout=PROBE_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        _kill_group(proc)
        try:
            proc.communicate(timeout=2)
        except Exception:
            pass
        return ProbeResult(False, transport="stdio",
                           error="probe timed out after %ss" % PROBE_TIMEOUT_S)
    except Exception as exc:
        try:
            proc.kill()
        except Exception:
            pass
        return ProbeResult(False, transport="stdio",
                           error="probe I/O error: %s" % exc)

    version = _extract_version_stdio(out)
    if version is None:
        detail = (err or b"").decode("utf-8", "replace").strip()
        if detail:
            # The launcher explains itself on stderr ("not installed", "no
            # Verus toolchain found"). Without this the user only ever sees
            # the generic "no valid `version` tool result from server".
            return ProbeResult(
                False, transport="stdio",
                error="server did not answer `version`: %s"
                      % detail.splitlines()[-1][:300],
            )
    return _finalize(version, "stdio")


def _extract_version_stdio(out):
    """Parse the stdout stream for the tools/call (id=2) result. -> dict|None."""
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
        return _version_from_result(msg.get("result"))
    return None


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def probe_version():
    """Probe the Verus MCP server over the configured transport.

    HTTP (default, dev hot-reload) unless VERUS_MCP_URL is empty or
    VERUS_MCP_TRANSPORT=stdio selects the pinned stdio launcher. Returns a
    ProbeResult; fail-closed on every failure path.
    """
    url = _http_url()
    if url:
        return probe_version_http(url)
    return probe_version_stdio()


# Backwards-compat alias for callers that referenced the old name.
_extract_version = _extract_version_stdio


if __name__ == "__main__":
    res = probe_version()
    json.dump(res.as_dict(), sys.stdout)
    sys.stdout.write("\n")
    sys.exit(0 if res.healthy else 1)
