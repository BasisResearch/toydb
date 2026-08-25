# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Shared session-trace envelope helper for the Verus verification-telemetry
# system (Component 2). Stdlib only: no pip dependencies.
#
# Responsibilities:
#   * Build the session envelope exactly as specified in CONTRACTS.md
#     (POST /verus/ingest/session).
#   * Gather common fields (author_email, machine, repo, branch, commit_sha,
#     rust_toolchain) at session start via git and the rust-toolchain file.
#   * Merge server-side MCP trace records from ~/.verus-tools-mcp/trace/*.jsonl
#     into the envelope's tool_calls by tool-name + timestamp-window overlap.
#   * Compute totals.
#   * POST the envelope with a bearer token, failing soft (never raising into
#     the caller's agent session; errors go to stderr).
#
# Every adapter (Claude Code, Codex, opencode) imports this module and hands it
# a normalized list of turns and tool_calls; this module owns everything that is
# identical across agents.

import datetime
import glob
import json
import os
import subprocess
import sys
import urllib.error
import urllib.request

# ---------------------------------------------------------------------------
# Constants / configuration
# ---------------------------------------------------------------------------

REPO_SLUG = "BasisResearch/toydb"
DEFAULT_INGEST_URL = "https://dashboard.kirancodes.me/verus/ingest/session"

# Env flags:
#   VERUS_INGEST_URL      override the ingest endpoint
#   VERUS_INGEST_TOKEN    bearer token (required for a live POST)
#   VERUS_INGEST_DRY_RUN  when truthy, do not POST; print the envelope to stdout
#   VERUS_MCP_LOG_DIR     server-side trace dir (default ~/.verus-tools-mcp/trace)


def _log(msg):
    """Diagnostics go to stderr only, never stdout (stdout is hook protocol)."""
    sys.stderr.write("[verus-trace] %s\n" % msg)


def _truthy(val):
    return str(val).strip().lower() in ("1", "true", "yes", "on")


def is_dry_run():
    return _truthy(os.environ.get("VERUS_INGEST_DRY_RUN", ""))


# ---------------------------------------------------------------------------
# Common field gathering (git + rust-toolchain)
# ---------------------------------------------------------------------------

def _git(args, cwd):
    try:
        out = subprocess.run(
            ["git"] + args,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=10,
        )
        if out.returncode == 0:
            return out.stdout.strip()
    except Exception as exc:  # pragma: no cover - defensive
        _log("git %s failed: %s" % (" ".join(args), exc))
    return ""


def author_email(cwd):
    return _git(["config", "user.email"], cwd) or ""


def machine():
    try:
        import socket

        return socket.gethostname()
    except Exception:
        return os.environ.get("HOSTNAME", "unknown")


def branch(cwd):
    b = _git(["rev-parse", "--abbrev-ref", "HEAD"], cwd)
    return b or ""


def commit_sha(cwd):
    return _git(["rev-parse", "HEAD"], cwd) or ""


def rust_toolchain(cwd):
    """Read the pinned Rust toolchain from the repo's rust-toolchain file.

    toyDB pins a bare `rust-toolchain` file (plain version string). Also handle
    a rust-toolchain.toml `channel = "..."` form defensively.
    """
    for name in ("rust-toolchain", "rust-toolchain.toml"):
        path = os.path.join(cwd, name)
        try:
            with open(path, "r", encoding="utf-8") as fh:
                text = fh.read().strip()
        except OSError:
            continue
        if not text:
            continue
        if name.endswith(".toml") or "channel" in text:
            for line in text.splitlines():
                line = line.strip()
                if line.startswith("channel"):
                    _, _, val = line.partition("=")
                    return val.strip().strip('"').strip("'")
        else:
            # bare file: first non-empty token
            return text.splitlines()[0].strip()
    return ""


def repo_root(start):
    """Best-effort repo root via git; falls back to the given dir."""
    root = _git(["rev-parse", "--show-toplevel"], start)
    return root or start


# ---------------------------------------------------------------------------
# Timestamp helpers
# ---------------------------------------------------------------------------

def _parse_iso(ts):
    """Parse an ISO-8601 timestamp to an aware UTC datetime, or None."""
    if not ts:
        return None
    if isinstance(ts, (int, float)):
        # epoch millis or seconds
        secs = ts / 1000.0 if ts > 1e12 else float(ts)
        return datetime.datetime.fromtimestamp(secs, tz=datetime.timezone.utc)
    s = str(ts).strip()
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        dt = datetime.datetime.fromisoformat(s)
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=datetime.timezone.utc)
    return dt.astimezone(datetime.timezone.utc)


def iso_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def epoch_ms_to_iso(ms):
    if ms is None:
        return None
    try:
        return datetime.datetime.fromtimestamp(
            float(ms) / 1000.0, tz=datetime.timezone.utc
        ).isoformat()
    except (TypeError, ValueError):
        return None


# ---------------------------------------------------------------------------
# Server-side MCP trace merge
# ---------------------------------------------------------------------------

def _trace_dir():
    d = os.environ.get("VERUS_MCP_LOG_DIR")
    if d:
        return os.path.expanduser(d)
    return os.path.expanduser("~/.verus-tools-mcp/trace")


def load_server_records(session_start, session_end, trace_dir=None):
    """Load server-side trace records whose window overlaps the session.

    Records are JSONL objects per CONTRACTS.md. Returns a list of dicts, each
    annotated with parsed `_started` / `_ended` datetimes. Fails soft: a
    missing directory or unreadable file yields fewer records, never an error.
    """
    trace_dir = trace_dir or _trace_dir()
    start_dt = _parse_iso(session_start)
    end_dt = _parse_iso(session_end)
    records = []
    try:
        paths = sorted(glob.glob(os.path.join(trace_dir, "*.jsonl")))
    except Exception as exc:  # pragma: no cover - defensive
        _log("cannot list trace dir %s: %s" % (trace_dir, exc))
        return records
    for path in paths:
        try:
            with open(path, "r", encoding="utf-8") as fh:
                for line in fh:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rec = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    r_start = _parse_iso(rec.get("started_at"))
                    r_end = _parse_iso(rec.get("ended_at")) or r_start
                    # Overlap test against session window when both bounds known.
                    if start_dt and r_end and r_end < start_dt:
                        continue
                    if end_dt and r_start and r_start > end_dt:
                        continue
                    rec["_started"] = r_start
                    rec["_ended"] = r_end
                    records.append(rec)
        except OSError as exc:
            _log("cannot read trace file %s: %s" % (path, exc))
    return records


def merge_server_records(tool_calls, server_records):
    """Fold server-side records into agent-side tool_calls.

    Match on tool name + timestamp-window: for each agent-side MCP tool_call,
    pick the unused server record with the same (normalized) tool name whose
    window contains, or is closest to, the agent-side ts. On a match, attach the
    server record's `subprocess` detail and richer inputs/outputs, and prefer
    the server-measured `wall_ms` as duration.

    Mutates and returns `tool_calls`. Fails soft.
    """
    if not server_records:
        return tool_calls
    used = set()
    for call in tool_calls:
        name = _bare_tool_name(call.get("name", ""))
        call_ts = _parse_iso(call.get("ts"))
        best_idx = None
        best_score = None
        for idx, rec in enumerate(server_records):
            if idx in used:
                continue
            if _bare_tool_name(rec.get("tool", "")) != name:
                continue
            r_start = rec.get("_started")
            r_end = rec.get("_ended")
            score = _window_score(call_ts, r_start, r_end)
            if best_score is None or score < best_score:
                best_score = score
                best_idx = idx
        if best_idx is None:
            continue
        used.add(best_idx)
        rec = server_records[best_idx]
        call["server_call_id"] = rec.get("call_id")
        call["connection_id"] = rec.get("connection_id")
        if rec.get("subprocess") is not None:
            call["subprocess"] = rec.get("subprocess")
        # Server has authoritative inputs/outputs and timing.
        if rec.get("inputs") and not call.get("args"):
            call["args"] = rec.get("inputs")
        if rec.get("outputs") is not None:
            call["result"] = rec.get("outputs")
        if rec.get("wall_ms") is not None:
            call["duration_ms"] = rec.get("wall_ms")
        call["is_mcp"] = True
    return tool_calls


def _window_score(call_ts, r_start, r_end):
    """Lower is better. 0 when call_ts falls inside [r_start, r_end]."""
    if call_ts is None or r_start is None:
        return float("inf")
    end = r_end or r_start
    if r_start <= call_ts <= end:
        return 0.0
    if call_ts < r_start:
        return (r_start - call_ts).total_seconds()
    return (call_ts - end).total_seconds()


# ---------------------------------------------------------------------------
# MCP detection
# ---------------------------------------------------------------------------

def _bare_tool_name(name):
    """Strip agent-specific MCP prefixes to a bare tool name.

    Claude Code:  mcp__verus__verify  -> verify
    opencode:     verus_verify        -> verify   (server_tool)
    Codex/plain:  verify              -> verify
    """
    if not name:
        return ""
    if name.startswith("mcp__"):
        parts = name.split("__")
        return parts[-1] if parts else name
    return name


def is_mcp_tool(name, mcp_server_names=("verus",)):
    """Heuristic: does this tool name denote an MCP (specifically Verus) call?"""
    if not name:
        return False
    if name.startswith("mcp__"):
        return True
    for srv in mcp_server_names:
        if name.startswith(srv + "_") or name.startswith(srv + "__"):
            return True
    return False


# ---------------------------------------------------------------------------
# Envelope construction
# ---------------------------------------------------------------------------

def build_envelope(
    session_id,
    agent,
    agent_version,
    cwd,
    turns,
    tool_calls,
    started_at,
    ended_at,
    mcp_version="",
    verus_version="",
    gate_violation=False,
    merge_server=True,
):
    """Build the full session envelope per CONTRACTS.md.

    `turns` and `tool_calls` are agent-normalized lists; this function fills in
    the common fields, merges server-side records, and computes totals.
    """
    cwd = os.path.abspath(cwd or os.getcwd())
    root = repo_root(cwd)

    if merge_server:
        try:
            records = load_server_records(started_at, ended_at)
            merge_server_records(tool_calls, records)
        except Exception as exc:  # pragma: no cover - defensive
            _log("server record merge failed: %s" % exc)

    totals = compute_totals(turns, tool_calls)

    envelope = {
        "session_id": session_id,
        "agent": agent,
        "agent_version": agent_version or "",
        "author_email": author_email(root),
        "machine": machine(),
        "repo": REPO_SLUG,
        "branch": branch(root),
        "commit_sha": commit_sha(root),
        "mcp_version": mcp_version or "",
        "verus_version": verus_version or "",
        "rust_toolchain": rust_toolchain(root),
        "gate_violation": bool(gate_violation),
        "started_at": started_at,
        "ended_at": ended_at,
        "totals": totals,
        "turns": turns,
        "tool_calls": tool_calls,
    }
    return envelope


def compute_totals(turns, tool_calls):
    tokens_in = 0
    tokens_out = 0
    cache_read = 0
    for t in turns:
        tokens_in += int(t.get("tokens_in") or 0)
        tokens_out += int(t.get("tokens_out") or 0)
        cache_read += int(t.get("cache_read") or 0)
    mcp_calls = sum(1 for c in tool_calls if c.get("is_mcp"))
    return {
        "tokens_in": tokens_in,
        "tokens_out": tokens_out,
        "cache_read": cache_read,
        "tool_calls": len(tool_calls),
        "mcp_tool_calls": mcp_calls,
        "turns": len(turns),
    }


# ---------------------------------------------------------------------------
# Upload
# ---------------------------------------------------------------------------

def post_envelope(envelope, url=None, token=None):
    """POST the envelope to the ingest endpoint with bearer auth.

    Fails soft: on dry-run prints the envelope and returns True; on any network
    error logs to stderr and returns False. Never raises.
    """
    url = url or os.environ.get("VERUS_INGEST_URL") or DEFAULT_INGEST_URL
    token = token or os.environ.get("VERUS_INGEST_TOKEN")

    if is_dry_run():
        sys.stdout.write(json.dumps(envelope, indent=2, default=str))
        sys.stdout.write("\n")
        _log("dry run: %d turns, %d tool_calls (not posted)"
             % (len(envelope.get("turns", [])), len(envelope.get("tool_calls", []))))
        return True

    if not token:
        _log("no VERUS_INGEST_TOKEN set; skipping upload (fail soft)")
        return False

    try:
        body = json.dumps(envelope, default=str).encode("utf-8")
        req = urllib.request.Request(
            url,
            data=body,
            method="POST",
            headers={
                "Content-Type": "application/json",
                "Authorization": "Bearer " + token,
            },
        )
        with urllib.request.urlopen(req, timeout=30) as resp:
            _log("uploaded session %s -> HTTP %s"
                 % (envelope.get("session_id"), resp.status))
        return True
    except urllib.error.HTTPError as exc:
        _log("ingest HTTP error %s: %s" % (exc.code, exc.reason))
    except Exception as exc:
        _log("ingest failed: %s" % exc)
    return False


def build_and_post(**kwargs):
    """Convenience: build the envelope then post it. Returns the envelope."""
    url = kwargs.pop("url", None)
    token = kwargs.pop("token", None)
    envelope = build_envelope(**kwargs)
    post_envelope(envelope, url=url, token=token)
    return envelope
