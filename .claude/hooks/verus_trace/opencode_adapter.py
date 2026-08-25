# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# opencode capture adapter. Reads a session from the opencode SQLite store
# (~/.local/share/opencode/opencode.db) and maps it to the shared session
# envelope.
#
# Schema (observed on this machine):
#   session(id, directory, version, time_created, time_updated, tokens_input,
#           tokens_output, tokens_cache_read, ...)
#   message(id, session_id, time_created, data)   -- data is a JSON blob with
#           role, tokens{input,output,cache{read,write}}, time{...}
#   part(id, message_id, session_id, time_created, data) -- data JSON with
#           type text|tool|reasoning|..., and for tool: tool, callID, state{...}
#
# opencode namespaces MCP tools as "<server>_<tool>" (e.g. "verus_verify").

import json
import os
import sqlite3

from . import envelope as env

_MCP_SERVER = "verus"


def _default_db_path():
    return os.path.expanduser("~/.local/share/opencode/opencode.db")


def _is_oc_mcp(tool_name):
    if not tool_name:
        return False
    return tool_name.startswith(_MCP_SERVER + "_")


def _bare_name(tool_name):
    if tool_name.startswith(_MCP_SERVER + "_"):
        return tool_name[len(_MCP_SERVER) + 1:]
    return tool_name


def _connect(db_path):
    # Read-only, immutable so we never touch a live WAL.
    uri = "file:%s?mode=ro&immutable=1" % db_path
    return sqlite3.connect(uri, uri=True)


def parse_session(db_path, session_id):
    """Parse one opencode session into (turns, tool_calls, meta)."""
    conn = _connect(db_path)
    try:
        conn.row_factory = sqlite3.Row
        srow = conn.execute(
            "SELECT * FROM session WHERE id = ?", (session_id,)
        ).fetchone()
        if srow is None:
            raise ValueError("session %s not found" % session_id)
        skeys = srow.keys()
        directory = srow["directory"] if "directory" in skeys else os.getcwd()
        version = srow["version"] if "version" in skeys else ""

        messages = conn.execute(
            "SELECT id, time_created, data FROM message "
            "WHERE session_id = ? ORDER BY time_created ASC",
            (session_id,),
        ).fetchall()

        turns = []
        tool_calls = []
        turn_idx = 0
        started_ms = None
        ended_ms = None

        for mrow in messages:
            mid = mrow["id"]
            try:
                mdata = json.loads(mrow["data"])
            except (json.JSONDecodeError, TypeError):
                mdata = {}
            role = mdata.get("role", "assistant")
            tokens = mdata.get("tokens", {}) or {}
            cache = tokens.get("cache", {}) or {}
            m_created = mrow["time_created"]
            if started_ms is None:
                started_ms = m_created
            ended_ms = m_created

            # Gather parts for this message: text + tool calls.
            parts = conn.execute(
                "SELECT data, time_created FROM part "
                "WHERE message_id = ? ORDER BY time_created ASC",
                (mid,),
            ).fetchall()

            text_chunks = []
            for prow in parts:
                try:
                    pdata = json.loads(prow["data"])
                except (json.JSONDecodeError, TypeError):
                    continue
                ptype = pdata.get("type")
                if ptype == "text":
                    text_chunks.append(pdata.get("text", ""))
                elif ptype == "reasoning":
                    text_chunks.append(pdata.get("text", ""))
                elif ptype == "tool":
                    tool_calls.append(_tool_call_from_part(pdata, turn_idx))

            turns.append(
                {
                    "idx": turn_idx,
                    "role": role,
                    "text": "\n".join(c for c in text_chunks if c),
                    "tokens_in": int(tokens.get("input") or 0),
                    "tokens_out": int(tokens.get("output") or 0),
                    "cache_read": int(cache.get("read") or 0),
                    "ts": env.epoch_ms_to_iso(m_created),
                }
            )
            turn_idx += 1

        meta = {
            "session_id": session_id,
            "agent_version": version,
            "cwd": directory,
            "started_at": env.epoch_ms_to_iso(started_ms) or env.iso_now(),
            "ended_at": env.epoch_ms_to_iso(ended_ms) or env.iso_now(),
        }
        return turns, tool_calls, meta
    finally:
        conn.close()


def _tool_call_from_part(pdata, turn_idx):
    tool_name = pdata.get("tool", "")
    state = pdata.get("state", {}) or {}
    time = state.get("time", {}) or {}
    start = time.get("start")
    end = time.get("end")
    duration = 0
    if start is not None and end is not None:
        try:
            duration = int(end) - int(start)
        except (TypeError, ValueError):
            duration = 0
    is_mcp = _is_oc_mcp(tool_name)
    return {
        "turn_idx": turn_idx,
        "name": _bare_name(tool_name) if is_mcp else tool_name,
        "is_mcp": is_mcp,
        "args": state.get("input", {}) or {},
        "result": {"output": state.get("output"), "metadata": state.get("metadata")},
        "duration_ms": duration,
        "ts": env.epoch_ms_to_iso(start),
    }


def latest_session_id(db_path, directory=None):
    """Most recently updated session, optionally scoped to a directory."""
    conn = _connect(db_path)
    try:
        if directory:
            row = conn.execute(
                "SELECT id FROM session WHERE directory = ? "
                "ORDER BY time_updated DESC LIMIT 1",
                (directory,),
            ).fetchone()
            if row:
                return row[0]
        row = conn.execute(
            "SELECT id FROM session ORDER BY time_updated DESC LIMIT 1"
        ).fetchone()
        return row[0] if row else None
    finally:
        conn.close()


def build_from_db(
    session_id,
    db_path=None,
    mcp_version="",
    verus_version="",
    gate_violation=False,
):
    db_path = db_path or _default_db_path()
    turns, tool_calls, meta = parse_session(db_path, session_id)
    return env.build_envelope(
        session_id=meta["session_id"],
        agent="opencode",
        agent_version=meta["agent_version"],
        cwd=meta["cwd"],
        turns=turns,
        tool_calls=tool_calls,
        started_at=meta["started_at"],
        ended_at=meta["ended_at"],
        mcp_version=mcp_version,
        verus_version=verus_version,
        gate_violation=gate_violation,
    )
