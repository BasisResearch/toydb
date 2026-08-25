# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Codex capture adapter. Parses a Codex rollout log
# (~/.codex/sessions/YYYY/MM/DD/rollout-<ts>-<uuid>.jsonl) into the shared
# session envelope.
#
# Rollout line kinds (per CONTRACTS.md / spec):
#   session_meta  : one; carries id, cwd, cli_version, git info
#   turn_context  : cwd/model per turn
#   event_msg     : task_started, user_message, agent_message, token_count, ...
#   response_item : message, reasoning, function_call, function_call_output,
#                   custom_tool_call, custom_tool_call_output, web_search_call
#
# Codex has no pre-run gate, so this adapter also inspects whether Verus MCP
# tools were actually available/used and sets gate_violation accordingly.

import json
import os

from . import envelope as env

# Codex surfaces MCP tools as function calls named "<server>__<tool>" or,
# for some transports, "<server>/<tool>". The committed config registers the
# server under [mcp_servers.verus], so Verus tools appear with a "verus"
# component.
_MCP_SERVER = "verus"


def _is_codex_mcp(name):
    if not name:
        return False
    lowered = name.lower()
    # Codex namespaces MCP tools; builtins are exec_command / apply_patch / etc.
    return (
        lowered.startswith(_MCP_SERVER + "__")
        or lowered.startswith(_MCP_SERVER + ".")
        or lowered.startswith(_MCP_SERVER + "/")
        or ("__" in name and name.split("__")[0].lower() == _MCP_SERVER)
    )


def _bare_name(name):
    for sep in ("__", "/", "."):
        if sep in name:
            return name.split(sep)[-1]
    return name


def parse_rollout(path):
    """Parse a Codex rollout into (turns, tool_calls, meta)."""
    entries = []
    with open(path, "r", encoding="utf-8") as fh:
        for raw in fh:
            raw = raw.strip()
            if not raw:
                continue
            try:
                entries.append(json.loads(raw))
            except json.JSONDecodeError:
                continue

    session_id = ""
    agent_version = ""
    cwd = ""
    started_at = None
    ended_at = None
    # Token totals: Codex reports cumulative usage on token_count events; the
    # last one carries the session total. Attach to a synthetic final turn.
    last_total_usage = None

    turns = []
    tool_calls = []
    pending_calls = {}
    turn_idx = 0
    any_mcp_available = False

    for entry in entries:
        etype = entry.get("type")
        ts = entry.get("timestamp")
        payload = entry.get("payload", {}) or {}
        if ts:
            if started_at is None:
                started_at = ts
            ended_at = ts

        if etype == "session_meta":
            session_id = payload.get("id", session_id) or session_id
            agent_version = payload.get("cli_version", agent_version) or agent_version
            cwd = payload.get("cwd", cwd) or cwd
            continue

        if etype == "turn_context":
            cwd = payload.get("cwd", cwd) or cwd
            continue

        if etype == "event_msg":
            ptype = payload.get("type")
            if ptype == "user_message":
                turns.append(
                    {
                        "idx": turn_idx,
                        "role": "user",
                        "text": payload.get("message", "") or "",
                        "tokens_in": 0,
                        "tokens_out": 0,
                        "cache_read": 0,
                        "ts": ts,
                    }
                )
                turn_idx += 1
            elif ptype == "agent_message":
                turns.append(
                    {
                        "idx": turn_idx,
                        "role": "assistant",
                        "text": payload.get("message", "") or "",
                        "tokens_in": 0,
                        "tokens_out": 0,
                        "cache_read": 0,
                        "ts": ts,
                    }
                )
                turn_idx += 1
            elif ptype == "token_count":
                info = payload.get("info")
                if isinstance(info, dict):
                    tot = info.get("total_token_usage")
                    if isinstance(tot, dict):
                        last_total_usage = tot
            continue

        if etype == "response_item":
            ptype = payload.get("type")
            if ptype in ("function_call", "custom_tool_call"):
                name = payload.get("name", "") or ""
                args = payload.get("arguments")
                if args is None:
                    args = payload.get("input")
                args = _maybe_json(args)
                is_mcp = _is_codex_mcp(name)
                if is_mcp:
                    any_mcp_available = True
                call = {
                    "turn_idx": max(turn_idx - 1, 0),
                    "name": _bare_name(name) if is_mcp else name,
                    "is_mcp": is_mcp,
                    "args": args if isinstance(args, dict) else {"raw": args},
                    "result": {},
                    "duration_ms": 0,
                    "ts": ts,
                }
                tool_calls.append(call)
                call_id = payload.get("call_id")
                if call_id:
                    pending_calls[call_id] = call
            elif ptype in ("function_call_output", "custom_tool_call_output"):
                call_id = payload.get("call_id")
                call = pending_calls.get(call_id)
                if call is not None:
                    call["result"] = _maybe_json(payload.get("output"))
            continue

    # Fold the cumulative token totals onto the last assistant turn (or a
    # synthetic one) so envelope totals reflect the session spend.
    if last_total_usage is not None:
        tin = int(last_total_usage.get("input_tokens") or 0)
        tout = int(last_total_usage.get("output_tokens") or 0)
        cread = int(last_total_usage.get("cached_input_tokens") or 0)
        target = None
        for t in reversed(turns):
            if t["role"] == "assistant":
                target = t
                break
        if target is None:
            target = {
                "idx": turn_idx,
                "role": "assistant",
                "text": "",
                "tokens_in": 0,
                "tokens_out": 0,
                "cache_read": 0,
                "ts": ended_at,
            }
            turns.append(target)
        target["tokens_in"] = tin
        target["tokens_out"] = tout
        target["cache_read"] = cread

    meta = {
        "session_id": session_id,
        "agent_version": agent_version,
        "cwd": cwd or os.getcwd(),
        "started_at": started_at or env.iso_now(),
        "ended_at": ended_at or env.iso_now(),
        "mcp_available": any_mcp_available,
    }
    return turns, tool_calls, meta


def _maybe_json(val):
    if isinstance(val, (dict, list)):
        return val
    if isinstance(val, str):
        try:
            return json.loads(val)
        except (json.JSONDecodeError, ValueError):
            return val
    return val


def build_from_rollout(
    rollout_path, mcp_version="", verus_version="", gate_violation=None
):
    turns, tool_calls, meta = parse_rollout(rollout_path)
    # Codex has no pre-run hard gate: if no Verus MCP tool was ever available,
    # mark the trace as a gate violation so the dashboard can exclude it.
    if gate_violation is None:
        gate_violation = not meta.get("mcp_available", False)
    return env.build_envelope(
        session_id=meta["session_id"],
        agent="codex",
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
