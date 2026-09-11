# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code capture adapter. Parses a Claude Code transcript JSONL
# (~/.claude/projects/<slug>/<uuid>.jsonl) into the shared session envelope.
#
# The transcript carries, per line, a `message` object with:
#   * role "user" | "assistant"
#   * assistant messages: `usage` (input_tokens, output_tokens,
#     cache_read_input_tokens, ...) and content blocks including `tool_use`
#   * user messages: content blocks including `tool_result`
# We map each message to a turn and each tool_use to a tool_call, matching its
# result by tool_use_id.

import json
import os

from . import envelope as env


def _text_from_content(content):
    """Flatten a Claude content field (str or list of blocks) to text."""
    if isinstance(content, str):
        return content
    if not isinstance(content, list):
        return ""
    parts = []
    for block in content:
        if not isinstance(block, dict):
            continue
        btype = block.get("type")
        if btype == "text":
            parts.append(block.get("text", ""))
        elif btype == "thinking":
            parts.append(block.get("thinking", ""))
    return "\n".join(p for p in parts if p)


def parse_transcript(path):
    """Parse a Claude transcript file into (turns, tool_calls, meta).

    meta = {session_id, agent_version, cwd, started_at, ended_at}.
    Fails soft on malformed lines.
    """
    lines = []
    with open(path, "r", encoding="utf-8") as fh:
        for raw in fh:
            raw = raw.strip()
            if not raw:
                continue
            try:
                lines.append(json.loads(raw))
            except json.JSONDecodeError:
                continue

    session_id = ""
    agent_version = ""
    cwd = ""
    started_at = None
    ended_at = None

    turns = []
    tool_calls = []
    # Map tool_use_id -> tool_call dict so we can attach results later.
    pending_calls = {}
    turn_idx = 0

    for entry in lines:
        etype = entry.get("type")
        session_id = entry.get("sessionId", session_id) or session_id
        agent_version = entry.get("version", agent_version) or agent_version
        cwd = entry.get("cwd", cwd) or cwd
        ts = entry.get("timestamp")
        if ts:
            if started_at is None:
                started_at = ts
            ended_at = ts

        if etype not in ("user", "assistant"):
            continue
        message = entry.get("message")
        if not isinstance(message, dict):
            continue
        role = message.get("role", etype)
        content = message.get("content")
        usage = message.get("usage") or {}

        # Extract tool_use / tool_result blocks before deciding turn text.
        has_only_tool_result = False
        if isinstance(content, list):
            block_types = {b.get("type") for b in content if isinstance(b, dict)}
            has_only_tool_result = block_types == {"tool_result"}
            for block in content:
                if not isinstance(block, dict):
                    continue
                if block.get("type") == "tool_use":
                    name = block.get("name", "")
                    call = {
                        "turn_idx": turn_idx,
                        "name": name,
                        "is_mcp": env.is_mcp_tool(name),
                        "args": block.get("input", {}) or {},
                        "result": {},
                        "duration_ms": 0,
                        "ts": ts,
                    }
                    tool_calls.append(call)
                    tuid = block.get("id")
                    if tuid:
                        # The transcript's per-call id: the dashboard joins
                        # SMT captures (and any per-call artifact) on it.
                        call["tool_use_id"] = tuid
                        pending_calls[tuid] = call
                elif block.get("type") == "tool_result":
                    tuid = block.get("tool_use_id")
                    call = pending_calls.get(tuid)
                    if call is not None:
                        call["result"] = _tool_result_payload(block, entry)

        text = _text_from_content(content)

        # Skip pure tool_result carrier messages as turns (they are not user
        # prose), but always keep real user/assistant turns.
        if has_only_tool_result:
            continue

        tokens_in = int(usage.get("input_tokens") or 0)
        tokens_out = int(usage.get("output_tokens") or 0)
        cache_read = int(usage.get("cache_read_input_tokens") or 0)

        turns.append(
            {
                "idx": turn_idx,
                "role": role,
                "text": text,
                "tokens_in": tokens_in,
                "tokens_out": tokens_out,
                "cache_read": cache_read,
                "ts": ts,
            }
        )
        turn_idx += 1

    meta = {
        "session_id": session_id,
        "agent_version": agent_version,
        "cwd": cwd or os.getcwd(),
        "started_at": started_at or env.iso_now(),
        "ended_at": ended_at or env.iso_now(),
    }
    return turns, tool_calls, meta


def _tool_result_payload(block, entry):
    """Best-effort structured result for a tool_result block."""
    tur = entry.get("toolUseResult")
    if isinstance(tur, (dict, list)):
        return tur
    content = block.get("content")
    return {"content": content, "is_error": block.get("is_error", False)}


def build_from_transcript(
    transcript_path, mcp_version="", verus_version="", gate_violation=False
):
    turns, tool_calls, meta = parse_transcript(transcript_path)
    return env.build_envelope(
        session_id=meta["session_id"],
        agent="claude",
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
