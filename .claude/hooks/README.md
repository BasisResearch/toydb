<!-- SPDX-License-Identifier: MIT -->
# Verus verification telemetry — trace capture & MCP gating (Component 2)

This directory (plus `.codex/`, `.opencode/`, `.mcp.json`, `opencode.json` at the
repo root) instruments toyDB so that **every agent session is captured** and
**no agent runs without the Verus MCP server connected**. A fresh clone is
instrumented with no extra setup for Claude Code and opencode; Codex needs a
one-time user-level config merge (it has no per-repo config).

Source of truth for the schemas is `../../../spec.md` and `../../../CONTRACTS.md`
(in the research repo). The uploaded document is the session-trace envelope
(`POST /verus/ingest/session`).

## Layout

```
.claude/
  settings.json              committed hook wiring (SessionStart gate, Stop capture)
  hooks/
    verus_gate.py            SessionStart: fail-closed MCP probe (hard gate)
    verus_stop.py            Stop: fail-soft transcript capture + upload
    verus_trace/             shared, agent-agnostic Python package (stdlib only)
      envelope.py            build envelope, gather git fields, merge server
                             records, compute totals, POST (bearer auth)
      claude_adapter.py      Claude transcript JSONL -> envelope
      codex_adapter.py       Codex rollout JSONL -> envelope
      opencode_adapter.py    opencode SQLite session -> envelope
      mcp_probe.py           JSON-RPC probe of the Verus `version` tool
    tests/                   fixtures + `test_adapters.py`
.codex/
  config.toml                user-merge fragment: [mcp_servers.verus] + Stop hook
  hooks/verus_stop.py        Codex Stop-hook entry point
.opencode/
  plugin/verus-telemetry.js  session-start gate + session-end capture
  plugin/verus_runner.py     Python entry the plugin shells out to
.mcp.json                    Claude Code: registers the Verus MCP server
opencode.json                opencode: registers the Verus MCP server (mcp block)
```

## The two invariants

**Capture (fail-soft).** On session end each agent's adapter maps its native
transcript to the one shared envelope and POSTs it. A capture failure — no
token, network down, malformed transcript — is logged to stderr and swallowed;
it never breaks the user's agent session. The server-side MCP trace records
(`~/.verus-tools-mcp/trace/*.jsonl`, written by verus-tools-mcp) are merged into
the envelope's `tool_calls` by **tool name + timestamp-window overlap**, folding
verus/Z3 timing onto the matching call without a shared session id.

**Gating (fail-closed).** An agent must not run on toyDB unless the Verus MCP
server is connected. On any doubt — probe error, timeout, unhealthy server — the
session is denied, never allowed through.

| Agent   | Gate                                             | Capture                          |
|---------|--------------------------------------------------|----------------------------------|
| Claude  | `SessionStart` hook probes `version`; blocks     | `Stop` hook reads `transcript_path` |
| opencode| plugin probes at session start; aborts session   | plugin reads SQLite at session end |
| Codex   | no pre-run event → best-effort: `gate_violation` marked on the trace | `Stop` hook reads the rollout log |

Codex is best-effort until it ships a session-start hook; the committed
`[mcp_servers.verus]` makes the server present by default, and the Stop hook sets
`gate_violation=true` when the Verus tools were not actually available, so an
ungated Codex run is *recorded and visible* on the dashboard (excluded from the
default comparison) rather than silently counted.

## Environment

- `VERUS_INGEST_TOKEN` — bearer token for `POST /verus/ingest/session` (required
  for a live upload). Held on contributor machines; keep it out of the repo.
- `VERUS_INGEST_URL` — override the endpoint (default
  `https://dashboard.kirancodes.me/verus/ingest/session`).
- `VERUS_INGEST_DRY_RUN=1` — build and print the envelope, do not POST. Use for
  local testing without a token.
- `VERUS_MCP_LOG_DIR` — server-side trace dir (default
  `~/.verus-tools-mcp/trace`).

## Codex one-time setup

Codex reads only `~/.codex/config.toml`. Merge the blocks from
`.codex/config.toml` into it, replacing `/ABSOLUTE/PATH/TO/toydb` with your clone
path. Codex trust-reviews the hook command on first run.

## Tests

```sh
python3 .claude/hooks/tests/test_adapters.py
```

Runs each adapter against a checked-in fixture (Claude transcript, Codex rollout,
a synthesized opencode SQLite DB) and asserts the envelope conforms to the
CONTRACTS schema — keys, nesting, `is_mcp` flagging, `gate_violation`, totals —
and that the server-record merge folds `subprocess` detail (verus invocation, Z3
time) onto the matching call. No network: the POST path is covered via
`VERUS_INGEST_DRY_RUN`.
