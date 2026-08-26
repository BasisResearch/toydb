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
  bin/verus-mcp              self-provisioning pinned stdio launcher (prod/CI)
  hooks/
    verus_gate.py            SessionStart: fail-closed MCP probe + drift warning
    verus_stop.py            Stop: fail-soft transcript capture + upload
    verus_trace/             shared, agent-agnostic Python package (stdlib only)
      envelope.py            build envelope, gather git fields, merge server
                             records, compute totals, POST (bearer auth)
      claude_adapter.py      Claude transcript JSONL -> envelope
      codex_adapter.py       Codex rollout JSONL -> envelope
      opencode_adapter.py    opencode SQLite session -> envelope
      mcp_probe.py           probe the Verus `version` tool over HTTP or stdio
    tests/                   fixtures + `test_adapters.py`
.codex/
  config.toml                user-merge fragment: [mcp_servers.verus] + Stop hook
  hooks/verus_stop.py        Codex Stop-hook entry point
.opencode/
  plugin/verus-telemetry.js  session-start gate + session-end capture
  plugin/verus_runner.py     Python entry the plugin shells out to
.mcp.json                    Claude Code TEAM DEFAULT: dev hot-reload HTTP server
.mcp.prod.json               Claude Code PINNED: stdio launcher for box/CI/non-dev
opencode.json                opencode: registers the Verus MCP server (mcp block)
```

## MCP config: dev-default HTTP vs pinned stdio

There are two committed Claude Code MCP configs, for two audiences:

- **`.mcp.json` (team default) — dev hot-reload over HTTP.** Points Claude Code
  at `http://127.0.0.1:8765/mcp`. The team runs the server under `cargo watch`
  from the sibling `verus-tools-mcp` repo:

  ```sh
  cd ../verus-tools-mcp && ./scripts/dev-http.sh
  ```

  so edits to the server hot-reload without restarting Claude. This is the
  default because the point of the experiment is to iterate on the MCP tooling.

- **`.mcp.prod.json` (box / CI / non-dev) — pinned stdio launcher.** Not everyone
  hacks on the server; they need a reproducible install, not a running dev
  server. This registers verus as a **stdio** server whose command is
  `.claude/bin/verus-mcp`. That script is self-provisioning: it ensures a
  **pinned** build of `verus-tools-mcp` is installed (via
  `cargo install --git https://github.com/BasisResearch/verus-tools-mcp` into a
  per-ref cache under `~/.cache/verus-mcp/<ref>`), then `exec`s it over stdio.
  The pin is a single constant near the top of the script,
  `VERUS_MCP_REF` (default `main`; switch to a release tag to freeze). It is
  idempotent (skips install when the cached binary exists) and falls back to a
  `verus-tools-mcp` already on PATH.

  **To make it active** on the box / in CI, select it as the Claude Code MCP
  config — e.g. symlink or rename it over `.mcp.json`:

  ```sh
  ln -sf .mcp.prod.json .mcp.json      # or: cp .mcp.prod.json .mcp.json
  ```

## Drift: warn + tag, do not block

The gate probes the server's `version` tool, which returns the precise
`mcp_version` (e.g. `0.1.0+g1b40a7d.dirty`). A `.dirty` suffix (or `+unknown`),
or `git_dirty=true`, marks a **dev / non-release build**.

- **Unreachable / unhealthy server → BLOCK** (fail-closed). The block message
  tells the user to start the dev HTTP server (`./scripts/dev-http.sh`) or switch
  to the pinned `.mcp.prod.json`.
- **Healthy but dirty → ALLOW + WARN** (never block). The user is warned that the
  server is a dev build, that the session is **tagged** with that `mcp_version`,
  and that the dashboard will **exclude it from release comparisons**. Dev work
  is not disrupted.

The probe supports both transports transparently: it uses HTTP when
`VERUS_MCP_URL` is set (it defaults to the dev endpoint), and the pinned stdio
binary otherwise (`VERUS_MCP_URL=""` or `VERUS_MCP_TRANSPORT=stdio` forces
stdio).

## How mcp_version tags a session

Each Stop path (Claude `verus_stop.py`, Codex `verus_stop.py`, opencode
`verus_runner.py capture`) probes `version` and stamps the envelope's
`mcp_version` and `verus_version` from it, **preferring the precise
`mcp_version`** field over the coarse `server_version`. So a dev session uploads
`mcp_version="0.1.0+g<sha>.dirty"` and the dashboard buckets it separately from
released builds automatically — no dashboard change needed.

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
| Claude  | `SessionStart` hook probes `version`; blocks if unreachable, warns (allows) if dirty | `Stop` hook reads `transcript_path` |
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
  `https://verus.kirancodes.me/verus/ingest/session`).
- `VERUS_INGEST_DRY_RUN=1` — build and print the envelope, do not POST. Use for
  local testing without a token.
- `VERUS_MCP_LOG_DIR` — server-side trace dir (default
  `~/.verus-tools-mcp/trace`).
- `VERUS_MCP_URL` — HTTP endpoint the probe uses (default
  `http://127.0.0.1:8765/mcp`, the dev server). Set empty to force stdio.
- `VERUS_MCP_TRANSPORT=stdio` — force the stdio probe path regardless of URL.
- `VERUS_MCP_COMMAND` — override the stdio launch command (default
  `verus-tools-mcp stdio`); used by the pinned launcher and tests.
- `VERUS_MCP_REF` / `VERUS_MCP_CACHE_ROOT` — override the pinned launcher's git
  ref and per-ref cache location (`.claude/bin/verus-mcp`).
- `VERUS_GATE_DISABLE=1` — disable the gate (telemetry-development escape hatch;
  off by default so a fresh clone is gated).

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
