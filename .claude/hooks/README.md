<!-- SPDX-License-Identifier: MIT -->
# Verus verification telemetry — trace capture & MCP gating (Component 2)

This directory (plus `.codex/`, `.opencode/`, `.mcp.json`, `opencode.json` at the
repo root) instruments toyDB so that **every agent session is captured** and
**no agent runs without the Verus MCP server connected**. A fresh clone is
instrumented with no extra setup for Claude Code and opencode; Codex needs the
project to be trusted once (`~/.codex/config.toml`: `projects."<path>".trust_level
= "trusted"`) plus a one-time `/hooks` trust review (or
`--dangerously-bypass-hook-trust`).

Source of truth for the schemas is `../../../spec.md` and `../../../CONTRACTS.md`
(in the research repo). The uploaded document is the session-trace envelope
(`POST /verus/ingest/session`).

## Layout

```
.claude/
  settings.json              committed hook wiring (PreToolUse guard,
                             SessionStart gate, Stop capture)
  bin/verus-mcp              self-provisioning pinned stdio launcher (prod/CI)
  hooks/
    branch_guard.py          PreToolUse (Bash): branch discipline — initials-
                             prefixed branch names, no commits/pushes to main
    verus_gate.py            SessionStart: fail-closed MCP probe + drift warning
    verus_stop.py            Stop: fail-soft transcript capture + upload
    mark_branch.py           CLI: mark a branch as a FAILED ATTEMPT (all agents)
    verus_trace/             shared, agent-agnostic Python package (stdlib only)
      envelope.py            build envelope, gather git fields, merge server
                             records, compute totals, POST (bearer auth)
      claude_adapter.py      Claude transcript JSONL -> envelope
      codex_adapter.py       Codex rollout JSONL -> envelope
      opencode_adapter.py    opencode SQLite session -> envelope
      mcp_probe.py           probe the Verus `version` tool over HTTP or stdio
      branch_mark.py         build + POST a branch outcome mark (failed/cleared)
    tests/                   fixtures + `test_adapters.py`, `test_branch_mark.py`
  skills/mark-failed/        Claude Code `/mark-failed` skill -> mark_branch.py
.codex/
  config.toml                project-scoped config (Codex >= 0.150 loads it for
                             trusted projects): [mcp_servers.verus] + Stop hook
  hooks/verus_stop.py        Codex Stop-hook entry point
.opencode/
  plugin/verus-telemetry.js  gate + capture via the generic `event` hook
                             (session.created / session.idle) + branch guard
                             via `tool.execute.before`
  plugin/verus_runner.py     Python entry the plugin shells out to
  command/mark-failed.md     opencode `/mark-failed` command -> mark_branch.py
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

## Branch discipline (branch_guard.py)

One shared guard, enforcing the workflow described in the repo-root
`CLAUDE.md` / `AGENTS.md` across all three agents: branch names must be
`<initials>/<topic>` (2-3 lowercase letters + `/`, e.g. `yl/fix-stop-hook`),
and `main` is never committed to or pushed directly. The dashboard keys the
`main` telemetry rollup on branch names (a branch's data folds into `main`
when its PR merges), so unique prefixes keep collaborators' data from
colliding.

The command-level check parses each shell command for `git
checkout/switch/branch` creations and renames, `git commit` while on `main`,
and `git push` destinations (including bare `git push` and `HEAD` refspecs,
which resolve to the current branch; `--delete` pushes are exempt so legacy
names can be cleaned up). Violations exit 2 with the reason on stderr, fed
back to the agent. FAIL-OPEN on unparseable input — the guard never bricks the
bash tool.

| Agent   | Enforcement                                                      |
|---------|------------------------------------------------------------------|
| Claude  | `PreToolUse` hook on Bash (`branch_guard.py`, default stdin mode) |
| opencode| plugin `tool.execute.before` shells to `branch_guard.py check`   |
| Codex   | no pre-tool event → git-hook backstop only                        |

The agent-agnostic backstop (covers Codex and humans): committed git hooks in
`.githooks/` (`pre-commit` blocks commits on `main` and warns on non-prefixed
branches; `pre-push` blocks pushes to `main` and of non-prefixed branch
names). They run via `branch_guard.py pre-commit` / `pre-push` and are
activated per clone by `git config core.hooksPath .githooks`, which
`ensure_hooks_path()` self-provisions fail-soft from each agent's session
hooks (Claude `SessionStart` gate, opencode gate, Codex Stop). It never
overrides a hooksPath the user set to something else.

## The two invariants

**Capture (fail-soft).** On session end each agent's adapter maps its native
transcript to the one shared envelope and POSTs it. A capture failure — no
token, network down, malformed transcript — is logged to stderr and swallowed;
it never breaks the user's agent session. The server-side MCP trace records
(`~/.verus-tools-mcp/trace/*.jsonl`, written by verus-tools-mcp) are merged into
the envelope's `tool_calls` by **tool name + timestamp-window overlap**, folding
verus/Z3 timing onto the matching call without a shared session id.

**SMT query capture (fail-soft).** Every Verus run also logs its full
diagnostics (`--log-all`: SMT-LIB queries, solver transcripts, AIR, VIR,
triggers, call graphs — not the huge Z3 trace profiles) and ships them to the
dashboard keyed to the exact tool call:

1. `scripts/verus/verify.sh` logs into a fresh dir under
   `~/.verus-trace/smt/pending/`, zstd's every artifact in place once Verus
   exits (`x` -> `x.zst`, ~25x smaller; the MCP server does the same) and
   prints `verus-smt-log-dir: <path>` on stderr (opt out:
   `VERUS_SMT_LOG_DISABLE=1`). The uploader decompresses transparently, so
   the wire format and the server are unchanged.
2. The `PostToolUse` hook (`smt_capture.py`, matcher `Bash|mcp__verus__verify`)
   finds that marker — or an `smt_log_dir` field in the MCP verify result — in
   `tool_response`, moves the dir to
   `~/.verus-trace/smt/<session_id>/<tool_use_id>/`, stamps `meta.json`
   (invocation, cwd, branch, commit), and spawns a **detached** background
   upload (`POST /verus/ingest/smt`, gzip'd, batched under the 32 MB ingest
   cap) so the agent loop never waits on the network.
3. The `Stop` hook retries anything still pending (`upload_pending()`); the
   server upserts by `(session_id, tool_use_id, filename)`, so retries and
   re-runs are idempotent. `tool_use_id` — now persisted on every envelope
   tool_call by the adapters — is the join key the dashboard uses to attach
   captures to transcript entries exactly (no timestamp heuristics).

The library lives in `verus_trace/smt_capture.py` and is shared by the
`verus-verify` CI workflow, which uploads the same capture per commit with
`source=ci` under a synthetic `ci:<run>` session. An empty log dir (cargo
considered the crate fresh, Verus never ran) is silently dropped; producer
dirs nothing collected are pruned after 7 days.

**Gating (fail-closed).** An agent must not run on toyDB unless the Verus MCP
server is connected. On any doubt — probe error, timeout, unhealthy server — the
session is denied, never allowed through.

| Agent   | Gate                                             | Capture                          |
|---------|--------------------------------------------------|----------------------------------|
| Claude  | `SessionStart` hook probes `version`; blocks if unreachable, warns (allows) if dirty | `Stop` hook reads `transcript_path` |
| opencode| plugin probes on `session.created`; warns loudly (opencode has no hook that can abort a session) | plugin captures on `session.idle` (per turn; ingest upserts by session_id) |
| Codex   | no pre-run event → best-effort: `gate_violation` marked on the trace | `Stop` hook reads the rollout log |

Codex is best-effort until it ships a session-start hook; the committed
`[mcp_servers.verus]` makes the server present by default, and the Stop hook sets
`gate_violation=true` when the Verus tools were not actually available, so an
ungated Codex run is *recorded and visible* on the dashboard (excluded from the
default comparison) rather than silently counted.

## Failed attempts (branch marks)

Not every branch succeeds. `mark_branch.py` records a branch as a **failed
attempt** on the dashboard (`POST /verus/ingest/branch_mark`) with a short,
deliberately loose reason and a category tag, so failures stay around and can
be filtered and analysed later to improve the tooling. It reuses
`verus_trace.envelope` for the git fields, so a mark joins the branch's
session telemetry on branch name. The dashboard then badges the branch,
offers an `outcome=ok|failed` filter, and lists marks on its **Failed
attempts** tab.

```sh
python3 .claude/hooks/mark_branch.py failed --category verus-timeout "Z3 blows up on the roundtrip lemma"
python3 .claude/hooks/mark_branch.py clear "retrying with a weaker spec"
python3 .claude/hooks/mark_branch.py categories
```

| Agent   | How it is triggered                                                |
|---------|--------------------------------------------------------------------|
| Claude  | `/mark-failed [tag] reason` skill (`.claude/skills/mark-failed/`) or CLAUDE.md instructions |
| opencode| `/mark-failed [tag] reason` command (`.opencode/command/`) or AGENTS.md |
| Codex   | AGENTS.md instructions -> runs the script directly                 |
| Humans  | run the script directly                                            |

Unlike session capture this is an explicit action, so it is **not**
fail-soft: exit 0 uploaded, 1 usage error, 2 upload failed (the mark is
still appended to `~/.verus-trace/branch_marks.jsonl`, override with
`VERUS_MARK_LOG`). The endpoint is derived from `VERUS_INGEST_URL` (or set
`VERUS_MARK_URL`); `VERUS_INGEST_DRY_RUN=1` prints instead of posting;
`VERUS_MARK_AGENT` overrides agent auto-detection. Marking `main` is
refused; marks never rename or delete the branch.

## Environment

- `VERUS_INGEST_TOKEN` — bearer token for `POST /verus/ingest/session` (required
  for a live upload). Held on contributor machines; keep it out of the repo.
- `VERUS_INGEST_URL` — override the endpoint (default
  `https://verus.basis.ai/verus/ingest/session`).
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
- `VERUS_SMT_LOG_DISABLE=1` — disable SMT query capture (both the verify.sh
  `--log-all` producer and the PostToolUse collector).
- `VERUS_SMT_LOG_ROOT` — where verify.sh creates producer log dirs (default
  `~/.verus-trace/smt/pending`; CI points it into the workspace).
- `VERUS_SMT_CAPTURE_ROOT` — keyed capture root (default `~/.verus-trace/smt`).
- `VERUS_SMT_INGEST_URL` — override the SMT ingest endpoint (default derived
  from `VERUS_INGEST_URL`: `.../ingest/session` -> `.../ingest/smt`).

## Codex one-time setup

Codex (>= 0.150) loads `.codex/config.toml` as a project config layer once the
project is trusted. Trust the clone once in `~/.codex/config.toml`:

    [projects."/path/to/toydb"]
    trust_level = "trusted"

then review the project hooks once via `/hooks` in the CLI (or launch with
`--dangerously-bypass-hook-trust`). The Stop-hook command resolves the repo
root via `git rev-parse`, so it works in any clone without editing the file.

## Tests

```sh
python3 .claude/hooks/tests/test_adapters.py
python3 .claude/hooks/tests/test_smt_capture.py
```

Runs each adapter against a checked-in fixture (Claude transcript, Codex rollout,
a synthesized opencode SQLite DB) and asserts the envelope conforms to the
CONTRACTS schema — keys, nesting, `is_mcp` flagging, `gate_violation`, totals —
and that the server-record merge folds `subprocess` detail (verus invocation, Z3
time) onto the matching call. No network: the POST path is covered via
`VERUS_INGEST_DRY_RUN`.
