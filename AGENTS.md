# toyDB (Basis) — repo rules for all agents

## Branch & PR discipline (MANDATORY, mechanically enforced)

- **Never commit to or push `main`.** All changes land through a feature
  branch and a PR to `main`.
- **Every branch you create MUST be named `<initials>/<topic>`** — the
  author's unique 2-3 lowercase-letter initials, a slash, then a short topic.
  Yiyun's prefix is `yl/` (e.g. `yl/fix-stop-hook`); each collaborator uses
  their own prefix. Initials must be unique across collaborators so branch
  names never collide.
- Why it matters beyond tidiness: the Verus CI dashboard associates agent
  session telemetry with **branch names**, and folds a branch's data into the
  `main` view once its PR merges. Colliding or reused branch names would
  attribute one person's sessions to another's work.

## Creating the PR (this repo is a fork)

`BasisResearch/toydb` is a **fork** of upstream toyDB, so `gh pr create`
defaults its base to the *parent* repo and a bare `gh pr create --base main`
fails (`No commits between main and <branch>` / `Head sha can't be blank`).
Always target this repo explicitly:

```
gh pr create --repo BasisResearch/toydb --base main --title "..." --body "..."
```

Enforcement (`.claude/hooks/branch_guard.py`, one shared guard):

- **Claude Code**: `PreToolUse` hook on Bash blocks violating git commands and
  a `gh pr create` that omits `--repo`.
- **opencode**: the `verus-telemetry` plugin's `tool.execute.before` handler
  blocks the same commands.
- **Codex / everyone**: committed git hooks (`.githooks/pre-commit`,
  `.githooks/pre-push`) block commits on `main` and pushes of `main` or
  non-prefixed branches. They are activated per clone via
  `git config core.hooksPath .githooks`, which the telemetry session hooks
  self-provision (or run it once yourself).

If blocked, rename the branch (`git branch -m <initials>/<topic>`) and retry —
do not try to bypass the hooks.

## Verus runs go through the MCP server (MANDATORY)

- **Never run `verus`, `cargo verus` / `cargo-verus`, or
  `scripts/verus/verify.sh` from the shell.** Use the `verus` MCP tools:
  - `check` — cargo-verus verification of this crate. `modules` =
    `["sql::parser::lexer", "src/raft/log.rs"]` verifies several modules in
    one run (or `module` for one); omit both for the full crate. Verus flags
    (`--rlimit 60`, `--triggers-mode silent`, `--multiple-errors 20`,
    `--verify-function f`) go in `extra_args`, cargo flags in `cargo_args`;
    `--lib` is added automatically. `raw=true` returns the unparsed output.
    `crate_name` is usually unnecessary: the default `.mcp.json` starts one
    server per session pinned to this checkout. Pass it (an absolute path)
    only when `version` reports a different `workspace`.
  - Full-crate or otherwise long runs: `check` with `background=true`, then
    `check_result(job_id)` — it waits up to 50 s per call and returns the
    full result when done; `check_cancel(job_id)` kills one you no longer
    need. `max_errors` (default 20) caps how many diagnostics come back.
  - `profile` — per-function SMT time / rlimit breakdown.
  - `verify` — bare `verus` on a standalone file (scratch models; no cargo
    deps). It cannot verify this crate and says so.
  - `version` — versions plus `workspace` and `toolchain_ok`. Call it first
    if a run fails oddly: `toolchain_ok: false` means the server cannot run
    Verus at all.
- Why: every MCP call is traced to the Verus dashboard together with its
  SMT logs; a shell run is invisible to the experiment. `check` also
  invalidates cargo's fingerprint, so it never replays a stale result the way
  a plain `cargo verus` does.
- Enforcement (`.claude/hooks/verus_cli_guard.py`, one shared guard):
  Claude Code `PreToolUse` hook on Bash; opencode plugin
  `tool.execute.before`. Codex has no pre-tool event, so it follows this rule
  by reading it. `--help`, `--version` and `command -v verus` stay allowed.
  Humans debugging the toolchain can set `VERUS_CLI_GUARD_DISABLE=1`.

## Marking a branch as a failed attempt

Some branches are experiments that do not work out. When the user says an
attempt/branch/approach **failed**, should be **abandoned / given up on**, or
asks to **record why it did not work**, mark the branch on the Verus
dashboard so the failure is kept, filterable, and analysable later (what went
wrong; what tooling change would have prevented it):

```
python3 .claude/hooks/mark_branch.py failed --category <tag> --agent <claude|codex|opencode> "<short reason>"
```

- `<short reason>`: 1–3 sentences. It does **not** need to be precise or
  complete — state the symptom (what Verus/the tool said) and your best guess
  at the cause. Something loose beats nothing.
- `<tag>`: one of `python3 .claude/hooks/mark_branch.py categories`
  (`verus-timeout`, `spec-too-strong`, `spec-wrong`, `missing-lemma`,
  `verus-unsupported`, `tooling-bug`, `scope-too-big`, `agent-stuck`,
  `abandoned`, `other`); free-form is accepted if none fits.
- Shortcuts: Claude Code `/mark-failed [tag] reason`, opencode
  `/mark-failed [tag] reason`. Codex and humans run the script directly.
- Exit code 2 means the upload failed (no `VERUS_INGEST_TOKEN`, network); the
  mark is appended to `~/.verus-trace/branch_marks.jsonl` — tell the user.
- To undo: `python3 .claude/hooks/mark_branch.py clear "<why>"`.
- Never rename, delete or force-push the branch to "mark" it, and do not
  commit anything as part of marking: the dashboard joins telemetry on the
  branch name and the mark is recorded server-side.
