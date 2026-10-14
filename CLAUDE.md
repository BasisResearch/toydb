# toyDB (Basis) — repo rules

## Branch & PR discipline (MANDATORY, mechanically enforced)

- **Never commit to or push `main`.** All changes land through a feature
  branch and a PR to `main`.
- **Every branch you create MUST be named `<initials>/<topic>`** — the
  author's unique 2-3 lowercase-letter initials, a slash, then a short topic.
  Yiyun's prefix is `yl/` (e.g. `yl/fix-stop-hook`); each collaborator uses
  their own prefix. Initials must be unique across collaborators so branch
  names never collide.
- Why it matters beyond tidiness: the Verus CI dashboard associates Claude
  session telemetry with **branch names**, and folds a branch's data into the
  `main` view once its PR merges. Colliding or reused branch names would
  attribute one person's sessions to another's work.

## Creating the PR (this repo is a fork)

- `BasisResearch/toydb` is a **fork** of the upstream toyDB. `gh pr create`
  defaults its base to the *parent* repo, so a bare `gh pr create --base main`
  fails with `No commits between main and <branch>` / `Head sha can't be
  blank`. **Always pass `--repo BasisResearch/toydb`:**

  ```
  gh pr create --repo BasisResearch/toydb --base main --title "..." --body "..."
  ```

  The branch guard blocks a `gh pr create` that omits `--repo`.

These rules are enforced by `.claude/hooks/branch_guard.py`, a `PreToolUse`
hook on the Bash tool: it blocks `git checkout -b`/`git switch -c`/`git
branch` with non-conforming names, `git commit` while on `main`, any
`git push` to `main` or of a non-prefixed branch, and a `gh pr create` that
omits `--repo`. The same guard also backs the opencode plugin
(`tool.execute.before`) and the committed git hooks in `.githooks/`
(pre-commit / pre-push, self-provisioned via `core.hooksPath`), which cover
Codex and humans — the same rules apply to every agent (see `AGENTS.md`). If
it blocks you, rename the branch (`git branch -m <initials>/<topic>`) and
retry — do not try to bypass the hook.

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
