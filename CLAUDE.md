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
