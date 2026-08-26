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
