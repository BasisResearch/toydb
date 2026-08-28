---
description: Mark the current branch as a failed attempt on the Verus dashboard (short reason + category tag)
---
<!-- SPDX-License-Identifier: MIT -->
Mark the current toyDB branch as a FAILED ATTEMPT on the Verus dashboard.

Arguments: `$ARGUMENTS` — a short reason, optionally starting with a category
tag in square brackets (e.g. `[missing-lemma] could not prove the sort
invariant`). If empty, summarise in one or two sentences why this attempt
failed based on the session so far.

Current branch: !`git rev-parse --abbrev-ref HEAD`
Suggested categories: !`python3 .claude/hooks/mark_branch.py categories | tr '\n' ' '`

1. Pick a category tag (free-form allowed, prefer the suggested ones).
2. Write a SHORT reason (1–3 sentences; imprecise is fine — it is kept for
   later analysis of what went wrong and how the tooling could improve).
   Mention the symptom and your best guess at the cause.
3. Run from the repo root:
   `python3 .claude/hooks/mark_branch.py failed --category <tag> --agent opencode "<reason>"`
4. Report the output. Exit code 2 means the upload failed and the mark was
   saved locally — tell the user.

Never rename, delete or force-push the branch (the dashboard joins on the
branch name). To undo: `python3 .claude/hooks/mark_branch.py clear "<why>"`.
