---
name: mark-failed
description: Mark the current toyDB branch as a FAILED ATTEMPT on the Verus dashboard, with a short reason and a category tag. Use when the user says the branch/attempt/approach failed, should be abandoned, or asks to record why it did not work.
---

<!-- SPDX-License-Identifier: MIT -->

Mark the current branch as a failed attempt on the Verus dashboard.

Arguments: `$ARGUMENTS` — a short reason for the failure, optionally starting
with a category tag in square brackets, e.g. `[verus-timeout] Z3 blows up on
the roundtrip lemma`. If no arguments were given, summarise in one or two
sentences why this attempt failed based on the conversation so far.

Steps:

1. Pick a category from `python3 .claude/hooks/mark_branch.py categories`
   (verus-timeout, spec-too-strong, spec-wrong, missing-lemma,
   verus-unsupported, tooling-bug, scope-too-big, agent-stuck, abandoned,
   other). Use the bracketed tag from the arguments if one was given.
2. Write a SHORT reason (1–3 sentences). It does not need to be precise or
   complete — the point is to keep enough information to analyse later what
   went wrong and what tooling change would have prevented it. Mention the
   symptom (what Verus/the tool said) and your best guess at the cause.
3. Run, from the repo root:

   ```
   python3 .claude/hooks/mark_branch.py failed --category <tag> --agent claude "<reason>"
   ```

4. Report the script's output to the user. If it exits 2 (upload failed) say
   so explicitly and show the error; the mark was saved to the local log.

Do NOT rename, delete, or force-push the branch: the dashboard joins telemetry
on the branch name, so the name must stay stable. Do not commit anything as
part of marking. To undo a mark, run
`python3 .claude/hooks/mark_branch.py clear "<why>"`.
