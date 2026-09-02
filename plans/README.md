# Verified-parser fix: phase briefs

Per-phase briefs for the fix plan responding to the 2026-08-31 review.
Phases 0-4, 6, and 7 are complete and their briefs deleted (git remembers;
see the merge commits on `kg/verified-parser-cutover` and the phase log in
`verus-parser-roundtrip-plan.md`).

Still here:

- `phase-4-delete-twins.md` — complete, retained because source
  doc-comments and the coverage allowlist cite it as provenance for the
  phase-4 deletions.
- `phase-5-retire-oracle.md` — OPEN (optional). The coverage allowlist's
  remaining entries name it as their scheduled follow-up: it decides
  whether the min-parens exec-carried theorems get test coverage or a
  recorded retirement, and whether the legacy oracle stays as permanent
  differential insurance (recommended) or is deleted again.

To execute a brief: spawn a fresh agent in the repo root and tell it to
read and execute the file. Branch off `kg/verified-parser-cutover` as
`kg/parser-fix-phase-N-<slug>`; do not push or open PRs without asking.
