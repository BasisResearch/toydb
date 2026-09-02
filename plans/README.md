# Verified-parser fix: phase briefs

Per-phase briefs for a fix plan, responding to a review. Each brief is
self-contained: spawn a fresh Claude instance in this repo root and
tell it to read and execute one brief. Example:

    cd ~/Documents/code/verus-research/toydb
    claude "Read plans/phase-1-verified-coverage.md and execute it."

Baseline on `kg/verified-parser-cutover` (all phases must preserve it):

- `scripts/verus/verify.sh` — 636 verified, 0 errors, 21 modules
- `cargo test --lib` — 313 passed, 0 failed

Ordering and dependencies:

| Phase | Brief | Depends on |
|---|---|---|
| 0 | phase-0-restore-oracle.md | nothing; do first |
| 1 | phase-1-verified-coverage.md | nothing; parallel with 0 |
| 2 | phase-2-statement-spec.md | 0 (uses restored differential as a check) |
| 3 | phase-3-minparen-roundtrip.md | spec lemma parallel with 2; corollary needs 2 |
| 4 | phase-4-delete-twins.md | 1 (gate) and 2 |
| 5 | phase-5-retire-oracle.md | 2 and 3 landed, phase-1 gate green |

Branch each phase off `kg/verified-parser-cutover` as
`kg/parser-fix-phase-N-<slug>`; do not push or open PRs without asking.
