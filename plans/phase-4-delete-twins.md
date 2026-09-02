# Phase 4: delete the dead verified twins

Branch `kg/parser-fix-phase-4-cleanup`, off the phase 2 result.
Gated on: phase 2 landed (the live parser carries the statement spec) and
phase 1 landed (the flagger verifies the cleanup).

## Context (self-contained)

After phase 2, the spec layer of `src/sql/parser/verified_stmt.rs` is
load-bearing for the live parser, but its exec twins are not: production
never calls `parse_stmt_exec` / `parse_stmt_full_exec`, which parse only the
fully-parenthesised grammar. Similarly dead: `lex_all_exec` and its round
trip in `verified_lexer.rs` (production `Lexer` is plain Rust except
`scan_number_bytes` / `scan_symbol_bytes`), and all of `verified.rs`
(a self-described "Phase 0 proving ground" with its own Token type).
A review flagged these; phase 1's
`scripts/verus/verified_coverage.py` allowlists them pending this phase.

## Tasks

1. In `verified_stmt.rs`, delete `parse_stmt_exec`, `parse_stmt_full_exec`,
   and whatever mirror-grammar spec/proof code serves ONLY them after
   phase 2 (check what phase 2 reuses before cutting: `view_stmt`,
   `sprint_stmt` / `print_stmt_exec`, and bridge lemmas likely stay). This
   should remove the two String-Ord axioms (~lines 4753, 4770 pre-phase-2;
   re-locate) — confirm the trust surface shrank and say so in the commit.
   Drop the module-level `#![allow(dead_code)]`.
2. Delete `src/sql/parser/verified.rs`; remove `sql::parser::verified`
   from `VERIFY_MODULES` in `scripts/verus/verify.sh` and its `mod`
   declaration.
3. `verified_lexer.rs`: do NOT wire it into production in this phase (that
   is its own future milestone; string-level round trip needs
   identifiers/keywords/strings verified, which today they are not).
   Either delete the dead exec twin (`lex_all_exec` and its roundtrip
   lemma), keeping any spec layer a future lexer phase would restate, or
   keep it with an explicit dated allowlist entry naming the follow-up.
   Recommend deletion; git remembers. Choose, and justify in the report.
4. Regenerate the phase 1 allowlist: remove the entries this phase clears.
5. Update doc comments and `verus-parser-roundtrip-plan.md` so no text
   still refers to the deleted twins as the round-trip carrier.

## Constraints

- No changes to production behaviour; deletions and docs only, plus
  whatever `use`/mod plumbing the deletions force.
- If a deletion breaks a phase 2/3 proof, the code was not dead; restore
  it and note it in the report instead of forcing the cut.
- Do not push or open a PR; commit locally and report.

## Acceptance

- `scripts/verus/verify.sh` green, 0 errors (report the new verified
  count and module count).
- `cargo test --lib` green.
- `python3 scripts/verus/verified_coverage.py --check` green with an
  empty allowlist, or one whose every entry names a scheduled follow-up.
- Report lines-of-code delta for `src/sql/parser/` and the remaining
  trust surface (axioms + external_body fns), before vs after.
