# Phase 0: restore the legacy oracle, fix overstated claims

Branch `kg/parser-fix-phase-0-oracle` off `kg/verified-parser-cutover`.

## Context (self-contained; verify against the tree, do not trust blindly)

This repo's SQL parser was cut over to a Verus-verified implementation
(`sql::parser::verified_control::parse_control_at`, called from
`Parser::parse` in `src/sql/parser/parser.rs`). A review found that the verified parser's
contract is only no-panic/termination/error-on-reject, and that commit
`ee8d73d` deleted the two things that pinned concrete-SQL behaviour beyond
the goldenscripts:

- the legacy recursive-descent parser (the `StreamingParser` methods,
  operator/precedence types, and the `#[cfg(test)]` oracles
  `Parser::parse_legacy` / `parse_expr_legacy`), and
- the differential harness (`sql::parser::differential`, ~447 lines:
  proptest generators over the full grammar, a concrete-syntax corpus, and
  per-line hooks in the goldenscript runners).

The review confirmed by mutation that a precedence swap and a
DESC-parses-as-Ascending bug both verify clean today; only goldenscripts
catch them. The oracle must come back until stronger specs land (phases 2-3).

## Tasks

1. Selectively revert `ee8d73d`: restore the legacy parser and the
   differential harness, gated under `#[cfg(test)]`. Read the commit
   (`git show ee8d73d`) for the full list of what it removed. The production
   path must not change: `parse_control_at` remains the only parser prod
   calls; the legacy code exists solely as a test oracle.
2. Restore the differential harness's per-line hooks in the goldenscript
   runners, and its error-message equivalence gating (see commit `8f3095c`
   for what that covered). One acknowledged, accepted divergence exists:
   `a IS <bad>` yields a trailing-token error rather than the legacy
   in-place error. Encode that exemption explicitly, do not weaken the
   whole check.
3. Fix the doc comment in `src/sql/parser/parser.rs` (around lines 24-30)
   claiming "The whole grammar ... is verified". State the actual
   guarantee: no-panic/termination everywhere; functional spec
   (refinement to `sparse_prec`) at the expression level only; round trip
   proven only on the fully-parenthesised range; statement grammar has no
   functional spec yet.
4. Make the same correction in the Phase 3/4 summaries of
   `verus-parser-roundtrip-plan.md` (repo root).

## Constraints

- No changes to any `verus!` proof code beyond what compiling the restored
  test-only modules requires.
- Do not push or open a PR; commit locally and report.

## Acceptance

- `scripts/verus/verify.sh` still reports 636 verified, 0 errors.
- `cargo test --lib` passes, now including the differential tests.
- Sanity check that the oracle bites: temporarily change
  `Token::Keyword(Keyword::Desc)` handling in
  `src/sql/parser/verified_control.rs` (~line 597) to `Ascending`, confirm
  the differential harness (not just goldenscripts) fails, then revert the
  mutation. Report the failing test name.
