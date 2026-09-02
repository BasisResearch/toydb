# Phase 2: functional spec on the live statement parser

Branch `kg/parser-fix-phase-2-stmt-spec` off `kg/verified-parser-cutover`
(rebase onto phase 0's branch if it has landed; the restored differential
harness is a useful cross-check here).

## Context (self-contained; verify against the tree)

Production parses statements via
`verified_control::parse_control_at(toks, pos)`
(`src/sql/parser/verified_control.rs`), whose ensures are only

    pos <= r.1 <= toks.len(),
    r.0 is None ==> r.2 is Some,

i.e. no-panic/termination/error-on-reject. A parser returning
`Statement::Commit` for every SELECT would verify. The 2026-08-31 review
(`../report.txt`) confirmed by mutation: making DESC parse as `Ascending`
(`verified_control.rs` ~line 597) verifies clean.

The expression layer below it is in good shape and is the template for this
phase: `verified_precedence::parse_expression_at`
(`src/sql/parser/verified_precedence.rs`, ensures around lines 761-781)
refines its spec twin `sparse_prec` on ALL inputs, up to
`verified_roundtrip::view_expr`, with the leftover-token stream pinned too.
`verified_control` calls it at every embedded expression position, so at each
such call site the spec-level result is already available.

Also relevant, in `src/sql/parser/verified_stmt.rs`: `view_stmt`
(ast::Statement -> SStmt, ~line 174), the token-level statement printer
`sprint_stmt` / exec `print_stmt_exec` (~line 3494), the mirror spec
`sparse_stmt` (~line 1216), and `lemma_sparse_stmt_sprint` (~line 1400),
which proves `sparse_stmt(sprint_stmt(s)) == (Some(s), empty)`.

**Warning:** do not try to prove `parse_control_at` refines the existing
`sparse_stmt`. That statement is false by construction: `sparse_stmt`'s
expression positions accept only the fully-parenthesised grammar, while
`parse_control_at` delegates to the precedence-climbing parser. You need a
new mirror.

## Tasks

1. Write `spec fn sparse_control(input: Seq<TokenView>, fuel: nat)` (name
   flexible): a spec-level mirror of `parse_control_at`'s keyword dispatch
   whose expression positions are `sparse_prec`. The exec code is the
   template; mirror it clause by clause, including the
   `parse_explain_at` mutual recursion. Target `SStmt` via `view_stmt`, or
   introduce a dedicated view type if `SStmt` does not fit; prefer reuse.
2. Strengthen `parse_control_at`'s ensures to a full refinement on all
   inputs, in the same shape as `parse_expression_at`'s: on `Some`, the
   spec twin agrees up to `view_stmt` and the rest-of-input views agree; on
   `None`, the spec twin rejects. Every clause parser in
   `verified_control.rs` (~15 routines) gets the corresponding
   strengthened contract. Expect to lean on `#[verifier::spinoff_prover]`
   and `#[verifier::rlimit]` as `verified_precedence.rs` does.
3. Prove the round trip at spec level: `sparse_control` inverts
   `sprint_stmt` (adapt the structure of `lemma_sparse_stmt_sprint`; the
   printer's fully-parenthesised expression output is inside `sparse_prec`'s
   accepted language, and `verified_stmt.rs` likely already has the
   expression-level bridge lemmas). Corollary on the live parser:
   `parse_control_at` over `print_stmt_exec(s)` returns `s` up to
   `view_stmt`, consuming all tokens.
4. Small, independent: `parse_expression_full`
   (`verified_precedence.rs` ~line 1106) is the entry production calls but
   ensures only error-presence; copy the refinement ensures onto it from
   `parse_expression` (bodies are identical).
5. Update the honest-guarantee doc comments (parser.rs header,
   `verus-parser-roundtrip-plan.md`) to reflect the new statement-level
   spec.

## Constraints

- No behaviour changes to the exec parser. If the proof reveals an actual
  bug, stop and report it rather than silently changing behaviour.
- Keep new spec/proof code in `verified_stmt.rs` or a new module added to
  `VERIFY_MODULES` in `scripts/verus/verify.sh`; do not remove anything
  from that list.
- Do not delete the dead twins yet (that is phase 4).
- Do not push or open a PR; commit locally and report.

## Acceptance

- `scripts/verus/verify.sh` green (count will grow past 636); 0 errors.
- `cargo test --lib` green.
- Mutation check: apply the DESC-as-Ascending mutation
  (`verified_control.rs` ~597) and confirm verification now FAILS; revert.
  Report the failing obligation.
- Second mutation check: swap `INSERT` and `DELETE` dispatch (or similar
  statement-level confusion) and confirm verification fails; revert.
- Report the exact top-level theorem statements as committed.
