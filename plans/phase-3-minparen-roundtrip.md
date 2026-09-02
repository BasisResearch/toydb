# Phase 3: minimal-parenthesisation round trip (pins precedence)

Branch `kg/parser-fix-phase-3-minparen` off `kg/verified-parser-cutover`.
The spec-level work is independent of phase 2; the statement-level corollary
(task 4) needs phase 2 landed.

## Context (self-contained; verify against the tree)

The existing round-trip theorem is over a printer that parenthesises
EVERY operator node (`src/sql/parser/verified_roundtrip.rs` ~lines
230-249; `src/sql/parser/printer.rs` header says this is
deliberate). Its domain therefore contains no `1 - 2 - 3`, `-3 ^ 2`,
`NOT a AND b` — no SQL anyone types — so it cannot see precedence or
associativity. A review confirmed by mutation: swapping the precedence
of {+,-} and {*,/,%} in BOTH the exec table and its spec twin
(`src/sql/parser/verified_precedence.rs` ~lines 67-71 and 105-106)
verifies clean. A min-parens printer closes this: its parenthesisation
decisions encode the precedence table a third time, independently, so
the round trip fails unless parser, spec twin, and printer all agree.

What exists to build on:

- `verified_precedence::parse_expression_at` refines `sparse_prec` on all
  inputs (ensures ~lines 761-781), up to `verified_roundtrip::view_expr`.
  Any spec-level lemma about `sparse_prec` lifts to the live parser free.
- The unverified display logic to mirror: `types::ExpressionDisplay`
  (`src/sql/types/expression.rs` ~line 453) parenthesises a child only when
  it binds looser than its context.
- The precedence/associativity table (cross-check against the code):
  Or 1, And 2, Not 3, = != LIKE IS 4, comparisons 5, + - 6, * / % 7,
  ^ 8 right-assoc, postfix ! 9, prefix +/- 10.

## Tasks

1. Write a spec-level min-parens token printer `sprint_min` (over the same
   view type `sparse_prec` consumes) and an exec twin `print_min_expr`
   refining it. Write the printer's precedence table out longhand in the
   printer module rather than importing the parser's table; the point is a
   third independent encoding. Mirror `ExpressionDisplay`'s decisions.
2. Prove the spec-level round trip:
   `sparse_prec(sprint_min(e), 0, fuel) == (Some(e), empty)` for adequate
   fuel. This is real precedence reasoning (the induction tracks the
   min-precedence context); budget most of the phase here.
3. Lift to the live parser via the existing refinement:
   `parse_expression_at` over `print_min_expr(e)` returns `e` up to
   `view_expr`, consuming all tokens. State it as a theorem, not a comment.
4. (Requires phase 2.) Statement corollary: min-parens statement printer
   delegating expressions to `sprint_min`, round trip through
   `parse_control_at` via phase 2's `sparse_control`.
5. Document the residual honestly wherever the guarantee is stated: a
   CONSISTENT swap of exec table + spec twin + printer table still
   round-trips; the guards for that are the goldenscripts
   (`op_precedence`) and the differential harness restored in phase 0.

## Constraints

- No behaviour changes to the parser. Printer additions are new code; the
  existing fully-parenthesised printer and its theorem stay (they anchor
  the paren-heavy corner of the grammar).
- Add any new module to `VERIFY_MODULES` in `scripts/verus/verify.sh`.
- Do not push or open a PR; commit locally and report.

## Acceptance

- `scripts/verus/verify.sh` green, 0 errors; `cargo test --lib` green.
- Mutation check: swap {+,-}/{*,/,%} precedence in both the exec table and
  spec twin (`verified_precedence.rs` ~67-71, ~105-106) and confirm
  verification now FAILS; revert. Report the failing obligation.
- Associativity check: state (or test) that `1 - 2 - 3` prints unbracketed
  and re-parses left-nested, and `2 ^ 3 ^ 2` right-nested.
- Report the exact theorem statements as committed.
