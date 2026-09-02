# Fix plan: verified-parser cutover (kg/verified-parser-cutover)

Response to the 2026-08-31 review (`../report.txt`). The review found: production
calls `verified_control::parse_control_at`, whose only contract is
no-panic/termination/error-on-reject; the round-trip-proven parsers
(`verified_stmt::parse_stmt_exec` and friends, 8.5k lines) are dead code; the
legacy oracle and differential harness were deleted in `ee8d73d`; mutation
experiments confirm a precedence swap and a DESC-as-Ascending bug both verify
clean today.

Goal state: the parser production calls carries the functional spec and the
round trip; every verified exec function is either on the production path or
deleted; a tool flags any verified component that tests never execute.

One fact makes this tractable: `verified_precedence::parse_expression_at`
already refines its spec twin `sparse_prec` on ALL inputs
(verified_precedence.rs:761-781), and `verified_control` calls it at every
expression position. The statement layer above it is plain keyword dispatch.
So the live parser is close to a full functional spec; the machinery just
sits on the dead twin instead.

## Phase 0 — restore the oracle, fix the claims (small; first)

- Selectively revert `ee8d73d`: bring back the legacy recursive-descent
  parser and `differential.rs` under `#[cfg(test)]`. It is the only
  precedence-sensitive guard beyond the goldenscripts, and deleting it was
  the one step the review called irreversible in effect.
- Fix `parser.rs:26-30` ("the whole grammar ... is verified") and the Phase
  3/4 summaries in `verus-parser-roundtrip-plan.md` to state the actual
  guarantee: no-panic/termination everywhere, functional spec at the
  expression level only, round trip only on the fully-parenthesised range.

## Phase 1 — verified-but-unexecuted flagger (independent; can land any time)

New script `scripts/verus/verified_coverage.py`, two lenses:

- Dynamic: which verified exec functions did the test suite execute?
  - Verified-function set with file/line spans from Verus `--output-json`
    func-details, which `extract_metrics.py` already parses. Partition exec
    fns from spec/proof fns (ghost code is erased; it can never execute and
    is reported separately, not flagged).
  - Execution counts from `cargo llvm-cov test --lib` JSON export
    (goldenscripts run under the lib harness, so they count).
  - Join on file + line range. A verified exec fn with zero executed lines
    is flagged; roll up per module.
- Static: which verified functions are unreachable from production entry
  points? Extend `extract_graph.py` (it already builds the function-level
  call graph) with reachability from `Session::execute` /
  `Parser::parse`. This lens catches the twin-with-its-own-tests case that
  coverage alone misses.

Outputs: human table, JSON block for the dashboard ingest alongside the
existing coverage metrics, and a `--check` CI mode with a committed
allowlist for intentional exceptions.

Acceptance: on the current branch it must flag `verified_stmt.rs` (exec
layer), `verified_lexer.rs` (`lex_all_exec`), and `verified.rs`. CI gate
stays red until Phase 4 clears them.

## Phase 2 — functional spec on the live statement parser

- Write `sparse_control`: a spec-level mirror of `parse_control_at`'s
  keyword dispatch whose expression positions are `sparse_prec`. Mechanical;
  the exec code is the template, and each expression call site already has
  the spec-level result via `parse_expression_at`'s ensures.
- Prove the refinement on all inputs, same shape as the expression one:
  `parse_control_at(toks, pos)` agrees with `sparse_control(views)` up to
  `view_stmt`. This closes review gap (a): the DESC mutation then fails
  verification.
- Prove `sparse_control` inverts `sprint_stmt` (adapt
  `lemma_sparse_stmt_sprint`; fully-parenthesised output is inside the
  precedence grammar's domain). Corollary on the live parser:
  `parse_control_at(print_stmt_exec(s)) == s` up to `view_stmt`.
- Move the refinement ensures onto `parse_expression_full`, the entry
  production calls (review note 3, first bullet).

Note: a refinement of `parse_control_at` against the EXISTING `sparse_stmt`
is false on purpose; `sparse_stmt`'s expression positions only accept the
fully-parenthesised grammar. Hence the new mirror over `sparse_prec` rather
than a patch to the old one.

## Phase 3 — minimal-parens round trip (pins precedence)

- Write `print_min_expr` mirroring `types::ExpressionDisplay`
  (expression.rs:453): parenthesise a child only when it binds looser than
  its context. The printer carries its own precedence table, written from
  the grammar documentation, not imported from the parser.
- Prove `sparse_prec(sprint_min(e), 0, fuel) == e` at spec level; the
  existing all-inputs refinement lifts it to the live parser:
  `parse_expression_at(print_min(e)) == e` up to view. The theorem's domain
  now contains `1 - 2 - 3`, `NOT a AND b`, `-3 ^ 2`; the review's
  precedence-swap mutation fails verification under it.
- Statement corollary via Phase 2: min-parens statement printer, round trip
  through `parse_control_at`.
- Residual, stated in the docs: a consistent swap of exec table, spec twin,
  AND printer table would still round-trip. The guards for that are the
  goldenscripts (`op_precedence`) and the restored differential harness.
- Optional dual, not scheduled: `print(parse(toks)) == toks` on accepted
  token streams, pinning that the parser is faithful rather than
  normalising.

## Phase 4 — delete the dead twins (gated by the Phase 1 tool)

Once Phase 2 lands:

- Delete `parse_stmt_exec` / `parse_stmt_full_exec` and the
  fully-parenthesised mirror grammar in `verified_stmt.rs`; keep
  `view_stmt`, `sprint_stmt` / `print_stmt_exec`, and whatever spec layer
  Phase 2 reuses. This also removes the two String-Ord axioms
  (verified_stmt.rs:4753,4770), shrinking the trust surface.
- Delete `verified.rs` (Phase 0 proving ground, its own Token type).
- `verified_lexer.rs`: wire `lex_all_exec` into the production `Lexer` as
  its own follow-up milestone (string-level round trip is the user-facing
  claim; identifiers/keywords/strings are unverified today), or delete the
  exec twin. Either way it is an explicit allowlist entry until resolved,
  not silently dead.

Exit criterion: `verified_coverage.py --check` green with an empty or
documented allowlist.

## Phase 5 — retire the oracle again (last)

Only after Phases 2-3 are in and the coverage gate is green, re-delete the
legacy parser and differential harness if desired. Keeping the differential
under `#[cfg(test)]` permanently is also fine; it is cheap insurance against
the consistent-triple-swap residual.

## Ordering

Phase 0 immediately. Phase 1 is independent and useful from day one (it
would have caught this branch's end state). Phase 3's spec lemma can start
in parallel with Phase 2; they meet at the statement corollary. Phase 2's
mirror is mechanical but its proofs are the bulk of the work, on the order
of the existing verified_stmt effort, minus what reuse of `sparse_prec` and
the lemma structure buys.
