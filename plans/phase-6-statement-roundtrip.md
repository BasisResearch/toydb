# Phase 6: statement-level spec composition + min-parens statement roundtrip

Branch `kg/parser-fix-phase-6-stmt-roundtrip`, off `kg/verified-parser-cutover`
AFTER the phase-4 twin deletion has merged (both phases touch
`verified_stmt.rs` / `verified_stmt_prec.rs`; do not start before).

## Context (self-contained)

Phase 2 refined every statement *sub*-parser in
`src/sql/parser/verified_control.rs` against `sparse_control_*` spec twins in
`verified_stmt_prec.rs` (BEGIN, DROP, DELETE, INSERT, UPDATE, CREATE, the
SELECT list, FROM join tree, GROUP BY, ORDER BY, and the shared
`parse_clause_expr_at`). Three functions still carry only the weak
no-panic/error-on-reject contract:

- `parse_control_at` (verified_control.rs:81) — the top-level dispatch
  production calls; COMMIT/ROLLBACK are inline here.
- `parse_select_at` (~line 170) — its clauses are refined individually but the
  composed SELECT is not.
- `parse_explain_at` (~line 114).

Consequence: a dispatch swap (e.g. route the INSERT keyword to
`parse_delete_at`) verifies clean today. Phase 3 proved the min-parens
roundtrip for expressions (`verified_minparen.rs`: `min_roundtrip`,
`min_roundtrip_live`) but deferred its task 4, the statement corollary,
because it needed this composition.

Phase 4 deleted the dead mirror exec twins from `verified_stmt.rs`; check
what spec layer survived (`view_stmt` and the view helpers should be there;
the old fully-parenthesised statement printer may not be — the printer you
need is new anyway).

## Tasks

1. `sparse_control_select`: compose the existing clause twins
   (`sparse_control_select_list`, `sparse_control_from`,
   `sparse_control_group_by`, `sparse_control_order_by`, plus WHERE/HAVING/
   LIMIT/OFFSET via `sparse_prec`) into a spec twin of `parse_select_at`'s
   sequencing, and prove the refinement on all sized inputs, same shape as
   the phase-2 proofs.
2. `sparse_control` (top level): keyword dispatch mirroring
   `parse_control_at`, including inline COMMIT/ROLLBACK and EXPLAIN
   (`sparse_control_explain` wrapping the recursion; mind the mutual
   recursion — mirror the exec side's `decreases` structure). Refine
   `parse_control_at` and `parse_explain_at`.
3. Min-parens statement printer: spec `sprint_min_stmt` (keyword skeleton
   per statement kind; expression positions delegate to
   `verified_minparen::sprint_min`; clause lists delegate to per-clause
   spec printers) and exec twin `print_min_stmt` whose token view refines
   it. New module or `verified_minparen.rs` — either way add to
   `VERIFY_MODULES` in scripts/verus/verify.sh if new.
4. The roundtrip: `sparse_control(sprint_min_stmt(s)) == (Some(s), empty)`
   at spec level for printable statements, lifted through task 2's
   refinement to the live parser:
   `parse_control_at(print_min_stmt(s)) == s` up to `view_stmt`, consuming
   every token. State both as named theorems.
5. Differential lens: add `statement_parsers_agree_minparens` to
   `src/sql/parser/differential.rs`, mirroring
   `expression_parsers_agree_minparens` (same printable-domain guard
   pattern) so generated statements reach bare-precedence clause syntax.
6. Docs: update the `Parser::parse` header comment in parser.rs (it also
   still says UPDATE has no functional spec — stale since phase 2's UPDATE
   refinement landed) and `verus-parser-roundtrip-plan.md`.

## Constraints

- No behaviour changes to the exec parser. If a proof reveals a real bug,
  stop and report it.
- Do not push or open a PR; commit locally (small commits per task) and
  report.
- cargo-verus caches by content hash and does not key on --verify-* flags;
  after edits, a "Finished in 0.05s" run is cache replay, not verification.
  Delete target/verus-partial/debug/.fingerprint/toydb-* to force a real
  run. Toolchain: export PATH="$HOME/.local/verus/verus-arm64-macos:$PATH".

## Acceptance

- `scripts/verus/verify.sh` fresh run, 0 errors; `cargo test --lib` green.
- Mutation check A: swap INSERT and DELETE dispatch in `parse_control_at`
  — verification must now FAIL; revert, report the failing obligation.
- Mutation check B: drop the WHERE clause from the SELECT composition (or
  similar clause omission) — verification must FAIL; revert, report.
- Report the exact theorem statements as committed.
