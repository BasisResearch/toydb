# Task: cut the toyDB SQL parser over to the verified implementation

## Your goal
Make the parser that runs in production (`Parser::parse` / `Parser::parse_expr`)
be a Verus-verified parser, replacing the unverified recursive-descent parser in
`src/sql/parser/parser.rs`, WITHOUT regressing any SQL the database currently
accepts. Land it incrementally behind a differential-testing safety net; do not
big-bang swap.

## Ground truth (verify before trusting — this was written 2026-08-28)
- What runs today for parsing: `Parser::parse` (src/sql/parser/parser.rs:29) ->
  `StreamingParser<S: PeekStream>` over `stream::TokenStream`. `parser.rs` has
  ZERO `verus!` blocks — it is entirely unverified. Callers: `sql/mod.rs`,
  `sql/execution/session.rs`.
- The production lexer already partly runs verified code (scan_symbol_bytes,
  scan_number_bytes, verified_integer). Leave the lexer cutover alone.
- The verified parser exists but is DORMANT (no production caller):
  - `verified.rs::parse_expr` (src/sql/parser/verified.rs:689) is a *canonical,
    fully-parenthesized* expression parser: it accepts only `( ... )` groups or a
    single atom, with NO operator precedence. It is the exact inverse of the
    canonical printer, not a concrete-syntax parser.
  - It operates on a MIRROR token type and MIRROR AST (`Token::Integer`,
    `Expression::Column(value)`, `Literal::True`, `IsValue`, ...), NOT the
    production `ast::Expression` / `super::Token`.
  - `parse_stmt_full_exec` (statement-level verified exec parser) lives in
    `verified_stmt.rs` and works over the mirror AST with `view_stmt`/`view_expr`
    bridges back to production `ast`.
- The roundtrip proof guarantees `parse(print(e)) == e` on CANONICAL forms only.
  It does NOT prove the parser is total or correct over arbitrary concrete SQL.
  That is the core gap.

## The gap you must close (two dimensions)
1. Types: the verified parser produces mirror types; production needs
   `ast::Statement` / `ast::Expression` over `super::Token`. Either make the
   verified exec parser emit production `ast` directly, or prove a `view` bridge
   and convert at the boundary.
2. Grammar: the verified parser accepts only canonical parenthesized forms.
   Production accepts the full concrete grammar — operator precedence /
   precedence-climbing (`a + b * c`), optional `AS` in aliases, all ten statement
   kinds and every SELECT clause, joins, `INFINITY`/`NAN`/`*`, function calls,
   etc. (see parser.rs `parse_expression`, `parse_expression_atom`,
   `parse_statement`). The verified parser must accept everything the production
   parser accepts.

## Proof story (be explicit about what "verified" buys here)
A full correctness proof against a declarative grammar is likely out of scope.
The achievable, defensible target:
- Verus gives no-panic / no-arithmetic-overflow / termination for the exec parser.
- Behavioural equivalence to the trusted old parser comes from EXHAUSTIVE
  differential testing (below), not a proof. The old parser is retained as the
  oracle during and after cutover.
- Keep the existing roundtrip lemma as the spec-level anchor.
State this trade-off in your plan; if you believe a stronger proof is tractable,
propose it in Phase 0 rather than assuming it.

## Required approach — phased, with checkpoints
Phase 0 — Scope & plan (STOP for sign-off before coding):
  - Map every concrete-syntax feature the production parser accepts that the
    verified parser does not. Produce a coverage table.
  - Decide the types strategy (emit `ast` directly vs view-bridge + convert).
  - Decide the precedence strategy (verified precedence climbing vs pratt).
  - Write the differential-test harness design.
  - Deliver a written plan + the coverage table. Do not proceed until approved.

Phase 1 — Differential harness first (safety net before any swap):
  - Add a test-only path that runs BOTH parsers on the same input and asserts
    identical `ast::Statement`. Feed it: every .sql in the goldenscript suites
    (queries / isolation / anomalies), the existing proptest generators in
    printer.rs, and a new SQL-source proptest corpus. This must be green on the
    OLD parser vs itself trivially, then used to gate the new parser.

Phase 2..N — Extend the verified parser feature-by-feature (expressions with
  precedence first, then each statement kind), keeping `scripts/verus/verify.sh`
  green and the differential harness green after each increment. Never expand the
  accepted-but-unverified surface; if the verified parser can't yet handle a form,
  keep routing it to the old parser behind an explicit, logged fallback so nothing
  regresses, and track the remaining fallbacks.

Final — Cutover: make `Parser::parse` call the verified parser; keep the old
  parser compiled and reachable as the differential oracle in tests. The accepted
  SQL surface must be identical (differential harness green on the full corpus).

## Constraints (mechanically enforced — do not fight the hooks)
- Never commit/push to `main`. Work on a branch named `<initials>/<topic>`
  (e.g. `kg/verified-parser-cutover`). See CLAUDE.md / AGENTS.md branch_guard.
- PRs: this repo is a fork — `gh pr create --repo BasisResearch/toydb --base main ...`.
- Verus workflow: run `bash scripts/verus/verify.sh` (cargo-verus focus over the
  opted-in modules). The `mcp__verus__verify` tool is standalone-single-file only;
  it fails on crate modules with `E0601 main not found` — do not use it for these.
- Gates that must stay green every commit: `cargo build`, `cargo test`,
  `cargo fmt -- --check`, `cargo clippy`, `scripts/verus/verify.sh`
  (currently 558 verified, 0 errors).
- Ghost-only imports go behind `#[cfg(verus_keep_ghost)]` so plain `cargo build`
  stays clean.

## Definition of done
- `Parser::parse` and `Parser::parse_expr` run the verified parser.
- Differential harness green across all goldenscripts + proptest corpora (old vs
  new produce identical ASTs); zero un-tracked fallbacks to the old parser on the
  accepted surface.
- `scripts/verus/verify.sh` green; the exec parser carries no-panic/termination
  proofs and the roundtrip lemma still holds.
- All standard gates green. A PR to `BasisResearch/toydb:main` describing the
  proof story honestly (what is proven vs differentially tested).

## First action
Do Phase 0 only and report back with the coverage table, the two strategy
decisions, and the harness design. Do not start Phase 2+ without sign-off.
