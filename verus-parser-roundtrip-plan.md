# toyDB SQL parser: Verus roundtrip verification plan

Status: **E0-E4 complete (2026-08-27)** — the full expression-grammar
print/parse roundtrip is verified end to end. Owner: kg (parser). Runs parallel
to MVCC work (yl), no file overlap. Verified module opt-in via
`scripts/verus/verify.sh`.

## Completion status (2026-08-27)

The "Complete expression roundtrip — execution plan" (E0-E4) below is **done**,
landed in `src/sql/parser/verified_roundtrip.rs` (opted into `verify.sh`,
`verus focus` green, normal `cargo check` clean):

- **E0** — `SExpr` mirror of the whole `ast::Expression` grammar, `view_expr`
  bridge, `sprint` canonical printer, `sdepth` fuel measure + `sdepth_le_len`
  length bound.
- **E1+E2** — `sparse`/`sparse_args` mirror parser and the roundtrip
  `lemma_sparse_sprint` / `lemma_sparse_args_sprint` over the *entire* grammar
  (`All`, `Column`, every `Literal`, all 15 `Operator`s, and nested
  `Function`s), with `mirror_roundtrip` and `mirror_injective` corollaries. The
  `Ident (` / `Ident . Ident` / bare-`Ident` disambiguation and the extended
  boundary predicate (forbids a trailing `(` and `.`) are proved.
- **E3** — `parse_expr_exec` / `parse_args_exec`: executable parsers over
  `Vec<Token>` building real `ast::Expression` (Box children, Vec args),
  verified to refine `sparse` at the `view_expr` level. Literal payloads parse
  through the existing `verified_integer` / `float_trust` exec surface.
- **E4** — `print_expr_exec` / `print_args_slice` (executable printer,
  `token_views(result) == sprint(view_expr(e))`), the paren-wrapping
  combinators, and the headlines `roundtrip_exec`,
  `print_parse_roundtrip_exec` (fully self-contained), and
  `roundtrip_injective`.

Trust surface is unchanged: the only axioms are the three `float_trust`
assumptions. Everything else is axiom-free.

The expression headline is fuel-free: `print_expr_exec` recurses on the ghost
measure `sdepth(view_expr(*e))` (a `decreases` may be ghost even for exec code),
so `print_parse_roundtrip_exec(e)` takes only the expression and `printable_se`.
An executable `usize` fuel counter was avoided on purpose — `sdepth` is an
unbounded `nat`, so a counter would need an unprovable "AST fits in `usize`"
bound to rule out overflow.

**Remaining work** — the statement layer and the production cutover — is scoped
concretely in "Remaining work" below.

## Remaining work — statement roundtrip + cutover

The statement layer reuses the expression pieces wholesale: `parse_expr_exec` /
`print_expr_exec` for every embedded expression, `sparse` / `sprint` for the
mirror, and the `view_expr` bridge. What is new is the statement-level mirror
`SStmt` (a `Seq`-based mirror of `ast::Statement`, embedding `SExpr` for
expression children), and the keyword-driven wrappers around the expression
grammar. Same three-layer shape as E0-E4: mirror + roundtrip, then executable
refinement at a `view_stmt` level.

The wrinkles are all about the containers `Statement` carries, so the phases are
ordered by container difficulty rather than by statement kind.

- **S0 — mirror scaffold + bridge.** `SStmt`, `view_stmt: ast::Statement ->
  SStmt`, `sprint_stmt`, `sdepth_stmt`. Expression children go through the
  existing `view_expr` / `sprint`. Small, mirrors E0.

- **S1 — list-free statements.** `Begin` / `Commit` / `Rollback` / `DropTable`
  / `Explain` (recursive wrapper, forbid `Explain(Explain(_))`), and `Delete`
  with an optional `where` in the verified expression domain. The spec-level
  encodings already exist in `verified_production` (`control_tokens`,
  `drop_table_tokens`, `begin_views`, `delete_views`); port them onto `SStmt`
  and prove `sparse_stmt(sprint_stmt(s)) == (Some(s), [])`. Reuse
  `lemma_sparse_sprint` for the embedded `Delete` predicate.

- **S2 — single-level lists.** `CreateTable` columns, `Select`'s `select` (with
  `Option<String>` aliases and the `All`-only-unaliased rule via the existing
  `contains_all` predicate), `group_by`, `order_by` (with `Direction`), and
  `Insert`'s optional column-name list. Each is one comma list over an
  expression (or name), so the `sparse_args` / comma-list lemma from
  `verified_roundtrip` is the template; write one statement-list lemma and
  instantiate it per position.

- **S3 — nested lists and the join tree.** `Insert.values : Vec<Vec<Expression>>`
  is a comma list of parenthesised comma lists, so the mirror needs
  `Seq<Seq<SExpr>>` and a two-level list lemma (outer list of rows, inner list
  of values). `Select.from : Vec<From>` with `From::Join` is a left-deep
  recursive tree (right child always a table, `CROSS JOIN` alone omits its
  predicate); mirror it as a recursive `SFrom` and prove its roundtrip with the
  join-associativity direction fixed by the printer, reusing `printable_from`.

- **S4 — `Update.set : BTreeMap<String, Option<Expression>>`.** The hard one.
  A `BTreeMap` has no canonical printable order that Verus models cheaply, and
  its equality is not view-determined. Decide the representation up front:
  carry the assignments in the mirror as a `Seq<(String, Option<SExpr>)>` sorted
  by key, have `print_stmt_exec` emit them in that fixed order, and have the
  parser rebuild the `BTreeMap` — stating the roundtrip through a `view_stmt`
  that canonicalises the map to the same sorted sequence (so map equality is
  never needed, exactly as `view_expr` sidesteps `Vec` equality). If Verus's
  `BTreeMap` model is too thin to rebuild from a sequence, restrict the verified
  `Update` domain to a sorted-key normal form and document the gap.

- **S5 — executable statements + headline.** `parse_stmt_exec` / `print_stmt_exec`
  building real `ast::Statement`, refining `sparse_stmt` / `sprint_stmt` at
  `view_stmt`, delegating every expression to `parse_expr_exec` /
  `print_expr_exec`. Headlines `print_parse_roundtrip_stmt` (fuel-free, same
  ghost-measure `decreases` trick) and `stmt_injective`.

### Phase 4 — production cutover (independent of S0-S5)

Replace the two `std::iter::Peekable`s with the verified cursors so the verified
functions become the production functions (coverage numerator up, denominator
flat):

- `Lexer.chars : Peekable<Chars>` -> the byte cursor `next_token(&[u8], pos)`
  from `verified.rs`.
- `Parser.lexer : Peekable<Lexer>` -> the `TokenStream` / `PeekStream` leaf.
- Swap `parse.rs`'s recursive-descent expression/statement parsers for
  `parse_expr_exec` / `parse_stmt_exec`, and delete the std-iterator plumbing.
- Run the existing SQL suite green. Budget the ripple onto `verified_production`
  / `verified_statements` (the spec-parser-backed statement proofs) — migrate
  them onto the executable parser, then retire the spec parser.

### Phase 5 — optional refinements

Minimal-parenthesisation printer (mirror `types::ExpressionDisplay`) reproved to
roundtrip via the precedence-table argument, and the lift to string level once
the byte-cursor lexer's own roundtrip is proved (`parse(print_str(e)) == e`).

## Original plan follows

Verified module opt-in via `scripts/verus/verify.sh`.

## Objective

Prove `parse(print(e)) == e` (print-parse roundtrip, "Style B") for parser-producible
`ast::Expression`, then `ast::Statement`, while:

- keeping the parser **streaming** (single pass, O(1) token buffer, no `Vec<Token>` materialisation),
- shipping a **single implementation** (no digital twin, no differential test),
- keeping the **trusted surface tiny and audited** (one file, three float assumptions; everything else axiom-free).

This grows the verified coverage surface in the pure-logic style already proven to work in
this repo (keycode), on code entirely disjoint from `storage/mvcc.rs`.

## Why roundtrip, not grammar-completeness

The heavy verified parsers (CompCert/Menhir, CoStar in Coq) prove soundness + completeness
against a formal grammar. That needs a separate grammar formalisation and an ambiguity proof.
Roundtrip against a canonical printer is the lighter, high-leverage property (the flavour of
Narcissus/EverParse and the Dafny stdlib JSON codec), and it is exactly the keycode roundtrip
one layer up the stack. toyDB's AST has no printer yet, so we write a canonical one and control
its shape.

## What toyDB uses today (the thing being replaced)

`std::iter::Peekable`, twice, for one-element lookahead:

- Parser layer: `Parser.lexer: Peekable<Lexer<'a>>` (`parser.rs:18`), from `Lexer::new(input).peekable()`.
  The peeked iterator is toyDB's own `Lexer` (`impl Iterator<Item = Result<Token>>`, `lexer.rs:320`).
- Lexer layer: `Lexer.chars: Peekable<Chars<'a>>` (`lexer.rs:316`), from `input.chars().peekable()`.
  The peeked iterator is std's `Chars`.

Neither is verifiable as-is: the "how much input is left" quantity lives inside a std type Verus
never compiles, so there is no `decreases` measure and no spec for `next()`. The obstacle is
specifically `std::iter::Peekable`, not streaming.

## Architecture (the spine)

Streaming is preserved by making the cursor **explicit** instead of hidden in a std iterator,
packaged behind a Peekable-shaped trait so parser code keeps `peek`/`next` ergonomics.

- **Layer A, bytes -> tokens** (replaces `Peekable<Chars>`): a pure scanner
  `next_token(input: &[u8], pos: usize) -> (Result<Option<Token>>, usize)` with
  `decreases input.len() - pos`. Explicit byte cursor, no `Chars`, no std `Peekable`.
- **Interface**: a `PeekStream` trait with `spec fn view(&self) -> Seq<Token>` and `peek`/`next`
  whose `ensures` are written against `view()`. This is a *contract*, not a trusted axiom:
  every implementer must prove its body meets it; the parser assumes only the contract.
- **Leaf**: `TokenStream { input: &[u8], pos, lookahead }` implements `PeekStream` using
  `next_token`; `view()` is defined as `tokens_from(input, pos)` (a `spec fn`, not assumed).
  Because the leaf bottoms out at `&[u8]` indexing (a Verus native), the contract is discharged
  with no axiom.
- **Layer B, tokens -> AST** (replaces `Peekable<Lexer>`): the parser is generic,
  `parse_expr<S: PeekStream>(s: &mut S) -> Result<Expression>`, verified once against the trait
  with `decreases s.view().len()`.
- **Printer**: canonical `print_expr`/`print_statement` emitting `Seq<Token>`, **fully
  parenthesised** first so the roundtrip proof is structural. Minimal-parens is a later refinement.

Same `peek/next` ergonomics as today, streaming, one implementation, and the termination proof is
done once against the contract, independent of the concrete stream.

## Spec skeleton

```rust
// interface
trait PeekStream {
    spec fn view(&self) -> Seq<Token>;                 // remaining tokens (ghost)

    fn peek(&mut self) -> (r: Option<Token>)
        ensures
            r == if self.view().len() == 0 { None } else { Some(self.view()[0]) },
            self.view() == old(self).view();            // peek does not consume

    fn next(&mut self) -> (r: Option<Token>)
        ensures
            old(self).view().len() == 0 ==> r is None && self.view() == old(self).view(),
            old(self).view().len() >  0 ==> r == Some(old(self).view()[0])
                                          && self.view() == old(self).view().drop_first();
}

// leaf (verified, discharges the contract; no axiom)
struct TokenStream<'a> { input: &'a [u8], pos: usize, lookahead: Option<Token> }
impl PeekStream for TokenStream<'_> {
    spec fn view(&self) -> Seq<Token> { tokens_from(self.input, self.pos) }
    fn next(&mut self) -> Option<Token> { /* body checked against ensures */ }
    fn peek(&mut self) -> Option<Token> { /* ditto */ }
}

// parser (verified once against the contract)
fn parse_expr<S: PeekStream>(s: &mut S) -> (r: Result<Expression>)
    decreases s.view().len()
{ /* uses s.peek()/s.next(); each recursion consumes >=1 so view() shrinks */ }

// canonical printer
spec fn print_expr(e: Expression) -> Seq<Token> decreases e;

// headline
proof fn print_parse(e: Expression)
    requires parseable(e),
    ensures  parse_expr(&mut TokenStream::of(print_expr(e))) == Ok(e);   // consumes the whole view
```

## Scope decisions

1. **Work at the token layer** (`Seq<Token>`), not raw `&str`. Compose with the byte-cursor lexer's
   own roundtrip later for the full string-level statement.
2. **String / identifier payloads are opaque byte runs**: carried and compared, never inspected,
   so Verus's weak `str` support never bites.
3. **`All` (`*`) handled by a context predicate**, valid only in a select list.
4. **Single implementation**: production `parser.rs`/`lexer.rs` are switched to the verified
   functions at cutover. No twin, so no differential test.
5. **Float literals: finite-guarded trust (option 2)** — see below. AST stays `Literal::Float(f64)`,
   so nothing ripples into the planner/executor.

## Float decision (option 2: finite-guarded trust)

The roundtrip `parse(print(Float(x))) == Float(x)` unfolds to `parse_f64(display_f64(x)) == x`,
bit-exact, which needs correctly-rounded decimal<->binary conversion (Ryu/Dragonbox + Lemire) and
an IEEE model. Verus has no `f64` reasoning, so proving it is out of scope. Instead:

- Parser-produced floats are always **finite** (`NaN`/`inf` lex as identifiers, not `Number` tokens).
- For finite `x`, Rust's `Display` emits the shortest string that `FromStr` reads back bit-exactly.
  So the finite-guarded roundtrip is a **true** statement; we trust rustc's float conversion rather
  than prove it.
- The naive *un*guarded axiom `parse(display(x)) == x` is **false** under toyDB's `to_bits` equality
  (NaN payloads, signalling NaN), so the `is_finite()` guard is load-bearing, not decoration.

Well-formedness carries the guard:
```rust
spec fn parseable(e: Expression) -> bool {
    match e {
        Literal(Float(x))  => x.is_finite(),
        Literal(_)         => true,
        Operator(op)       => parseable_op(op),
        Function(_, args)  => forall|i| 0 <= i < args.len() ==> parseable(args[i]),
        // All only in select-list position; handled by a context predicate at Phase 3
        ...
    }
}
```

Trusted boundary, quarantined to one file `float_trust.rs`:
```rust
#[verifier::external_body] fn display_f64(x: f64) -> (s: Vec<u8>) ensures s@ == spec_display(x);
#[verifier::external_body] fn parse_f64(s: &[u8]) -> (r: Option<f64>) ensures r == spec_parse(s@);

#[verifier::external_body]                    // THE trusted assumption (true for finite x)
proof fn axiom_f64_finite_roundtrip(x: f64)
    requires x.is_finite(),
    ensures  spec_parse(spec_display(x)) == Some(x);
```

`f64` stays fully opaque: no arithmetic, no IEEE model. The only facts used are `is_finite`, the two
uninterpreted `spec_display`/`spec_parse`, the axiom relating them, and that `f64` spec-equality is
bit-equality (to match toyDB's `to_bits` `Literal` equality). Integer literals get a **native** exact
proof (`parse_i64(display_i64(n)) == n`), no trust.

## Trust surface (audited, small)

Exactly three assumptions, all in `float_trust.rs`:

1. `display_f64` / `parse_f64` faithfully model `<f64 as Display>` / `<f64 as FromStr>`.
2. `axiom_f64_finite_roundtrip` (true, but trusts rustc's formatter/parser instead of proving them).
3. `f64` spec-equality is bit-equality.

Everything else (the `PeekStream` contract, the `TokenStream` leaf, the parser, all
integer/string/bool/null literals, the whole roundtrip proof) is fully verified with no axioms.
Review rule: any new `PeekStream` implementer must be verified Rust; an `external_body` implementer
would silently re-introduce trust.

## Properties delivered

- **Totality**: the parser panics on no input; every token stream yields a `Result`.
- **Termination**: proved once against the `PeekStream` contract via `decreases s.view().len()`.
- **Roundtrip**: `parse(print(e)) == e` for `parseable(e)`, including finite floats.
- **Printer injectivity** on `parseable` ASTs, as a corollary.

## Phases

- **Phase 0 - spine compiles and proves trivially (2-4 days).**
  Add module `sql::parser::verified` to `scripts/verus/verify.sh`. Define Verus-side `Token`
  (plain enum, byte payloads), a minimal `next_token`/`tokens_from` with `decreases input.len()-pos`,
  the `PeekStream` trait, the `TokenStream` leaf (prove its two methods meet the contract),
  the `float_trust.rs` stub. Prove one literal roundtrip (integer native, float via the axiom).
  Wires leaf -> trait -> generic parser -> printer and the proof harness.

- **Phase 1 - minimal expression grammar, end to end (3-5 days).**
  Literals + `Column` + two binary ops + one unary. Fully-parenthesised printer,
  `parse_expr<S: PeekStream>`. Prove totality, termination, roundtrip. This is the template.

- **Phase 2 - full expression operator set (1.5-2.5 weeks).**
  All of `Operator`: `And/Or/Not`, comparisons (`= != < <= > >=`, `IS`), arithmetic
  (`+ - * / % ^`), unaries (`Negate`, `Identity`, `Factorial`, `SquareRoot`), `Like`.
  Plus `Function(name, args)` (comma-list roundtrip lemma over `Vec<Expression>`) and qualified
  `Column(Option<String>, String)`. Float literals land here via `float_trust`. Proof is structural
  induction on `Expression`; the generic termination proof from Phase 1 is reused unchanged.

- **Phase 3 - statements (1-1.5 weeks).**
  `print_statement`/`parse_statement` roundtrip for the `Statement` variants (transaction control,
  `CREATE/DROP TABLE`, `INSERT`, `UPDATE`, `DELETE`, `SELECT`). Linear keyword-driven wrappers around
  expressions; roundtrip composes over Phase 2 + list lemmas. `All` enters via the select-list predicate.

- **Phase 4 - cut over production (3-5 days).**
  Replace `Parser`'s `Peekable<Lexer>` with `TokenStream` and `Lexer`'s `Peekable<Chars>` with the
  byte cursor; delete the std-iterator plumbing. Run the existing SQL suite green. The verified
  functions become the production functions, so coverage moves properly (numerator up, denominator flat).

- **Phase 5 - optional refinements.**
  Minimal-parenthesisation printer (mirror `types::ExpressionDisplay`, `expression.rs:451`) reproved
  to roundtrip (the precedence-table = precedence-table argument). Lift to string level once the
  byte-cursor lexer's own roundtrip is proved: `parse(print_str(e)) == e`.

## Findings so far (2026-08-27)

Phase 2's `Function(name, args)` case turned out to have two separate obstacles,
only one of which the plan anticipated.

- **Termination is solved.** Recursion through `Vec<Expression>` admits a
  measure: a spec height whose list component decreases on the argument
  *sequence* (`decreases args`), not on `args.len()` (an `int`, which is
  type-incompatible with the datatype measure in the mutual-recursion group).
  Confirmed on Verus `0.2026.08.23`.

- **The real wall is Verus's `Vec` model.** `Vec` has no spec-level
  constructor, and `Vec` equality is not determined by its view, not even
  deeply (`v1@ == v2@` does not give `v1 == v2`). So a `spec fn` parser cannot
  build a `Function(name, Vec)` node, and no spec proof can recover the node
  equality the roundtrip needs. This is why the spec-parser core in
  `verified_expression.rs` is intrinsically limited to function-free
  expressions.

- **The exec-parser path works, and is validated in-repo.** An executable
  parser that builds `Vec`s at runtime, verified against a `Seq`-based mirror
  AST at the level of a structural view, closes the comma-list roundtrip for
  functions with no axioms. `src/sql/parser/verified_function_list.rs` carries
  the full pattern (spec-mirror roundtrip, `parse_exec`/`parse_args_exec`
  refining the mirror, and an end-to-end `roundtrip_demo` over real `Vec`s) and
  is opted in to `verify.sh`.

This sharpens Phase 4: the parser cutover is not only the production win, it is
the *only* way to bring functions into the roundtrip at all. Phases 2-3 should
either move to the executable-parser style throughout or accept the function-
free restriction until cutover.

## Complete expression roundtrip — execution plan

Goal: `view_expr(parse_expr_exec(print_expr(e))) == view_expr(e)` for every
`printable(e)` across the full grammar — `All`, `Column`, `Literal`, all 15
`Operator` variants, and `Function` — axiom-free apart from the existing
`float_trust` surface. Injectivity up to `view_expr` follows as the corollary.

The target equality is stated through `view_expr`, not raw `==`, because Verus
`Vec` equality is not view-determined (see Findings). `view_expr` is total and
structural, so the statement loses no information: it fixes every name, literal,
operator, nesting, and argument order/count.

### Why one unified executable parser

A `Function` can nest under any operator, and any expression can be a function
argument, so the parser is a single mutually-recursive nest. The spec parser
cannot build `Function` nodes, so the whole nest moves to executable code at
once. There is no partial spec/exec split at the expression level.

### Architecture (three layers)

- **Mirror layer (all spec).** A `Seq`-based mirror AST `SExpr` covering the
  full grammar — operator children are `Box<SExpr>`, function arguments are
  `Seq<SExpr>`. It carries the printer, fuel measure, parser, and the roundtrip
  proof. Everything here is spec-constructible and extensional, so the roundtrip
  closes with real `==` on `SExpr`.
- **Executable layer.** `parse_expr_exec` builds real `ast::Expression` (Box
  children, `Vec` arguments) and is verified to refine the mirror parser at the
  level of `view_expr`. `print_expr_exec` materialises the token vector.
- **Bridge.** `view_expr: ast::Expression -> SExpr` and the lemma
  `print_expr(e) == sprint(view_expr(e))` connect the two, so the existing spec
  printer (and the statement printers built on it) are reused unchanged.

### Components

- `SExpr` + `view_expr` / `view_args` (`ast::Expression -> SExpr`,
  `Seq<ast::Expression> -> Seq<SExpr>`).
- `sprint(se: SExpr) -> Seq<TokenView>`, the mirror printer, plus
  `print_expr(e) == sprint(view_expr(e))`.
- `sdepth(se) -> nat` / `slist_depth(args) -> nat`, the fuel measure, plus
  `sdepth(se) <= sprint(se).len()` for the fuel bound at the headline.
- `sparse(input, fuel) -> (Option<SExpr>, Seq<TokenView>)` and
  `sparse_args(...)`, the mirror parser over the full grammar.
- `lemma_sparse_sprint` / `lemma_sparse_args_sprint`, the roundtrip induction;
  mirror injectivity as its corollary.
- `parse_expr_exec` / `parse_args_exec` (executable, refine `sparse`).
- `print_expr_exec` (executable, `result@ == print_expr(e)`).
- `roundtrip` / `injective` headlines composing the above.

### Grammar deltas versus today's spec parser

- **`Ident` disambiguation.** After an `Ident`, peek: `Ident (` is a function
  call, `Ident . Ident` is a qualified column, bare `Ident` is a column.
- **Boundary predicate.** Extend `prefix_boundary(tail)` to also forbid `tail`
  opening with `OpenParen`, so a bare column is never re-read as a call. Audit
  every recursive call site — all pass `CloseParen`, `Comma`, `Is`,
  `Exclamation`, or an operator token, none of which is `OpenParen`.
- **Comma list.** `sparse_args` / `parse_args_exec` and the comma-list lemma
  come straight from `verified_function_list`.

### Phases (each ends green under `verify.sh`)

- **E0 — mirror scaffold + bridge.** `SExpr`, `view_expr`, `sprint`, and
  `print_expr(e) == sprint(view_expr(e))`; `sdepth` + the length bound. Small.
- **E1 — mirror parser + roundtrip, function-free.** Port `parse_prefix` to
  `sparse` and `lemma_parse_print_prefix` to `lemma_sparse_sprint` over `SExpr`,
  no `Function` yet. Re-establishes current coverage in the mirror; de-risks the
  port. Medium.
- **E2 — add `Function` to the mirror.** The `Ident ( args )` case, `sparse_args`,
  the comma-list lemma, and the boundary extension. The mirror roundtrip now
  covers the whole expression grammar. Medium.
- **E3 — executable parser.** `parse_expr_exec` over the full grammar, building
  `ast::Expression`, refining `sparse` at the `view_expr` level. Largest phase.
- **E4 — executable printer + headline.** `print_expr_exec` (`@ == print_expr`),
  then `roundtrip` and `injective` composing bridge + mirror roundtrip +
  refinement. Medium.

### Risks and decisions

- **Retire or keep the spec parser.** `parse_prefix` / `depth` /
  `lemma_parse_print_prefix` back the statement proofs in
  `verified_production.rs` (`delete_views`) and `verified_statements.rs`. Keep
  both paths until E3 lands, then migrate the statement proofs onto the
  executable parser and delete the spec parser. The migration is the ripple to
  budget, not the expression proof itself.
- **`TokenView` in exec.** Executable comparison needs `derive(Clone, PartialEq)`
  (or match helpers); `String` / `Ident` / `Number` payloads are carried and
  compared by value, never inspected.
- **Executable printer build order.** Building the token `Vec` with a forward
  loop fights `sprint_args`'s `drop_first` recursion (a `take`-vs-`drop_first`
  mismatch). Build by recursion over argument slices matching `drop_first`, or
  prove a prefix-extension lemma; do not stub it.
- **Fuel.** The executable parser passes `fuel = toks.len()`; `sdepth(se) <=
  sprint(se).len()` makes that a safe bound.
- **Trust surface.** Unchanged. No new axioms; `float_trust` stays the only
  trusted boundary.

### Statements follow the same shape

`Statement` carries `Vec`s too (`Insert.values`, `CreateTable.columns`,
`Select.select`/`from`, `Update.set`), so the full statement roundtrip needs the
same mirror + executable treatment, reusing the expression executable parser.
This is the original Phase 3, reframed: it cannot stay on the spec parser either.

## Risks and mitigations

- **Lexer error channel**: `next_token` returns `Result` (invalid bytes). Keep totality on arbitrary
  input; state roundtrip over the well-formed view that `print` produces, where the scan never errors.
  Fix the `PeekStream::next` signature (error state vs `Option<Result<Token>>`) in Phase 0.
- **Byte cursor vs unicode**: syntax is ASCII; UTF-8 only inside string/ident payloads, carried opaque.
  Inspecting inside a payload would be a separate verified UTF-8 step, not a `Chars` axiom.
- **Generics ceremony**: proving through `S: PeekStream` costs more annotation than a monomorphic
  function. If it drags, verify against `TokenStream` directly first (still axiom-free) and generalise
  to the trait in Phase 4; the trait's payoff is multi-implementer reuse, not soundness.

## Logistics

- Module opt-in: one line in `scripts/verus/verify.sh` (`VERIFY_MODULES`).
- Branch: `kg/parser-roundtrip-verify` per `CLAUDE.md` (initials-prefixed, never on `main`).
- Disjoint from `storage/mvcc.rs`: parallel with the MVCC work, zero merge contention.
- Rough total: a proving-out week (Phases 0-1), then ~4-5 weeks for the full expression + statement
  surface and the production cutover; Phase 5 open-ended.

## Prior art (for the colleague)

- Roundtrip/codec style: Narcissus (Coq, ICFP 2019), EverParse/LowParse (F*, USENIX Security 2019),
  Dafny stdlib JSON, AWS Encryption SDK serialisation (Dafny).
- Grammar-correctness style (heavier, not chosen): CompCert C parser via Menhir (Jourdan/Pottier/Leroy,
  ESOP 2012), CoStar (Lasser et al., PLDI 2021), TRX (Koprowski/Binsztok, ESOP 2010),
  Total Parser Combinators (Danielsson, Agda, ICFP 2010).
- Float handling: binary-format verifiers avoid it (floats are bit patterns); textual front-ends
  (CompCert) keep the literal as text and elaborate separately, leaning on Flocq for IEEE reasoning.
