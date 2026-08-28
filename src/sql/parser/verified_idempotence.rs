//! Parser idempotence at the token level, in three phases.
//!
//! The roundtrip proofs in `verified_roundtrip` / `verified_stmt` fix one
//! direction: for a *printable* AST `a`, parsing its canonical print recovers
//! `a` (`parse(print(a)) == a`). This module states the complementary,
//! input-driven property — *parse idempotence*:
//!
//! ```text
//!     for every token sequence `toks`,
//!     if parse(toks) = Some(a) then parse(print(a)) = parse(toks).
//! ```
//!
//! i.e. `parse ∘ print ∘ parse == parse`. Re-printing what you parsed and
//! parsing that again lands exactly where the first parse did. It is proved by
//! composing three phases:
//!
//! - **Phase 1 — parse image is printable.** `parse(toks) = Some(a)` implies
//!   `printable(a)`. Every *structural* case holds: columns, `*`, functions,
//!   and the operator forms build printable nodes whenever their children are
//!   printable, and the integer/keyword/string literal leaves land in the
//!   printable set (`parse_literal_views` yields a non-negative integer or a
//!   `Null`/`Boolean`/`String`). Phase 1 is therefore true on the finite-float
//!   fragment — but *not universally*. A number token such as `1e400` lexes and
//!   parses to `Literal::Float(inf)`, which `printable_literal` rejects (it
//!   demands `is_finite`), because Rust prints `inf` as the text `"inf"`, which
//!   re-lexes as an identifier rather than a number. So the parser can emit an
//!   AST that does not roundtrip, and idempotence genuinely fails there. This
//!   is the same load-bearing finite guard the float-trust decision rests on
//!   (`x.is_finite()` is not decoration). Consequently the `printable`
//!   hypothesis on the Phase-3 headlines below is *necessary*, not a temporary
//!   crutch: it carves out exactly the inputs whose parse the printer can
//!   reproduce. Discharging it for a given input reduces to showing the parsed
//!   literals are finite and in range.
//!
//! - **Phase 2 — printer right-inverts on the printable image.**
//!   `printable(a) ==> parse(print(a)) = (Some(a), [])`. This is exactly the
//!   existing roundtrip lemma (`lemma_sparse_sprint` for expressions,
//!   `lemma_sparse_stmt_sprint` for statements); it is reused verbatim.
//!
//! - **Phase 3 — idempotence.** Compose 1 and 2: parsing `toks` gives
//!   `(Some(a), tail)`; Phase 2 turns `print(a)` back into `(Some(a), [])`; so
//!   the two parses agree (exactly when `tail` is empty, and always on the AST
//!   component).
//!
//! Everything here is axiom-free: the headlines only compose lemmas already
//! proved in the roundtrip modules. Both the expression grammar (`SExpr`) and
//! the full statement grammar (`SStmt`) are covered.

#![allow(dead_code, unused_variables)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::float::FloatBitsProperties;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
// All items used here are ghost (spec/proof); gate the imports behind
// `verus_keep_ghost` so a plain `cargo build` (which strips ghost code) still
// resolves. This module defines no executable functions.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_integer::parse_i64_spec;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_production::{parse_literal_views, printable_literal};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::{
    SExpr, all_printable_se, boundary, lemma_sparse_sprint, printable_se, sdepth, sparse,
    sparse_args, sparse_operator, sprint,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::{
    SStmt, lemma_sparse_stmt_sprint, printable_stmt, sdepth_stmt, sparse_stmt, sprint_stmt,
};
#[allow(unused_imports)]
use super::{Keyword, ast, verified_expression, verified_integer, verified_production};

verus! {

// ---- Phase 1: the parse image is printable on the finite-float fragment ----
//
// `printable_se` over the expression grammar constrains only literal leaves:
// integers must be non-negative and floats must be finite and non-negative
// (everything else is structurally true). A successful parse always yields
// non-negative integers, so the *only* residual is float finiteness. We isolate
// exactly that residual as `finite_floats`, a predicate that constrains float
// leaves and nothing else, and prove `parse(toks) = Some(e) && finite_floats(e)
// ==> printable_se(e)`. On the finite-float fragment (all real SQL number
// literals), the printability side-condition is thereby discharged.

/// Every `Float` literal leaf of `e` is finite and non-negative — matching the
/// `printable_literal` float clause exactly. Integer leaves are unconstrained
/// (a successful parse makes them non-negative for free).
pub open spec fn finite_floats(e: SExpr) -> bool
    decreases e,
{
    match e {
        SExpr::All => true,
        SExpr::Column(_, _) => true,
        SExpr::Literal(l) => match l {
            ast::Literal::Float(x) => x.is_finite_spec() && !x.is_sign_negative_spec(),
            _ => true,
        },
        SExpr::Unary(_, inner) => finite_floats(*inner),
        SExpr::Factorial(inner) => finite_floats(*inner),
        SExpr::Is(inner, _) => finite_floats(*inner),
        SExpr::Binary(_, left, right) => finite_floats(*left) && finite_floats(*right),
        SExpr::Function(_, args) => all_finite_floats(args),
    }
}

pub open spec fn all_finite_floats(args: Seq<SExpr>) -> bool
    decreases args,
{
    if args.len() == 0 {
        true
    } else {
        finite_floats(args[0]) && all_finite_floats(args.drop_first())
    }
}

/// The integer leaf is free: `parse_i64_spec` returns `Some(value as i64)` for a
/// `u64 value <= I64_MAX`, so a successful parse is always non-negative.
pub proof fn parse_i64_nonneg(bytes: Seq<u8>)
    requires
        parse_i64_spec(bytes) is Some,
    ensures
        parse_i64_spec(bytes).unwrap() >= 0,
{
}

/// Phase 1 for expressions. A successful parse whose float leaves are finite is
/// printable. Mutually recursive with the operator/argument parsers, matching
/// `sparse`'s `(fuel, k)` termination measure.
pub proof fn lemma_sparse_printable(input: Seq<TokenView>, fuel: nat)
    requires
        sparse(input, fuel).0 is Some,
        finite_floats(sparse(input, fuel).0.unwrap()),
    ensures
        printable_se(sparse(input, fuel).0.unwrap()),
    decreases fuel, 1nat,
{
    reveal_with_fuel(sparse, 1);
    reveal(printable_se);
    reveal(finite_floats);
    reveal(parse_literal_views);
    let e = sparse(input, fuel).0.unwrap();
    match input[0] {
        TokenView::OpenParen => {
            lemma_sparse_operator_printable(input, fuel);
        },
        TokenView::Asterisk => {},
        TokenView::Ident(name) => {
            if input.len() >= 2 && input[1] == TokenView::OpenParen {
                lemma_sparse_args_printable(input.drop_first().drop_first(), (fuel - 1) as nat);
            }
            // qualified / bare columns are printable unconditionally.
        },
        TokenView::Number(bytes) => {
            // e == Literal(l); Integer case non-negative by parse_i64_nonneg,
            // Float case finite by the finite_floats hypothesis on e.
            if verified_integer::all_digits(bytes) {
                parse_i64_nonneg(bytes);
            }
        },
        _ => {
            // Null / True / False / String literals are printable.
        },
    }
}

pub proof fn lemma_sparse_operator_printable(input: Seq<TokenView>, fuel: nat)
    requires
        sparse_operator(input, fuel).0 is Some,
        finite_floats(sparse_operator(input, fuel).0.unwrap()),
    ensures
        printable_se(sparse_operator(input, fuel).0.unwrap()),
    decreases fuel, 0nat,
{
    reveal_with_fuel(sparse_operator, 1);
    reveal(printable_se);
    reveal(finite_floats);
    match verified_expression::prefix_operator(input[1]) {
        Some(tag) => {
            // Unary(tag, inner): printable_se(inner) from the child parse.
            lemma_sparse_printable(input.drop_first().drop_first(), (fuel - 1) as nat);
        },
        None => {
            let (left_opt, after_left) = sparse(input.drop_first(), (fuel - 1) as nat);
            // The left child is parsed in every surviving branch.
            lemma_sparse_printable(input.drop_first(), (fuel - 1) as nat);
            if after_left.len() > 0 {
                if after_left[0] != TokenView::Exclamation
                    && after_left[0] != TokenView::Keyword(Keyword::Is) {
                    // Binary(tag, left, right): also parse the right child.
                    if verified_expression::binary_from_token(after_left[0]) is Some {
                        lemma_sparse_printable(after_left.drop_first(), (fuel - 1) as nat);
                    }
                }
            }
        },
    }
}

pub proof fn lemma_sparse_args_printable(input: Seq<TokenView>, fuel: nat)
    requires
        sparse_args(input, fuel).0 is Some,
        all_finite_floats(sparse_args(input, fuel).0.unwrap()),
    ensures
        all_printable_se(sparse_args(input, fuel).0.unwrap()),
    decreases fuel, 0nat,
{
    reveal_with_fuel(sparse_args, 1);
    reveal(printable_se);
    if input.len() > 0 && input[0] != TokenView::CloseParen {
        let (e_opt, rest) = sparse(input, (fuel - 1) as nat);
        if e_opt is Some && rest.len() > 0 {
            let e0 = e_opt.unwrap();
            if rest[0] == TokenView::CloseParen {
                // result == seq![e0]
                assert(all_finite_floats(seq![e0]) == (finite_floats(e0)
                    && all_finite_floats(seq![e0].drop_first())));
                assert(seq![e0].drop_first() =~= Seq::<SExpr>::empty());
                lemma_sparse_printable(input, (fuel - 1) as nat);
                assert(all_printable_se(seq![e0]) == (printable_se(e0)
                    && all_printable_se(seq![e0].drop_first())));
            } else if rest[0] == TokenView::Comma {
                // result == seq![e0] + more
                let (more_opt, rest2) = sparse_args(rest.drop_first(), (fuel - 1) as nat);
                if more_opt is Some {
                    let more = more_opt.unwrap();
                    let full = seq![e0] + more;
                    assert(full[0] == e0);
                    assert(full.drop_first() =~= more);
                    // finite_floats distributes over the head/tail split.
                    assert(all_finite_floats(full) == (finite_floats(e0) && all_finite_floats(more)));
                    lemma_sparse_printable(input, (fuel - 1) as nat);
                    lemma_sparse_args_printable(rest.drop_first(), (fuel - 1) as nat);
                    assert(all_printable_se(full) == (printable_se(e0) && all_printable_se(more)));
                }
            }
        }
    }
}

// ---- Phase 3 headlines: idempotence, given the Phase 1 printability side-condition ----
//
// These carry `printable` as a hypothesis. Per Phase 1 (module docs), that
// hypothesis is necessary: the parser can produce non-printable infinite-float
// ASTs (from overflow number tokens like `1e400`) that do not roundtrip, so the
// headlines hold exactly on the finite-float fragment `printable` carves out.
// The composition itself — Phase 2 turning `print(a)` back into `(Some(a), [])`
// — is proved here.

/// Expression idempotence, full-consume form. When `toks` parses to `e` with no
/// leftover, re-parsing `print(e)` reproduces that parse exactly:
/// `parse(print(e)) == parse(toks)`. This is the token-level statement of
/// `parse(prettyprint(ast)) = parse(input)` for a fully-consumed input.
pub proof fn lemma_parse_idempotent_expr(
    input: Seq<TokenView>,
    e: SExpr,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse(input, fuel) == (Some(e), Seq::<TokenView>::empty()),
        printable_se(e),
        fuel2 >= sdepth(e),
    ensures
        sparse(sprint(e), fuel2) == sparse(input, fuel),
{
    // Phase 2: printer right-inverse with the empty tail (boundary(empty) holds).
    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel2);
    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
    // Now sparse(sprint(e), fuel2) == (Some(e), []) == sparse(input, fuel).
}

/// Expression idempotence on the finite-float fragment, with the Phase-1
/// printability side-condition *discharged*. The hypothesis is now the natural,
/// semantically clear `finite_floats(e)` (no overflow floats) rather than
/// `printable_se(e)`; Phase 1 turns it into printability. This is unconditional
/// idempotence for every input whose number literals are finite — i.e. all real
/// SQL.
pub proof fn lemma_parse_idempotent_expr_finite(
    input: Seq<TokenView>,
    e: SExpr,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse(input, fuel) == (Some(e), Seq::<TokenView>::empty()),
        finite_floats(e),
        fuel2 >= sdepth(e),
    ensures
        sparse(sprint(e), fuel2) == sparse(input, fuel),
{
    lemma_sparse_printable(input, fuel);
    lemma_parse_idempotent_expr(input, e, fuel, fuel2);
}

/// Expression idempotence, AST-component form (tail-agnostic). Even when the
/// first parse leaves a leftover `tail`, the AST recovered by re-parsing
/// `print(e)` equals the AST of the original parse.
pub proof fn lemma_parse_idempotent_expr_ast(
    input: Seq<TokenView>,
    e: SExpr,
    tail: Seq<TokenView>,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse(input, fuel) == (Some(e), tail),
        printable_se(e),
        fuel2 >= sdepth(e),
    ensures
        sparse(sprint(e), fuel2).0 == sparse(input, fuel).0,
{
    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel2);
    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
}

/// Statement idempotence, full-consume form: `parse(print(s)) == parse(toks)`
/// when `toks` parses to statement `s` with no leftover. This is the headline
/// property `parse(prettyprint(ast)) = parse(input)` over the whole SQL
/// statement grammar.
pub proof fn lemma_parse_idempotent_stmt(
    input: Seq<TokenView>,
    s: SStmt,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse_stmt(input, fuel) == (Some(s), Seq::<TokenView>::empty()),
        printable_stmt(s),
        fuel2 >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel2) == sparse_stmt(input, fuel),
{
    // Phase 2 for statements: sparse_stmt(sprint_stmt(s), fuel2) == (Some(s), []).
    lemma_sparse_stmt_sprint(s, fuel2);
}

/// Statement idempotence, AST-component form (tail-agnostic).
pub proof fn lemma_parse_idempotent_stmt_ast(
    input: Seq<TokenView>,
    s: SStmt,
    tail: Seq<TokenView>,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse_stmt(input, fuel) == (Some(s), tail),
        printable_stmt(s),
        fuel2 >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel2).0 == sparse_stmt(input, fuel).0,
{
    lemma_sparse_stmt_sprint(s, fuel2);
}

} // verus!
