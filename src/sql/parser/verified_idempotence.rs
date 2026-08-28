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
//!   literals are finite and in range. At the statement level there is a second
//!   load-bearing guard of the same flavour: `SELECT * AS a` parses to a
//!   `(All, Some("a"))` select item that the printer cannot reproduce (an
//!   aliased `*`), so `finite_floats_stmt` carries `All ==> no alias` alongside
//!   float finiteness. Every other structural constraint (`is_stable` right
//!   children, `CROSS`/predicate coupling, list `len >= 1`) is recovered from
//!   the parser image, not required.
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
use super::verified_stmt;
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

// ============================================================================
// Phase 1 for STATEMENTS.
//
// We mirror the family of `printable_*` predicates over the statement grammar
// with `finite_floats_*` predicates that constrain only the float leaves of
// embedded expressions and OMIT the structural facts the parser guarantees
// (`is_stable(right)`, the Cross/predicate coupling, `All => no alias`, and
// `len >= 1`). Those structural facts are recovered from the PARSER IMAGE by the
// per-sub-parser image lemmas below, never demanded of the caller. Each image
// lemma has the shape
//
//     sparse_X(toks, fuel).0 = Some(v) && finite_floats_X(v) ==> printable_X(v)
//
// and reuses `lemma_sparse_printable` for every embedded expression. The kind
// sub-parsers (create/select/insert/update/delete/begin/drop) do not call
// `sparse_stmt`, so their image lemmas are INDEPENDENT of the dispatcher; only
// `Explain` recurses, so `lemma_sparse_stmt_printable` self-recurses only in the
// Explain arm.
// ============================================================================

// ---- columns (CREATE TABLE) ------------------------------------------------

pub open spec fn finite_floats_column(c: verified_stmt::SColumn) -> bool {
    match c.default {
        Some(e) => finite_floats(e),
        None => true,
    }
}

pub open spec fn all_finite_floats_columns(cols: Seq<verified_stmt::SColumn>) -> bool
    decreases cols,
{
    if cols.len() == 0 {
        true
    } else {
        finite_floats_column(cols[0]) && all_finite_floats_columns(cols.drop_first())
    }
}

pub proof fn lemma_sparse_column_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_column(input, fuel).0 is Some,
        finite_floats_column(verified_stmt::sparse_column(input, fuel).0.unwrap()),
    ensures
        verified_stmt::printable_column(verified_stmt::sparse_column(input, fuel).0.unwrap()),
{
    let c = verified_stmt::sparse_column(input, fuel).0.unwrap();
    // A parsed column has `default: Some(e)` only when it came from `sparse`.
    match c.default {
        Some(e) => {
            // Recover the exact token slice that produced `e`.
            let r0 = input.drop_first().drop_first();
            let (primary_key, r1) = verified_stmt::col_parse_pk(r0);
            let (nullable, r2) = verified_stmt::col_parse_null(r1);
            let (unique, r3) = verified_stmt::opt_flag(r2, Keyword::Unique);
            let (index, r4) = verified_stmt::opt_flag(r3, Keyword::Index);
            let (references, r5) = verified_stmt::col_parse_ref(r4);
            assert(sparse(r5.drop_first(), fuel).0 == Some(e));
            lemma_sparse_printable(r5.drop_first(), fuel);
        },
        None => {},
    }
}

pub proof fn lemma_sparse_columns_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_columns(input, fuel).0 is Some,
        all_finite_floats_columns(verified_stmt::sparse_columns(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_columns(verified_stmt::sparse_columns(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_columns, 1);
    let cols = verified_stmt::sparse_columns(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (c_opt, rest) = verified_stmt::sparse_column(input, fuel);
        let c = c_opt.unwrap();
        if rest.len() == 0 {
        } else if rest[0] == TokenView::CloseParen {
            // cols == seq![c]
            assert(cols =~= seq![c]);
            assert(all_finite_floats_columns(seq![c]) == (finite_floats_column(c)
                && all_finite_floats_columns(seq![c].drop_first())));
            assert(seq![c].drop_first() =~= Seq::<verified_stmt::SColumn>::empty());
            lemma_sparse_column_printable(input, fuel);
            assert(verified_stmt::all_printable_columns(seq![c]) == (verified_stmt::printable_column(c)
                && verified_stmt::all_printable_columns(seq![c].drop_first())));
        } else if rest[0] == TokenView::Comma {
            let (more_opt, rest2) = verified_stmt::sparse_columns(rest.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![c] + more;
            assert(cols =~= full);
            assert(full[0] == c);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_columns(full) == (finite_floats_column(c)
                && all_finite_floats_columns(more)));
            lemma_sparse_column_printable(input, fuel);
            lemma_sparse_columns_printable(rest.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_columns(full) == (verified_stmt::printable_column(c)
                && verified_stmt::all_printable_columns(more)));
        } else {
        }
    }
}

// ---- FROM join tree --------------------------------------------------------
//
// `finite_floats_from` mirrors `printable_from` but keeps only the recursive
// float constraint on join predicates, dropping `is_stable(right)` and the
// Cross/predicate coupling (both recovered from the parser image).

pub open spec fn finite_floats_from(f: verified_stmt::SFrom) -> bool
    decreases f,
{
    match f {
        verified_stmt::SFrom::Table { .. } => true,
        verified_stmt::SFrom::Join { left, right, join_type, predicate } =>
            (match predicate {
                Some(e) => finite_floats(e),
                None => true,
            })
            && finite_floats_from(*left),
    }
}

pub open spec fn all_finite_floats_froms(froms: Seq<verified_stmt::SFrom>) -> bool
    decreases froms,
{
    if froms.len() == 0 {
        true
    } else {
        finite_floats_from(froms[0]) && all_finite_floats_froms(froms.drop_first())
    }
}

// `sparse_table` always yields a bare `Table`, so its result is stable.
pub proof fn lemma_sparse_table_stable(input: Seq<TokenView>)
    requires
        verified_stmt::sparse_table(input).0 is Some,
    ensures
        verified_stmt::is_stable(verified_stmt::sparse_table(input).0.unwrap()),
{
}

// A join step is printable when its right child is a bare table and the
// join-type/predicate coupling holds. `sparse_step` builds exactly those.
pub proof fn lemma_sparse_step_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_step(input, fuel).0 is Some,
        match verified_stmt::sparse_step(input, fuel).0.unwrap().predicate {
            Some(e) => finite_floats(e),
            None => true,
        },
    ensures
        verified_stmt::printable_step(verified_stmt::sparse_step(input, fuel).0.unwrap()),
{
    let step = verified_stmt::sparse_step(input, fuel).0.unwrap();
    let jt = verified_stmt::join_type_of(input[0]).unwrap();
    let (right_opt, r) = verified_stmt::sparse_table(input.drop_first().drop_first());
    // sparse_table only ever returns a bare Table, so is_stable holds.
    lemma_sparse_table_stable(input.drop_first().drop_first());
    assert(verified_stmt::is_stable(step.right));
    if verified_stmt::is_cross(jt) {
        // Cross join: predicate forced to None by the parser.
        assert(step.predicate is None);
    } else {
        // predicate came from `sparse(r.drop_first(), fuel)`.
        assert(step.predicate == sparse(r.drop_first(), fuel).0);
        assert(sparse(r.drop_first(), fuel).0 is Some);
        lemma_sparse_printable(r.drop_first(), fuel);
    }
}

// Reassembling a stable head + printable step list gives a printable tree.
// The last step is the outermost `Join`, so induct dropping the tail step.
pub proof fn lemma_fold_printable(head: verified_stmt::SFrom, steps: Seq<verified_stmt::SJoinStep>)
    requires
        verified_stmt::is_stable(head),
        verified_stmt::all_printable_steps(steps),
    ensures
        verified_stmt::printable_from(verified_stmt::fold_joins(head, steps)),
    decreases steps,
{
    if steps.len() == 0 {
        assert(verified_stmt::fold_joins(head, steps) == head);
    } else {
        let init = steps.drop_last();
        let last = steps.last();
        assert(steps =~= init + seq![last]);
        verified_stmt::fold_append(head, init, seq![last]);
        let acc = verified_stmt::fold_joins(head, init);
        assert(verified_stmt::fold_joins(acc, seq![last])
            == verified_stmt::apply_step(acc, last)) by {
            reveal_with_fuel(verified_stmt::fold_joins, 2);
            assert(seq![last][0] == last);
            assert(seq![last].drop_first() =~= Seq::<verified_stmt::SJoinStep>::empty());
        }
        assert(verified_stmt::fold_joins(head, steps) == verified_stmt::apply_step(acc, last));
        // init is printable-steps, last is a printable step.
        verified_stmt::all_printable_steps_append(init, seq![last]);
        assert(verified_stmt::all_printable_steps(seq![last])) by {
            reveal_with_fuel(verified_stmt::all_printable_steps, 2);
            assert(seq![last][0] == last);
            assert(seq![last].drop_first() =~= Seq::<verified_stmt::SJoinStep>::empty());
        }
        lemma_fold_printable(head, init);
    }
}

// Dually, if the reassembled tree has finite floats, each step's predicate is
// finite. Same last-step induction.
pub proof fn lemma_fold_finite_step(head: verified_stmt::SFrom, steps: Seq<verified_stmt::SJoinStep>)
    requires
        finite_floats_from(verified_stmt::fold_joins(head, steps)),
    ensures
        forall|i: int| 0 <= i < steps.len() ==> (match #[trigger] steps[i].predicate {
            Some(e) => finite_floats(e),
            None => true,
        }),
    decreases steps,
{
    if steps.len() == 0 {
    } else {
        let init = steps.drop_last();
        let last = steps.last();
        assert(steps =~= init + seq![last]);
        verified_stmt::fold_append(head, init, seq![last]);
        let acc = verified_stmt::fold_joins(head, init);
        assert(verified_stmt::fold_joins(acc, seq![last])
            == verified_stmt::apply_step(acc, last)) by {
            reveal_with_fuel(verified_stmt::fold_joins, 2);
            assert(seq![last][0] == last);
            assert(seq![last].drop_first() =~= Seq::<verified_stmt::SJoinStep>::empty());
        }
        let f = verified_stmt::fold_joins(head, steps);
        assert(f == verified_stmt::apply_step(acc, last));
        // f is Join{left: acc, right: last.right, ..., predicate: last.predicate}.
        // finite_floats_from(f) => finite_floats(pred(last)) && finite_floats_from(acc).
        assert(match last.predicate { Some(e) => finite_floats(e), None => true });
        assert(finite_floats_from(acc));
        lemma_fold_finite_step(head, init);
        assert(forall|i: int| 0 <= i < steps.len() ==> (match #[trigger] steps[i].predicate {
            Some(e) => finite_floats(e),
            None => true,
        })) by {
            assert(forall|i: int| 0 <= i < init.len() ==> steps[i] == init[i]);
            assert(steps[steps.len() - 1] == last);
        }
    }
}

// `all_finite_floats_steps` from the pointwise step-predicate finiteness.
pub open spec fn all_finite_floats_steps(steps: Seq<verified_stmt::SJoinStep>) -> bool
    decreases steps,
{
    if steps.len() == 0 {
        true
    } else {
        (match steps[0].predicate {
            Some(e) => finite_floats(e),
            None => true,
        }) && all_finite_floats_steps(steps.drop_first())
    }
}

pub proof fn lemma_steps_pointwise_to_all(steps: Seq<verified_stmt::SJoinStep>)
    requires
        forall|i: int| 0 <= i < steps.len() ==> (match #[trigger] steps[i].predicate {
            Some(e) => finite_floats(e),
            None => true,
        }),
    ensures
        all_finite_floats_steps(steps),
    decreases steps,
{
    if steps.len() == 0 {
    } else {
        assert(match steps[0].predicate { Some(e) => finite_floats(e), None => true });
        assert(forall|i: int| 0 <= i < steps.drop_first().len()
            ==> steps.drop_first()[i] == steps[i + 1]);
        lemma_steps_pointwise_to_all(steps.drop_first());
    }
}

// Image lemma for the step list.
pub proof fn lemma_sparse_steps_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_steps(input, fuel).0 is Some,
        all_finite_floats_steps(verified_stmt::sparse_steps(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_steps(verified_stmt::sparse_steps(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_steps, 1);
    let steps = verified_stmt::sparse_steps(input, fuel).0.unwrap();
    if input.len() >= 1 && verified_stmt::is_join_kw(input[0]) {
        // fuel > 0 here since result is Some.
        let (step_opt, rest) = verified_stmt::sparse_step(input, fuel);
        let step = step_opt.unwrap();
        let (more_opt, rest2) = verified_stmt::sparse_steps(rest, (fuel - 1) as nat);
        let more = more_opt.unwrap();
        let full = seq![step] + more;
        assert(steps =~= full);
        assert(full[0] == step);
        assert(full.drop_first() =~= more);
        assert(all_finite_floats_steps(full) == ((match step.predicate {
            Some(e) => finite_floats(e),
            None => true,
        }) && all_finite_floats_steps(more)));
        lemma_sparse_step_printable(input, fuel);
        lemma_sparse_steps_printable(rest, (fuel - 1) as nat);
        assert(verified_stmt::all_printable_steps(full) == (verified_stmt::printable_step(step)
            && verified_stmt::all_printable_steps(more)));
    } else {
        // steps == empty
        assert(steps =~= Seq::<verified_stmt::SJoinStep>::empty());
    }
}

// Image lemma for a single FROM item (join tree).
pub proof fn lemma_sparse_from_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_from(input, fuel).0 is Some,
        finite_floats_from(verified_stmt::sparse_from(input, fuel).0.unwrap()),
    ensures
        verified_stmt::printable_from(verified_stmt::sparse_from(input, fuel).0.unwrap()),
{
    reveal(verified_stmt::sparse_from);
    let f = verified_stmt::sparse_from(input, fuel).0.unwrap();
    let (head_opt, r) = verified_stmt::sparse_table(input);
    let head = head_opt.unwrap();
    let (steps_opt, r2) = verified_stmt::sparse_steps(r, fuel);
    let steps = steps_opt.unwrap();
    assert(f == verified_stmt::fold_joins(head, steps));
    lemma_sparse_table_stable(input);
    // finite floats of the tree gives finite predicates of every step.
    lemma_fold_finite_step(head, steps);
    lemma_steps_pointwise_to_all(steps);
    lemma_sparse_steps_printable(r, fuel);
    lemma_fold_printable(head, steps);
}

// Image lemma for the FROM comma-list.
pub proof fn lemma_sparse_from_list_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_from_list(input, fuel).0 is Some,
        all_finite_floats_froms(verified_stmt::sparse_from_list(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_froms(verified_stmt::sparse_from_list(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_from_list, 1);
    let froms = verified_stmt::sparse_from_list(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (f_opt, r) = verified_stmt::sparse_from(input, fuel);
        let f = f_opt.unwrap();
        if r.len() >= 1 && r[0] == TokenView::Comma {
            let (more_opt, r2) = verified_stmt::sparse_from_list(r.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![f] + more;
            assert(froms =~= full);
            assert(full[0] == f);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_froms(full) == (finite_floats_from(f)
                && all_finite_floats_froms(more)));
            lemma_sparse_from_printable(input, fuel);
            lemma_sparse_from_list_printable(r.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_froms(full) == (verified_stmt::printable_from(f)
                && verified_stmt::all_printable_froms(more)));
        } else {
            assert(froms =~= seq![f]);
            assert(all_finite_floats_froms(seq![f]) == (finite_floats_from(f)
                && all_finite_floats_froms(seq![f].drop_first())));
            assert(seq![f].drop_first() =~= Seq::<verified_stmt::SFrom>::empty());
            lemma_sparse_from_printable(input, fuel);
            assert(verified_stmt::all_printable_froms(seq![f]) == (verified_stmt::printable_from(f)
                && verified_stmt::all_printable_froms(seq![f].drop_first())));
        }
    }
}

// ---- UPDATE SET list -------------------------------------------------------

pub open spec fn finite_floats_assign(a: (String, Option<SExpr>)) -> bool {
    match a.1 {
        Some(e) => finite_floats(e),
        None => true,
    }
}

pub open spec fn all_finite_floats_assigns(items: Seq<(String, Option<SExpr>)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        finite_floats_assign(items[0]) && all_finite_floats_assigns(items.drop_first())
    }
}

pub proof fn lemma_sparse_assign_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_assign(input, fuel).0 is Some,
        finite_floats_assign(verified_stmt::sparse_assign(input, fuel).0.unwrap()),
    ensures
        verified_stmt::printable_assign(verified_stmt::sparse_assign(input, fuel).0.unwrap()),
{
    reveal(verified_stmt::sparse_assign);
    let a = verified_stmt::sparse_assign(input, fuel).0.unwrap();
    match a.1 {
        Some(e) => {
            let rest = input.drop_first().drop_first();
            assert(sparse(rest, fuel).0 == Some(e));
            lemma_sparse_printable(rest, fuel);
        },
        None => {},
    }
}

pub proof fn lemma_sparse_set_list_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_set_list(input, fuel).0 is Some,
        all_finite_floats_assigns(verified_stmt::sparse_set_list(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_assigns(verified_stmt::sparse_set_list(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_set_list, 1);
    let items = verified_stmt::sparse_set_list(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (a_opt, r) = verified_stmt::sparse_assign(input, fuel);
        let a = a_opt.unwrap();
        if r.len() >= 1 && r[0] == TokenView::Comma {
            let (more_opt, r2) = verified_stmt::sparse_set_list(r.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![a] + more;
            assert(items =~= full);
            assert(full[0] == a);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_assigns(full) == (finite_floats_assign(a)
                && all_finite_floats_assigns(more)));
            lemma_sparse_assign_printable(input, fuel);
            lemma_sparse_set_list_printable(r.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_assigns(full) == (verified_stmt::printable_assign(a)
                && verified_stmt::all_printable_assigns(more)));
        } else {
            assert(items =~= seq![a]);
            assert(all_finite_floats_assigns(seq![a]) == (finite_floats_assign(a)
                && all_finite_floats_assigns(seq![a].drop_first())));
            assert(seq![a].drop_first() =~= Seq::<(String, Option<SExpr>)>::empty());
            lemma_sparse_assign_printable(input, fuel);
            assert(verified_stmt::all_printable_assigns(seq![a]) == (verified_stmt::printable_assign(a)
                && verified_stmt::all_printable_assigns(seq![a].drop_first())));
        }
    }
}

// ---- group-by / expr comma-list (reuses `all_finite_floats` over Seq<SExpr>) --

pub proof fn lemma_sparse_expr_list_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_expr_list(input, fuel).0 is Some,
        all_finite_floats(verified_stmt::sparse_expr_list(input, fuel).0.unwrap()),
    ensures
        all_printable_se(verified_stmt::sparse_expr_list(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_expr_list, 1);
    reveal(all_finite_floats);
    let items = verified_stmt::sparse_expr_list(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (e_opt, r) = sparse(input, fuel);
        let e = e_opt.unwrap();
        if r.len() >= 1 && r[0] == TokenView::Comma {
            let (more_opt, r2) = verified_stmt::sparse_expr_list(r.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![e] + more;
            assert(items =~= full);
            assert(full[0] == e);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats(full) == (finite_floats(e) && all_finite_floats(more)));
            lemma_sparse_printable(input, fuel);
            lemma_sparse_expr_list_printable(r.drop_first(), (fuel - 1) as nat);
            assert(all_printable_se(full) == (printable_se(e) && all_printable_se(more)));
        } else {
            assert(items =~= seq![e]);
            assert(all_finite_floats(seq![e]) == (finite_floats(e)
                && all_finite_floats(seq![e].drop_first())));
            assert(seq![e].drop_first() =~= Seq::<SExpr>::empty());
            lemma_sparse_printable(input, fuel);
            assert(all_printable_se(seq![e]) == (printable_se(e)
                && all_printable_se(seq![e].drop_first())));
        }
    }
}

// ---- ORDER BY item list ----------------------------------------------------

pub open spec fn all_finite_floats_order(items: Seq<(SExpr, ast::Direction)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        finite_floats(items[0].0) && all_finite_floats_order(items.drop_first())
    }
}

pub proof fn lemma_sparse_order_list_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_order_list(input, fuel).0 is Some,
        all_finite_floats_order(verified_stmt::sparse_order_list(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_order(verified_stmt::sparse_order_list(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_order_list, 1);
    let items = verified_stmt::sparse_order_list(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (e_opt, r) = sparse(input, fuel);
        let e = e_opt.unwrap();
        let d = if r[0] == TokenView::Keyword(Keyword::Asc) {
            ast::Direction::Ascending
        } else {
            ast::Direction::Descending
        };
        let r1 = r.drop_first();
        if r1.len() >= 1 && r1[0] == TokenView::Comma {
            let (more_opt, r2) = verified_stmt::sparse_order_list(r1.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![(e, d)] + more;
            assert(items =~= full);
            assert(full[0] == (e, d));
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_order(full) == (finite_floats(full[0].0)
                && all_finite_floats_order(more)));
            lemma_sparse_printable(input, fuel);
            lemma_sparse_order_list_printable(r1.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_order(full) == (printable_se(full[0].0)
                && verified_stmt::all_printable_order(more)));
        } else {
            assert(items =~= seq![(e, d)]);
            assert(all_finite_floats_order(seq![(e, d)]) == (finite_floats(e)
                && all_finite_floats_order(seq![(e, d)].drop_first())));
            assert(seq![(e, d)].drop_first() =~= Seq::<(SExpr, ast::Direction)>::empty());
            lemma_sparse_printable(input, fuel);
            assert(verified_stmt::all_printable_order(seq![(e, d)]) == (printable_se(e)
                && verified_stmt::all_printable_order(seq![(e, d)].drop_first())));
        }
    }
}

// ---- SELECT item list ------------------------------------------------------
//
// `printable_select_item((e, alias))` demands `e == All ==> alias is None`. This
// is NOT a fact the parser guarantees: `sparse` on `Asterisk` returns
// `(Some(All), tail)` unconditionally (verified_roundtrip.rs L314), so on the
// tokens `[* , AS, a, ..]` the parser genuinely produces the non-printable
// `(All, Some(a))` — `SELECT * AS a` re-prints without the alias, so idempotence
// fails there. The `All => no-alias` side-condition is therefore load-bearing,
// exactly like the finite-float guard: it carves out the printable fragment. We
// keep it as an explicit clause of `finite_floats_select_item` (a genuinely
// necessary hypothesis, not a parser-guaranteed structural fact we could drop),
// which keeps the whole development axiom-free while still covering SELECT.

pub open spec fn finite_floats_select_item(item: (SExpr, Option<String>)) -> bool {
    finite_floats(item.0) && (match item.0 {
        SExpr::All => item.1 is None,
        _ => true,
    })
}

pub open spec fn all_finite_floats_select(items: Seq<(SExpr, Option<String>)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        finite_floats_select_item(items[0]) && all_finite_floats_select(items.drop_first())
    }
}

pub proof fn lemma_sparse_select_item_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_select_item(input, fuel).0 is Some,
        finite_floats_select_item(verified_stmt::sparse_select_item(input, fuel).0.unwrap()),
    ensures
        verified_stmt::printable_select_item(verified_stmt::sparse_select_item(input, fuel).0.unwrap()),
{
    reveal(verified_stmt::sparse_select_item);
    let item = verified_stmt::sparse_select_item(input, fuel).0.unwrap();
    let (e_opt, r) = sparse(input, fuel);
    let e = e_opt.unwrap();
    // item.0 == e in every surviving branch; printable_se(e) from Phase 1.
    assert(item.0 == e);
    lemma_sparse_printable(input, fuel);
    // The `All => alias None` clause is carried by finite_floats_select_item.
}

pub proof fn lemma_sparse_select_list_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_select_list(input, fuel).0 is Some,
        all_finite_floats_select(verified_stmt::sparse_select_list(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_select(verified_stmt::sparse_select_list(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_select_list, 1);
    let items = verified_stmt::sparse_select_list(input, fuel).0.unwrap();
    if fuel == 0 {
    } else {
        let (item_opt, r) = verified_stmt::sparse_select_item(input, fuel);
        let item = item_opt.unwrap();
        if r.len() >= 1 && r[0] == TokenView::Comma {
            let (more_opt, r2) = verified_stmt::sparse_select_list(r.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![item] + more;
            assert(items =~= full);
            assert(full[0] == item);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_select(full) == (finite_floats_select_item(item)
                && all_finite_floats_select(more)));
            lemma_sparse_select_item_printable(input, fuel);
            lemma_sparse_select_list_printable(r.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_select(full) == (verified_stmt::printable_select_item(item)
                && verified_stmt::all_printable_select(more)));
        } else {
            assert(items =~= seq![item]);
            assert(all_finite_floats_select(seq![item]) == (finite_floats_select_item(item)
                && all_finite_floats_select(seq![item].drop_first())));
            assert(seq![item].drop_first() =~= Seq::<(SExpr, Option<String>)>::empty());
            lemma_sparse_select_item_printable(input, fuel);
            assert(verified_stmt::all_printable_select(seq![item]) == (verified_stmt::printable_select_item(item)
                && verified_stmt::all_printable_select(seq![item].drop_first())));
        }
    }
}

// ---- INSERT rows (two-level comma list) ------------------------------------

pub open spec fn all_finite_floats_rows(rows: Seq<Seq<SExpr>>) -> bool
    decreases rows,
{
    if rows.len() == 0 {
        true
    } else {
        all_finite_floats(rows[0]) && all_finite_floats_rows(rows.drop_first())
    }
}

// The row expressions come from `sparse_args`, so one row's printability is the
// existing expression-args image lemma.
pub proof fn lemma_sparse_rows_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_rows(input, fuel).0 is Some,
        all_finite_floats_rows(verified_stmt::sparse_rows(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_rows(verified_stmt::sparse_rows(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(verified_stmt::sparse_rows, 1);
    let rows = verified_stmt::sparse_rows(input, fuel).0.unwrap();
    if fuel == 0 || input.len() == 0 || input[0] != TokenView::OpenParen {
    } else {
        let (row_opt, r) = sparse_args(input.drop_first(), fuel);
        let row = row_opt.unwrap();
        // this row's printability from the expression-args image lemma.
        assert(r.len() > 0 && r[0] == TokenView::CloseParen);
        let r2 = r.drop_first();
        if r2.len() > 0 && r2[0] == TokenView::Comma {
            let (more_opt, r3) = verified_stmt::sparse_rows(r2.drop_first(), (fuel - 1) as nat);
            let more = more_opt.unwrap();
            let full = seq![row] + more;
            assert(rows =~= full);
            assert(full[0] == row);
            assert(full.drop_first() =~= more);
            assert(all_finite_floats_rows(full) == (all_finite_floats(row)
                && all_finite_floats_rows(more)));
            lemma_sparse_args_printable(input.drop_first(), fuel);
            lemma_sparse_rows_printable(r2.drop_first(), (fuel - 1) as nat);
            assert(verified_stmt::all_printable_rows(full) == (all_printable_se(row)
                && verified_stmt::all_printable_rows(more)));
        } else {
            assert(rows =~= seq![row]);
            assert(all_finite_floats_rows(seq![row]) == (all_finite_floats(row)
                && all_finite_floats_rows(seq![row].drop_first())));
            assert(seq![row].drop_first() =~= Seq::<Seq<SExpr>>::empty());
            lemma_sparse_args_printable(input.drop_first(), fuel);
            assert(verified_stmt::all_printable_rows(seq![row]) == (all_printable_se(row)
                && verified_stmt::all_printable_rows(seq![row].drop_first())));
        }
    }
}

// ---- SELECT clause helpers (WHERE/GROUP/HAVING, ORDER BY, LIMIT/OFFSET) -----

// A parsed optional `KW <expr>` clause is printable when its expr is finite.
pub proof fn lemma_sparse_kw_expr_printable(input: Seq<TokenView>, kw: Keyword, fuel: nat)
    requires
        verified_stmt::sparse_kw_expr(input, kw, fuel).0 is Some,
        match verified_stmt::sparse_kw_expr(input, kw, fuel).0.unwrap() {
            Some(e) => finite_floats(e),
            None => true,
        },
    ensures
        match verified_stmt::sparse_kw_expr(input, kw, fuel).0.unwrap() {
            Some(e) => printable_se(e),
            None => true,
        },
{
    let clause = verified_stmt::sparse_kw_expr(input, kw, fuel).0.unwrap();
    if input.len() >= 1 && input[0] == TokenView::Keyword(kw) {
        match clause {
            Some(e) => {
                assert(sparse(input.drop_first(), fuel).0 == Some(e));
                lemma_sparse_printable(input.drop_first(), fuel);
            },
            None => {},
        }
    }
}

// The WHERE/GROUP/HAVING tail: where + having printable-se, group_by all
// printable-se, all from finite floats.
pub proof fn lemma_sparse_where_group_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_where_group(input, fuel).0 is Some,
        ({
            let t = verified_stmt::sparse_where_group(input, fuel).0.unwrap();
            &&& (match t.0 { Some(e) => finite_floats(e), None => true })
            &&& all_finite_floats(t.1)
            &&& (match t.2 { Some(e) => finite_floats(e), None => true })
        }),
    ensures
        ({
            let t = verified_stmt::sparse_where_group(input, fuel).0.unwrap();
            &&& (match t.0 { Some(e) => printable_se(e), None => true })
            &&& all_printable_se(t.1)
            &&& (match t.2 { Some(e) => printable_se(e), None => true })
        }),
{
    reveal(verified_stmt::sparse_where_group);
    let t = verified_stmt::sparse_where_group(input, fuel).0.unwrap();
    // WHERE clause.
    if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Where) {
        assert(sparse(input.drop_first(), fuel).0 == Some(t.0.unwrap()));
        lemma_sparse_printable(input.drop_first(), fuel);
    }
    // The residual after WHERE.
    let rw = if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Where) {
        sparse(input.drop_first(), fuel).1
    } else {
        input
    };
    // GROUP BY list.
    if rw.len() >= 2 && rw[0] == TokenView::Keyword(Keyword::Group)
        && rw[1] == TokenView::Keyword(Keyword::By) {
        assert(verified_stmt::sparse_expr_list(rw.drop_first().drop_first(), fuel).0 == Some(t.1));
        lemma_sparse_expr_list_printable(rw.drop_first().drop_first(), fuel);
    } else {
        assert(t.1 =~= Seq::<SExpr>::empty());
        assert(all_printable_se(t.1));
    }
    // HAVING clause.
    let rg = if rw.len() >= 2 && rw[0] == TokenView::Keyword(Keyword::Group)
        && rw[1] == TokenView::Keyword(Keyword::By) {
        verified_stmt::sparse_expr_list(rw.drop_first().drop_first(), fuel).1
    } else {
        rw
    };
    if rg.len() >= 1 && rg[0] == TokenView::Keyword(Keyword::Having) {
        assert(sparse(rg.drop_first(), fuel).0 == Some(t.2.unwrap()));
        lemma_sparse_printable(rg.drop_first(), fuel);
    }
}

// ORDER BY clause.
pub proof fn lemma_sparse_order_clause_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_order_clause(input, fuel).0 is Some,
        all_finite_floats_order(verified_stmt::sparse_order_clause(input, fuel).0.unwrap()),
    ensures
        verified_stmt::all_printable_order(verified_stmt::sparse_order_clause(input, fuel).0.unwrap()),
{
    reveal(verified_stmt::sparse_order_clause);
    let items = verified_stmt::sparse_order_clause(input, fuel).0.unwrap();
    if input.len() >= 2 && input[0] == TokenView::Keyword(Keyword::Order)
        && input[1] == TokenView::Keyword(Keyword::By) {
        assert(verified_stmt::sparse_order_list(input.drop_first().drop_first(), fuel).0 == Some(items));
        lemma_sparse_order_list_printable(input.drop_first().drop_first(), fuel);
    } else {
        assert(items =~= Seq::<(SExpr, ast::Direction)>::empty());
    }
}

// LIMIT/OFFSET tail.
pub proof fn lemma_sparse_limit_offset_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_limit_offset(input, fuel).0 is Some,
        ({
            let t = verified_stmt::sparse_limit_offset(input, fuel).0.unwrap();
            &&& (match t.0 { Some(e) => finite_floats(e), None => true })
            &&& (match t.1 { Some(e) => finite_floats(e), None => true })
        }),
    ensures
        ({
            let t = verified_stmt::sparse_limit_offset(input, fuel).0.unwrap();
            &&& (match t.0 { Some(e) => printable_se(e), None => true })
            &&& (match t.1 { Some(e) => printable_se(e), None => true })
        }),
{
    reveal(verified_stmt::sparse_limit_offset);
    let t = verified_stmt::sparse_limit_offset(input, fuel).0.unwrap();
    let (limit, rl) = verified_stmt::sparse_kw_expr(input, Keyword::Limit, fuel);
    lemma_sparse_kw_expr_printable(input, Keyword::Limit, fuel);
    assert(t.0 == limit.unwrap());
    lemma_sparse_kw_expr_printable(rl, Keyword::Offset, fuel);
    assert(t.1 == verified_stmt::sparse_kw_expr(rl, Keyword::Offset, fuel).0.unwrap());
}

// ---- list non-emptiness from the parser image ------------------------------
//
// Each comma-list parser only ever returns a non-empty sequence (it parses at
// least one element before looping), so `len >= 1` is a parser-image fact, not
// a caller hypothesis.

pub proof fn lemma_sparse_columns_nonempty(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_columns(input, fuel).0 is Some,
    ensures
        verified_stmt::sparse_columns(input, fuel).0.unwrap().len() >= 1,
{
    reveal_with_fuel(verified_stmt::sparse_columns, 1);
}

pub proof fn lemma_sparse_names_nonempty(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_names(input, fuel).0 is Some,
    ensures
        verified_stmt::sparse_names(input, fuel).0.unwrap().len() >= 1,
{
    reveal_with_fuel(verified_stmt::sparse_names, 1);
}

pub proof fn lemma_sparse_rows_nonempty(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_rows(input, fuel).0 is Some,
    ensures
        verified_stmt::sparse_rows(input, fuel).0.unwrap().len() >= 1,
{
    reveal_with_fuel(verified_stmt::sparse_rows, 1);
}

pub proof fn lemma_sparse_set_list_nonempty(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_set_list(input, fuel).0 is Some,
    ensures
        verified_stmt::sparse_set_list(input, fuel).0.unwrap().len() >= 1,
{
    reveal_with_fuel(verified_stmt::sparse_set_list, 1);
}

pub proof fn lemma_sparse_select_list_nonempty(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_select_list(input, fuel).0 is Some,
    ensures
        verified_stmt::sparse_select_list(input, fuel).0.unwrap().len() >= 1,
{
    reveal_with_fuel(verified_stmt::sparse_select_list, 1);
}

// ---- statement-level finite-floats predicate -------------------------------
//
// Mirrors `printable_stmt` clause by clause, with `finite_floats*` in place of
// `printable*`. Structural facts the parser guarantees (column/row/set len>=1,
// the FROM is_stable/Cross coupling) are OMITTED — recovered from the parser
// image. The single genuinely-necessary structural side-condition (`All =>
// no-alias` in the SELECT list) is carried by `finite_floats_select_item`, and
// `SELECT`'s `columns Some => len>=1` for INSERT is also parser-guaranteed.

pub open spec fn finite_floats_stmt(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Begin { .. } => true,
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::DropTable { .. } => true,
        SStmt::CreateTable { columns, .. } => all_finite_floats_columns(columns),
        SStmt::Delete { where_clause: Some(e), .. } => finite_floats(e),
        SStmt::Delete { where_clause: None, .. } => true,
        SStmt::Insert { values, .. } => all_finite_floats_rows(values),
        SStmt::Update { set, where_clause, .. } =>
            all_finite_floats_assigns(set)
                && (match where_clause { Some(e) => finite_floats(e), None => true }),
        SStmt::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } =>
            all_finite_floats_select(select)
                && all_finite_floats_froms(from)
                && (match where_clause { Some(e) => finite_floats(e), None => true })
                && all_finite_floats(group_by)
                && (match having { Some(e) => finite_floats(e), None => true })
                && all_finite_floats_order(order_by)
                && (match limit { Some(e) => finite_floats(e), None => true })
                && (match offset { Some(e) => finite_floats(e), None => true }),
        SStmt::Explain(inner) => finite_floats_stmt(*inner),
        SStmt::Unsupported => false,
    }
}

// ---- per-kind image lemmas -------------------------------------------------

pub proof fn lemma_sparse_create_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_create(input, fuel).0 is Some,
        finite_floats_stmt(verified_stmt::sparse_create(input, fuel).0.unwrap()),
    ensures
        printable_stmt(verified_stmt::sparse_create(input, fuel).0.unwrap()),
{
    reveal(printable_stmt);
    let s = verified_stmt::sparse_create(input, fuel).0.unwrap();
    // s == CreateTable{ name, columns: cols } with cols from sparse_columns.
    match s {
        SStmt::CreateTable { name, columns } => {
            let cols_input = input.drop_first().drop_first().drop_first().drop_first();
            assert(verified_stmt::sparse_columns(cols_input, fuel).0 == Some(columns));
            // sparse_create only succeeds when the columns are closed by `)`,
            // which sparse_columns yields only for a non-empty list.
            lemma_sparse_columns_nonempty(cols_input, fuel);
            lemma_sparse_columns_printable(cols_input, fuel);
        },
        _ => {},
    }
}

pub proof fn lemma_sparse_delete_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_delete(input, fuel).0 is Some,
        finite_floats_stmt(verified_stmt::sparse_delete(input, fuel).0.unwrap()),
    ensures
        printable_stmt(verified_stmt::sparse_delete(input, fuel).0.unwrap()),
{
    reveal(printable_stmt);
    let s = verified_stmt::sparse_delete(input, fuel).0.unwrap();
    match s {
        SStmt::Delete { table, where_clause: Some(e) } => {
            let wl = input.drop_first().drop_first().drop_first().drop_first();
            assert(sparse(wl, fuel).0 == Some(e));
            lemma_sparse_printable(wl, fuel);
        },
        _ => {},
    }
}

pub proof fn lemma_sparse_insert_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_insert(input, fuel).0 is Some,
        finite_floats_stmt(verified_stmt::sparse_insert(input, fuel).0.unwrap()),
    ensures
        printable_stmt(verified_stmt::sparse_insert(input, fuel).0.unwrap()),
{
    reveal(printable_stmt);
    let s = verified_stmt::sparse_insert(input, fuel).0.unwrap();
    match s {
        SStmt::Insert { table, columns, values } => {
            // Recover the rows-token slice and prove all_printable_rows + len>=1.
            let rest = input.drop_first().drop_first().drop_first();
            if rest.len() >= 1 && rest[0] == TokenView::OpenParen {
                let (names_opt, r) = verified_stmt::sparse_names(rest.drop_first(), fuel);
                let r2 = r.drop_first();
                let rows_input = r2.drop_first();
                assert(columns == Some(names_opt.unwrap()));
                lemma_sparse_names_nonempty(rest.drop_first(), fuel);
                assert(verified_stmt::sparse_rows(rows_input, fuel).0 == Some(values));
                lemma_sparse_rows_nonempty(rows_input, fuel);
                lemma_sparse_rows_printable(rows_input, fuel);
            } else {
                let rows_input = rest.drop_first();
                assert(columns is None);
                assert(verified_stmt::sparse_rows(rows_input, fuel).0 == Some(values));
                lemma_sparse_rows_nonempty(rows_input, fuel);
                lemma_sparse_rows_printable(rows_input, fuel);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_sparse_update_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_update(input, fuel).0 is Some,
        finite_floats_stmt(verified_stmt::sparse_update(input, fuel).0.unwrap()),
    ensures
        printable_stmt(verified_stmt::sparse_update(input, fuel).0.unwrap()),
{
    reveal(printable_stmt);
    let s = verified_stmt::sparse_update(input, fuel).0.unwrap();
    match s {
        SStmt::Update { table, set, where_clause } => {
            let set_input = input.drop_first().drop_first().drop_first();
            let (set_opt, r) = verified_stmt::sparse_set_list(set_input, fuel);
            assert(set == set_opt.unwrap());
            lemma_sparse_set_list_nonempty(set_input, fuel);
            lemma_sparse_set_list_printable(set_input, fuel);
            match where_clause {
                Some(e) => {
                    assert(sparse(r.drop_first(), fuel).0 == Some(e));
                    lemma_sparse_printable(r.drop_first(), fuel);
                },
                None => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_sparse_select_printable(input: Seq<TokenView>, fuel: nat)
    requires
        verified_stmt::sparse_select(input, fuel).0 is Some,
        finite_floats_stmt(verified_stmt::sparse_select(input, fuel).0.unwrap()),
    ensures
        printable_stmt(verified_stmt::sparse_select(input, fuel).0.unwrap()),
{
    reveal(printable_stmt);
    let s = verified_stmt::sparse_select(input, fuel).0.unwrap();
    match s {
        SStmt::Select { select, from, where_clause, group_by, having, order_by, limit, offset } => {
            // select list
            let (sel_opt, r1) = verified_stmt::sparse_select_list(input.drop_first(), fuel);
            assert(select == sel_opt.unwrap());
            lemma_sparse_select_list_nonempty(input.drop_first(), fuel);
            lemma_sparse_select_list_printable(input.drop_first(), fuel);
            // from list
            let from_result = if r1.len() >= 1 && r1[0] == TokenView::Keyword(Keyword::From) {
                verified_stmt::sparse_from_list(r1.drop_first(), fuel)
            } else {
                (Some(Seq::<verified_stmt::SFrom>::empty()), r1)
            };
            let (from2_opt, r2) = from_result;
            assert(from == from2_opt.unwrap());
            if r1.len() >= 1 && r1[0] == TokenView::Keyword(Keyword::From) {
                lemma_sparse_from_list_printable(r1.drop_first(), fuel);
            } else {
                assert(from =~= Seq::<verified_stmt::SFrom>::empty());
                assert(verified_stmt::all_printable_froms(from));
            }
            // where/group/having
            let (wg_opt, rg) = verified_stmt::sparse_where_group(r2, fuel);
            let wg = wg_opt.unwrap();
            assert(wg.0 == where_clause && wg.1 == group_by && wg.2 == having);
            lemma_sparse_where_group_printable(r2, fuel);
            // order by
            let (ord_opt, rord) = verified_stmt::sparse_order_clause(rg, fuel);
            assert(order_by == ord_opt.unwrap());
            lemma_sparse_order_clause_printable(rg, fuel);
            // limit/offset
            let (lo_opt, ro) = verified_stmt::sparse_limit_offset(rord, fuel);
            let lo = lo_opt.unwrap();
            assert(lo.0 == limit && lo.1 == offset);
            lemma_sparse_limit_offset_printable(rord, fuel);
        },
        _ => {},
    }
}

// ---- dispatcher: Phase 1 for the whole statement grammar -------------------
//
// Self-recurses only in the Explain arm (at `fuel - 1`); every other arm calls
// the corresponding standalone kind helper, which is independent of the
// dispatcher.
pub proof fn lemma_sparse_stmt_printable(input: Seq<TokenView>, fuel: nat)
    requires
        sparse_stmt(input, fuel).0 is Some,
        finite_floats_stmt(sparse_stmt(input, fuel).0.unwrap()),
    ensures
        printable_stmt(sparse_stmt(input, fuel).0.unwrap()),
    decreases fuel,
{
    reveal_with_fuel(sparse_stmt, 1);
    reveal(printable_stmt);
    let s = sparse_stmt(input, fuel).0.unwrap();
    match input[0] {
        TokenView::Keyword(Keyword::Commit) => {},
        TokenView::Keyword(Keyword::Rollback) => {},
        TokenView::Keyword(Keyword::Begin) => {},
        TokenView::Keyword(Keyword::Create) => {
            lemma_sparse_create_printable(input, fuel);
        },
        TokenView::Keyword(Keyword::Drop) => {},
        TokenView::Keyword(Keyword::Delete) => {
            lemma_sparse_delete_printable(input, fuel);
        },
        TokenView::Keyword(Keyword::Insert) => {
            lemma_sparse_insert_printable(input, fuel);
        },
        TokenView::Keyword(Keyword::Update) => {
            lemma_sparse_update_printable(input, fuel);
        },
        TokenView::Keyword(Keyword::Select) => {
            lemma_sparse_select_printable(input, fuel);
        },
        TokenView::Keyword(Keyword::Explain) => {
            // s == Explain(inner) with inner from sparse_stmt(input.drop_first(), fuel-1)
            // and !is_sexplain(inner).
            let (inner_opt, rest) = sparse_stmt(input.drop_first(), (fuel - 1) as nat);
            let inner = inner_opt.unwrap();
            assert(s == SStmt::Explain(Box::new(inner)));
            assert(!verified_stmt::is_sexplain(inner));
            assert(finite_floats_stmt(inner));
            lemma_sparse_stmt_printable(input.drop_first(), (fuel - 1) as nat);
        },
        _ => {},
    }
}

// ---- Phase-3 headline: statement idempotence on the finite-float fragment ---
//
// The natural, semantically clear `finite_floats_stmt(s)` hypothesis (no
// overflow floats; plus the load-bearing `SELECT * AS a` exclusion) replaces the
// `printable_stmt(s)` side-condition, which Phase 1 discharges.
pub proof fn lemma_parse_idempotent_stmt_finite(
    input: Seq<TokenView>,
    s: SStmt,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse_stmt(input, fuel) == (Some(s), Seq::<TokenView>::empty()),
        finite_floats_stmt(s),
        fuel2 >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel2) == sparse_stmt(input, fuel),
{
    lemma_sparse_stmt_printable(input, fuel);
    lemma_parse_idempotent_stmt(input, s, fuel, fuel2);
}

} // verus!
