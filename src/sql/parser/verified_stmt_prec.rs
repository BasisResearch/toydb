//! Functional spec twin of the live statement parser `verified_control`.
//!
//! `verified_control::parse_control_at` parses production statements by
//! delegating every embedded expression to the precedence-climbing parser
//! `verified_precedence::parse_expression_at`, whose spec twin is
//! `sparse_prec`. The pre-existing statement mirror `verified_stmt::sparse_stmt`
//! is *not* a spec for `parse_control_at`: its expression positions accept only
//! the fully-parenthesised grammar (`sparse`), while `parse_control_at` accepts
//! the full precedence grammar. This module provides a *new* mirror,
//! `sparse_control`, whose expression positions are `sparse_prec`, and against
//! which the live parser is proven to refine (up to `verified_stmt::view_stmt`).
//!
//! Convention (matching `sparse_prec` / `sparse_stmt`): each spec parser works
//! over a `Seq<TokenView>` *suffix* and returns the remaining suffix; on any
//! parse failure it returns `(None, input)` (the original input), mirroring the
//! exec parsers, which return the original `pos` on failure. Fuel bounds the
//! `EXPLAIN` recursion, exactly as `sparse_stmt`.

#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::SExpr;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_precedence::sparse_prec;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::{SColumn, SFrom, SStmt};
#[allow(unused_imports)]
use super::{Keyword, ast, verified_precedence, verified_production, verified_roundtrip, verified_stmt};
#[allow(unused_imports)]
use crate::sql::types::DataType;

verus! {

// ===========================================================================
// Spec-level fuel for a token suffix.
//
// The live parser calls `parse_expression_at(toks, pos, 0, 2*(len-pos)+3)` at
// every expression position. The spec twin passes the matching fuel to
// `sparse_prec`. `expr_fuel(input)` is that value as a `nat`, where `input` is
// the token-view suffix at the expression position.
// ===========================================================================

/// Fuel the live parser hands `parse_expression_at` for a suffix of length `n`:
/// `2*n + 3`, as a `nat`.
pub open spec fn expr_fuel(input: Seq<TokenView>) -> nat {
    (2 * input.len() + 3) as nat
}

// ===========================================================================
// DELETE  (spec twin of `verified_control::parse_delete_at`)
//
// `input` is the token-view suffix at `pos`, where the caller has already
// consumed the leading `DELETE` keyword. Grammar: `FROM <ident> [WHERE <expr>]`.
// The expression position uses `sparse_prec` at precedence 0 with the exact
// fuel the exec code passes (`2 * suffix.len() + 3`).
// ===========================================================================

/// `FROM <ident> [WHERE <expr>]`, with `input` positioned just past `DELETE`.
pub open spec fn sparse_control_delete(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 2 || input[0] != TokenView::Keyword(Keyword::From) {
        (None, input)
    } else {
        match input[1] {
            TokenView::Ident(table) => {
                // Position just past `FROM <ident>`.
                let r = input.drop_first().drop_first();
                if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Where) {
                    let e_in = r.drop_first();
                    match sparse_prec(e_in, 0, expr_fuel(e_in)) {
                        (Some(e), rest) => (
                            Some(SStmt::Delete { table, where_clause: Some(e) }),
                            rest,
                        ),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(SStmt::Delete { table, where_clause: None }), r)
                }
            },
            _ => (None, input),
        }
    }
}

// ===========================================================================
// DROP  (spec twin of `verified_control::parse_drop_at`)
//
// `input` is the suffix just past `DROP`. Grammar: `TABLE [IF EXISTS] <ident>`.
// ===========================================================================

/// `TABLE [IF EXISTS] <ident>`, with `input` positioned just past `DROP`.
pub open spec fn sparse_control_drop(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Table) {
        (None, input)
    } else {
        // Optional IF EXISTS. `IF` present but not followed by `EXISTS` errors.
        let has_if = input.len() >= 2 && input[1] == TokenView::Keyword(Keyword::If);
        let has_if_exists = input.len() >= 3
            && input[1] == TokenView::Keyword(Keyword::If)
            && input[2] == TokenView::Keyword(Keyword::Exists);
        if has_if && !has_if_exists {
            (None, input)
        } else {
            let if_exists = has_if_exists;
            let r = if has_if_exists {
                input.drop_first().drop_first().drop_first()
            } else {
                input.drop_first()
            };
            if r.len() < 1 {
                (None, input)
            } else {
                match r[0] {
                    TokenView::Ident(name) => (
                        Some(SStmt::DropTable { name, if_exists }),
                        r.drop_first(),
                    ),
                    _ => (None, input),
                }
            }
        }
    }
}

// ===========================================================================
// BEGIN  (spec twin of `verified_control::parse_begin_at`)
//
// `input` is the suffix just past `BEGIN`. Grammar: `[TRANSACTION]
// [READ ONLY | READ WRITE] [AS OF SYSTEM TIME <number>]`. Note this differs
// from `verified_stmt::sparse_begin`, which omits TRANSACTION and READ WRITE.
// ===========================================================================

/// `[TRANSACTION] [READ ONLY|WRITE] [AS OF SYSTEM TIME <num>]`, past `BEGIN`.
pub open spec fn sparse_control_begin(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    // Optional TRANSACTION.
    let r0 = if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Transaction) {
        input.drop_first()
    } else {
        input
    };
    // Optional READ ONLY / READ WRITE.
    let read_res: Option<(bool, Seq<TokenView>)> =
        if r0.len() >= 1 && r0[0] == TokenView::Keyword(Keyword::Read) {
            let r1 = r0.drop_first();
            if r1.len() < 1 {
                None
            } else if r1[0] == TokenView::Keyword(Keyword::Only) {
                Some((true, r1.drop_first()))
            } else if r1[0] == TokenView::Keyword(Keyword::Write) {
                Some((false, r1.drop_first()))
            } else {
                None
            }
        } else {
            Some((false, r0))
        };
    match read_res {
        None => (None, input),
        Some((read_only, r2)) => {
            // Optional AS OF SYSTEM TIME <number>.
            if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::As) {
                let r3 = r2.drop_first();
                if r3.len() < 1 || r3[0] != TokenView::Keyword(Keyword::Of) {
                    (None, input)
                } else {
                    let r4 = r3.drop_first();
                    if r4.len() < 1 || r4[0] != TokenView::Keyword(Keyword::System) {
                        (None, input)
                    } else {
                        let r5 = r4.drop_first();
                        if r5.len() < 1 || r5[0] != TokenView::Keyword(Keyword::Time) {
                            (None, input)
                        } else {
                            let r6 = r5.drop_first();
                            if r6.len() < 1 {
                                (None, input)
                            } else {
                                match r6[0] {
                                    TokenView::Number(bytes) =>
                                        match super::verified_integer::parse_digits_spec(bytes) {
                                            Some(version) => (
                                                Some(SStmt::Begin { read_only, as_of: Some(version) }),
                                                r6.drop_first(),
                                            ),
                                            None => (None, input),
                                        },
                                    _ => (None, input),
                                }
                            }
                        }
                    }
                }
            } else {
                (Some(SStmt::Begin { read_only, as_of: None }), r2)
            }
        },
    }
}

// ===========================================================================
// ORDER BY  (spec twin of `verified_control::parse_order_by_at`)
//
// `input` is the suffix at the position where the optional `ORDER BY` clause may
// begin. Grammar: `[ORDER BY <expr> [ASC|DESC] (, <expr> [ASC|DESC])*]`. The
// direction defaults to Ascending when neither `ASC` nor `DESC` is present.
// ===========================================================================

/// One-or-more `<expr> [ASC|DESC]` comma-separated items. Recurses on the input
/// length: the tail `r1.drop_first()` is always strictly shorter than `input`
/// (`r1.len() <= sparse_prec(...).1.len() <= input.len()`, minus the dropped
/// comma), so no fuel parameter is needed and fuel-stability never arises.
pub open spec fn sparse_control_order_list(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_order_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            // Optional direction; defaults to Ascending.
            let (d, r1) = if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc) {
                (ast::Direction::Ascending, r.drop_first())
            } else if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc) {
                (ast::Direction::Descending, r.drop_first())
            } else {
                (ast::Direction::Ascending, r)
            };
            if r1.len() >= 1 && r1[0] == TokenView::Comma {
                match sparse_control_order_list(r1.drop_first()) {
                    (Some(more), r2) => (Some(seq![(e, d)] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![(e, d)]), r1)
            }
        },
        (None, _) => (None, input),
    }
}

/// Termination witness for `sparse_control_order_list`: the recursive tail
/// `r1.drop_first()` is strictly shorter than `input`, because `sparse_prec`
/// never grows its input (`lemma_prec_slen`) and the direction/comma steps only
/// drop tokens.
#[via_fn]
proof fn sparse_control_order_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
    // r.len() <= input.len(); r1.len() <= r.len(); r1.drop_first().len() < input.len()
    // when the recursive branch is taken (r1 non-empty), which the SMT derives
    // from the length facts above.
}

/// `[ORDER BY <list>]`, with `input` at the (optional) `ORDER` keyword.
pub open spec fn sparse_control_order_by(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>)
{
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Order) {
        (Some(Seq::<(SExpr, ast::Direction)>::empty()), input)
    } else if input.len() < 2 || input[1] != TokenView::Keyword(Keyword::By) {
        (None, input)
    } else {
        let r = input.drop_first().drop_first();
        match sparse_control_order_list(r) {
            (Some(items), rest) => (Some(items), rest),
            (None, _) => (None, input),
        }
    }
}

/// `verified_stmt::view_order_list` distributes over sequence concatenation.
pub proof fn lemma_view_order_list_append(
    a: Seq<(ast::Expression, ast::Direction)>,
    b: Seq<(ast::Expression, ast::Direction)>,
)
    ensures
        verified_stmt::view_order_list(a + b)
            == verified_stmt::view_order_list(a) + verified_stmt::view_order_list(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_order_list, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_order_list_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

/// Single-item view: `view_order_list(seq![(expr, d)]) == seq![(view_expr(expr), d)]`.
pub proof fn lemma_view_order_list_single(expr: ast::Expression, d: ast::Direction)
    ensures
        verified_stmt::view_order_list(seq![(expr, d)])
            == seq![(verified_roundtrip::view_expr(expr), d)],
{
    reveal_with_fuel(verified_stmt::view_order_list, 2);
    let s = seq![(expr, d)];
    assert(s.len() == 1);
    assert(s[0] == (expr, d));
    assert(s.drop_first() =~= Seq::<(ast::Expression, ast::Direction)>::empty());
    assert(verified_stmt::view_order_list(s.drop_first())
        =~= Seq::<(SExpr, ast::Direction)>::empty());
    assert(verified_stmt::view_order_list(s)
        =~= seq![(verified_roundtrip::view_expr(expr), d)]);
}

/// Prepend already-consumed `done` items onto a tail order-list parse, routing
/// `whole` through on rejection (matching how `sparse_control_order_list`
/// returns its top-level input on any inner reject).
pub open spec fn order_list_prepend(
    done: Seq<(SExpr, ast::Direction)>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>),
) -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

/// Loop-resumption bridge for `parse_order_by_at`. Parsing the whole list from
/// `start` equals prepending the `done` items already consumed onto the parse
/// continuing at the current suffix `cur`, where `start` is (semantically) the
/// tokens of `done` followed by `cur`. The exec loop maintains the antecedent
/// `sparse_control_order_list(start) == order_list_prepend(done, start, P(cur))`
/// and steps it; this lemma discharges the single inductive step, unfolding one
/// level of `sparse_control_order_list(cur)`.
///
/// It is stated as: given the head item `(e, d)` parsed from `cur` and a comma,
/// with `cur1` the suffix after the comma, one level of the recursion at `cur`
/// rewrites to prepending `(e, d)` and recursing at `cur1`.
pub proof fn lemma_order_list_step(cur: Seq<TokenView>, e: SExpr, d: ast::Direction, r: Seq<TokenView>, r1: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc)) ==> d == ast::Direction::Ascending && r1 == r.drop_first(),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc)) ==> d == ast::Direction::Descending && r1 == r.drop_first(),
        !(r.len() >= 1 && (r[0] == TokenView::Keyword(Keyword::Asc) || r[0] == TokenView::Keyword(Keyword::Desc)))
            ==> d == ast::Direction::Ascending && r1 == r,
        r1.len() >= 1,
        r1[0] == TokenView::Comma,
    ensures
        sparse_control_order_list(cur)
            == order_list_prepend(seq![(e, d)], cur, sparse_control_order_list(r1.drop_first())),
{
    // Unfold one level of `sparse_control_order_list(cur)`: its lhs phase is
    // `sparse_prec(cur, ..) == (Some(e), r)` by hypothesis, the direction/comma
    // steps land on `r1` with a leading comma, so it recurses on
    // `r1.drop_first()`. The `order_list_prepend` shape then matches by def.
    match sparse_control_order_list(r1.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_order_list(cur) == (Some(seq![(e, d)] + more), r2));
            assert(seq![(e, d)] + more == seq![(e, d)] + more);
        },
        (None, _) => {
            assert(sparse_control_order_list(cur) == (None::<Seq<(SExpr, ast::Direction)>>, cur));
        },
    }
}

/// Re-establishes the loop-resumption invariant after consuming one more item.
/// Given the invariant at `cur` (`whole == prepend(done, ls, P(cur))`) and the
/// single-step unfold (`P(cur) == prepend([(se,d)], cur, P(cur1))`), the
/// invariant at `cur1` holds with `done ++ [(se,d)]`. Pure `order_list_prepend`
/// algebra with sequence-append associativity.
pub proof fn lemma_order_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<(SExpr, ast::Direction)>,
    se: SExpr,
    d: ast::Direction,
    whole: (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>),
)
    requires
        whole == order_list_prepend(done, ls, sparse_control_order_list(cur)),
        sparse_control_order_list(cur)
            == order_list_prepend(seq![(se, d)], cur, sparse_control_order_list(cur1)),
    ensures
        whole == order_list_prepend(done + seq![(se, d)], ls, sparse_control_order_list(cur1)),
{
    match sparse_control_order_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![(se, d)] + more) == (done + seq![(se, d)]) + more);
        },
        None => {},
    }
}

/// Terminal step: no comma after the (optional) direction, so the list is the
/// single head item.
pub proof fn lemma_order_list_last(cur: Seq<TokenView>, e: SExpr, d: ast::Direction, r: Seq<TokenView>, r1: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc)) ==> d == ast::Direction::Ascending && r1 == r.drop_first(),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc)) ==> d == ast::Direction::Descending && r1 == r.drop_first(),
        !(r.len() >= 1 && (r[0] == TokenView::Keyword(Keyword::Asc) || r[0] == TokenView::Keyword(Keyword::Desc)))
            ==> d == ast::Direction::Ascending && r1 == r,
        !(r1.len() >= 1 && r1[0] == TokenView::Comma),
    ensures
        sparse_control_order_list(cur) == (Some(seq![(e, d)]), r1),
{
}

// ===========================================================================
// GROUP BY  (spec twin of `verified_control::parse_group_by_at`)
//
// `input` is the suffix at the position where the optional `GROUP BY` clause may
// begin. Grammar: `[GROUP BY <expr> (, <expr>)*]`. This is the ORDER BY list
// minus the ASC/DESC direction: a plain comma-separated list of expressions,
// viewed through `verified_roundtrip::view_args` (`Seq<ast::Expression>` ->
// `Seq<SExpr>`), which the live parser accumulates as a `Vec<ast::Expression>`.
// ===========================================================================

/// One-or-more comma-separated `<expr>` items. Recurses on the input length: the
/// tail `r.drop_first()` (past the comma) is strictly shorter than `input`
/// (`r.len() <= sparse_prec(...).1.len() <= input.len()`, minus the dropped
/// comma), so no fuel parameter is needed. Mirrors `sparse_control_order_list`.
pub open spec fn sparse_control_group_list(input: Seq<TokenView>)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_group_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_group_list(r.drop_first()) {
                    (Some(more), r2) => (Some(seq![e] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![e]), r)
            }
        },
        (None, _) => (None, input),
    }
}

/// Termination witness for `sparse_control_group_list`: `r.drop_first()` is
/// strictly shorter than `input`, because `sparse_prec` never grows its input
/// (`lemma_prec_slen`) and the comma step drops one more token.
#[via_fn]
proof fn sparse_control_group_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
}

/// `[GROUP BY <list>]`, with `input` at the (optional) `GROUP` keyword. Returns
/// the empty list (no consumption) when no `GROUP` keyword is present, and
/// rejects a bare `GROUP` without a following `BY`. Mirrors `parse_group_by_at`.
pub open spec fn sparse_control_group_by(input: Seq<TokenView>)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
{
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Group) {
        (Some(Seq::<SExpr>::empty()), input)
    } else if input.len() < 2 || input[1] != TokenView::Keyword(Keyword::By) {
        (None, input)
    } else {
        let r = input.drop_first().drop_first();
        match sparse_control_group_list(r) {
            (Some(items), rest) => (Some(items), rest),
            (None, _) => (None, input),
        }
    }
}

/// `verified_roundtrip::view_args` distributes over sequence concatenation.
pub proof fn lemma_view_args_append(
    a: Seq<ast::Expression>,
    b: Seq<ast::Expression>,
)
    ensures
        verified_roundtrip::view_args(a + b)
            == verified_roundtrip::view_args(a) + verified_roundtrip::view_args(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_roundtrip::view_args, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_args_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

/// Single-item view: `view_args(seq![expr]) == seq![view_expr(expr)]`.
pub proof fn lemma_view_args_single(expr: ast::Expression)
    ensures
        verified_roundtrip::view_args(seq![expr]) == seq![verified_roundtrip::view_expr(expr)],
{
    reveal_with_fuel(verified_roundtrip::view_args, 2);
    let s = seq![expr];
    assert(s.len() == 1);
    assert(s[0] == expr);
    assert(s.drop_first() =~= Seq::<ast::Expression>::empty());
    assert(verified_roundtrip::view_args(s.drop_first()) =~= Seq::<SExpr>::empty());
    assert(verified_roundtrip::view_args(s) =~= seq![verified_roundtrip::view_expr(expr)]);
}

/// Prepend already-consumed `done` items onto a tail group-list parse, routing
/// `whole` through on rejection (matching how `sparse_control_group_list`
/// returns its top-level input on any inner reject).
pub open spec fn group_list_prepend(
    done: Seq<SExpr>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<SExpr>>, Seq<TokenView>),
) -> (Option<Seq<SExpr>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

/// One-level unfold of `sparse_control_group_list(cur)` when a comma follows the
/// head item `e`: rewrites to prepending `[e]` and recursing at the post-comma
/// suffix. Mirrors `lemma_order_list_step`.
pub proof fn lemma_group_list_step(cur: Seq<TokenView>, e: SExpr, r: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_group_list(cur)
            == group_list_prepend(seq![e], cur, sparse_control_group_list(r.drop_first())),
{
    match sparse_control_group_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_group_list(cur) == (Some(seq![e] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_group_list(cur) == (None::<Seq<SExpr>>, cur));
        },
    }
}

/// Re-establishes the loop-resumption invariant after consuming one more item.
/// Pure `group_list_prepend` algebra with sequence-append associativity. Mirrors
/// `lemma_order_list_resume_step`.
pub proof fn lemma_group_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<SExpr>,
    se: SExpr,
    whole: (Option<Seq<SExpr>>, Seq<TokenView>),
)
    requires
        whole == group_list_prepend(done, ls, sparse_control_group_list(cur)),
        sparse_control_group_list(cur)
            == group_list_prepend(seq![se], cur, sparse_control_group_list(cur1)),
    ensures
        whole == group_list_prepend(done + seq![se], ls, sparse_control_group_list(cur1)),
{
    match sparse_control_group_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![se] + more) == (done + seq![se]) + more);
        },
        None => {},
    }
}

/// Terminal step: no comma after the head item, so the list is the single item.
pub proof fn lemma_group_list_last(cur: Seq<TokenView>, e: SExpr, r: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_group_list(cur) == (Some(seq![e]), r),
{
}

// ===========================================================================
// CREATE TABLE  (spec twins of `verified_control::parse_create_column_at` and
// `parse_create_at`).
//
// Grammar (`input` positioned just past `CREATE`):
//   `TABLE <ident> ( <column> (, <column>)* )`
// where a `<column>` is `<name> <datatype> <constraint>*` and each
// `<constraint>` is one of the keyword-led clauses `PRIMARY KEY`, `NULL`,
// `NOT NULL`, `DEFAULT <expr>`, `UNIQUE`, `INDEX`, `REFERENCES <ident>`, parsed
// in *any order* by a loop that ends at the first non-keyword token. `DEFAULT`'s
// expression position is `sparse_prec` at the fuel the exec code passes
// (`2 * suffix.len() + 3`). Unlike `verified_stmt::sparse_column`, this mirror
// (a) accepts constraints in any order, and (b) uses the precedence grammar for
// `DEFAULT`, matching the live parser exactly.
// ===========================================================================

/// The datatype a column-definition keyword denotes, mirroring the `match` in
/// `parse_create_column_at` (with all the accepted aliases). `None` for any
/// token that does not begin a datatype.
pub open spec fn parse_column_datatype_kw(t: TokenView) -> Option<DataType> {
    match t {
        TokenView::Keyword(Keyword::Bool) => Some(DataType::Boolean),
        TokenView::Keyword(Keyword::Boolean) => Some(DataType::Boolean),
        TokenView::Keyword(Keyword::Float) => Some(DataType::Float),
        TokenView::Keyword(Keyword::Double) => Some(DataType::Float),
        TokenView::Keyword(Keyword::Int) => Some(DataType::Integer),
        TokenView::Keyword(Keyword::Integer) => Some(DataType::Integer),
        TokenView::Keyword(Keyword::String) => Some(DataType::String),
        TokenView::Keyword(Keyword::Text) => Some(DataType::String),
        TokenView::Keyword(Keyword::Varchar) => Some(DataType::String),
        _ => None,
    }
}

/// The mutable constraint accumulator threaded through the column loop: the six
/// constraint fields of `SColumn` (name and datatype are fixed once parsed).
pub struct ColAcc {
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<SExpr>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

/// Assemble the finished `SColumn` from the fixed name/datatype and the
/// constraint accumulator.
pub open spec fn col_from_acc(name: String, datatype: DataType, acc: ColAcc) -> SColumn {
    SColumn {
        name,
        datatype,
        primary_key: acc.primary_key,
        nullable: acc.nullable,
        default: acc.default,
        unique: acc.unique,
        index: acc.index,
        references: acc.references,
    }
}

/// Spec twin of the constraint loop in `parse_create_column_at`. `input` is the
/// suffix at the current loop position (past name + datatype and any constraints
/// already folded into `acc`); `name` is carried for the finished column. On the
/// first non-keyword token (or EOF) the loop stops and returns
/// `(Some(col_from_acc(...)), input)`; a malformed constraint rejects with
/// `(None, input)` where `input` is *this* suffix (the exec code returns `pos`,
/// but every reject unwinds all the way up to `parse_create_column_at`'s `pos` —
/// this local reject is lifted to the column's `pos` by the caller-side proof,
/// matching how the list bridges route rejection through `whole`).
///
/// Terminates on `input.len()`: every accepted constraint drops at least the
/// leading keyword (and `DEFAULT` never grows its input, by `lemma_prec_slen`),
/// so the recursive suffix is strictly shorter.
pub open spec fn sparse_control_col_constraints(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
) -> (Option<SColumn>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_col_constraints_decreases
{
    if input.len() < 1 {
        (Some(col_from_acc(name, datatype, acc)), input)
    } else {
        match input[0] {
            TokenView::Keyword(k) => {
                let r = input.drop_first();
                if k == Keyword::Primary {
                    if r.len() < 1 || r[0] != TokenView::Keyword(Keyword::Key) {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r.drop_first(), name, datatype,
                            ColAcc { primary_key: true, ..acc })
                    }
                } else if k == Keyword::Null {
                    if acc.nullable is Some {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r, name, datatype,
                            ColAcc { nullable: Some(true), ..acc })
                    }
                } else if k == Keyword::Not {
                    if r.len() < 1 || r[0] != TokenView::Keyword(Keyword::Null) {
                        (None, input)
                    } else if acc.nullable is Some {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r.drop_first(), name, datatype,
                            ColAcc { nullable: Some(false), ..acc })
                    }
                } else if k == Keyword::Default {
                    match sparse_prec(r, 0, expr_fuel(r)) {
                        (Some(e), r6) => sparse_control_col_constraints(
                            r6, name, datatype,
                            ColAcc { default: Some(e), ..acc }),
                        (None, _) => (None, input),
                    }
                } else if k == Keyword::Unique {
                    sparse_control_col_constraints(
                        r, name, datatype, ColAcc { unique: true, ..acc })
                } else if k == Keyword::Index {
                    sparse_control_col_constraints(
                        r, name, datatype, ColAcc { index: true, ..acc })
                } else if k == Keyword::References {
                    if r.len() < 1 {
                        (None, input)
                    } else {
                        match r[0] {
                            TokenView::Ident(n) => sparse_control_col_constraints(
                                r.drop_first(), name, datatype,
                                ColAcc { references: Some(n), ..acc }),
                            _ => (None, input),
                        }
                    }
                } else {
                    (None, input)
                }
            },
            // Non-keyword token ends the column definition.
            _ => (Some(col_from_acc(name, datatype, acc)), input),
        }
    }
}

/// Termination witness for `sparse_control_col_constraints`: every recursive
/// suffix is strictly shorter than `input`. All arms drop at least the leading
/// keyword; `DEFAULT` recurses on `sparse_prec`'s remainder, which never exceeds
/// `r.len() < input.len()` (`lemma_prec_slen`).
#[via_fn]
proof fn sparse_control_col_constraints_decreases(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
) {
    if input.len() >= 1 {
        let r = input.drop_first();
        verified_precedence::lemma_prec_slen(r, 0, expr_fuel(r));
    }
}

/// View of an optional default expression: `Some(view_expr(e))` / `None`.
/// Used to relate the exec `Option<ast::Expression>` default local to the
/// spec-level `Option<SExpr>` in `ColAcc` without a by-value `match` (which
/// would move the non-`Copy` expression).
pub open spec fn opt_view_expr(d: Option<ast::Expression>) -> Option<SExpr> {
    match d {
        Some(e) => Some(verified_roundtrip::view_expr(e)),
        None => None,
    }
}

/// The empty (freshly-initialised) constraint accumulator, matching the exec
/// loop's locals before the first iteration.
pub open spec fn col_acc_empty() -> ColAcc {
    ColAcc {
        primary_key: false,
        nullable: None,
        default: None,
        unique: false,
        index: false,
        references: None,
    }
}

/// Spec twin of `parse_create_column_at`. `input` is the suffix at the column's
/// starting position. Grammar: `<name:ident> <datatype:kw> <constraint>*`.
pub open spec fn sparse_control_column(input: Seq<TokenView>) -> (Option<SColumn>, Seq<TokenView>) {
    if input.len() < 1 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                let r0 = input.drop_first();
                if r0.len() < 1 {
                    (None, input)
                } else {
                    match parse_column_datatype_kw(r0[0]) {
                        Some(datatype) => {
                            let r1 = r0.drop_first();
                            match sparse_control_col_constraints(r1, name, datatype, col_acc_empty()) {
                                (Some(c), rest) => (Some(c), rest),
                                (None, _) => (None, input),
                            }
                        },
                        None => (None, input),
                    }
                }
            },
            _ => (None, input),
        }
    }
}

/// One-or-more comma-separated column definitions, terminated by the first token
/// that is not a comma. Mirrors the column loop in `parse_create_at`. Recurses on
/// `input.len()`: each accepted column consumes at least its name + datatype
/// (`sparse_control_column` strictly advances on `Some`), and the comma step
/// drops one more.
pub open spec fn sparse_control_column_list(input: Seq<TokenView>)
    -> (Option<Seq<SColumn>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_column_list_decreases
{
    match sparse_control_column(input) {
        (Some(c), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_column_list(r.drop_first()) {
                    (Some(more), r2) => (Some(seq![c] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![c]), r)
            }
        },
        (None, _) => (None, input),
    }
}

/// Termination witness for `sparse_control_column_list`: `sparse_control_column`
/// strictly advances on `Some` and never grows its input, so `r.drop_first()`
/// (past the comma) is strictly shorter than `input`.
#[via_fn]
proof fn sparse_control_column_list_decreases(input: Seq<TokenView>) {
    lemma_control_column_slen(input);
}

/// `sparse_control_column` never grows its input, and strictly shrinks it on a
/// `Some` result (a column consumes at least its name and datatype). Mirrors
/// `parse_create_column_at`'s `r.0 is Some ==> pos < r.1` postcondition.
pub proof fn lemma_control_column_slen(input: Seq<TokenView>)
    ensures
        sparse_control_column(input).1.len() <= input.len(),
        sparse_control_column(input).0 is Some ==> sparse_control_column(input).1.len() < input.len(),
{
    if input.len() >= 1 {
        match input[0] {
            TokenView::Ident(name) => {
                let r0 = input.drop_first();
                if r0.len() >= 1 {
                    match parse_column_datatype_kw(r0[0]) {
                        Some(datatype) => {
                            let r1 = r0.drop_first();
                            lemma_col_constraints_slen(r1, name, datatype, col_acc_empty());
                        },
                        None => {},
                    }
                }
            },
            _ => {},
        }
    }
}

/// `sparse_control_col_constraints` never grows its input suffix. Used to show
/// the whole column strictly advances.
pub proof fn lemma_col_constraints_slen(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
)
    ensures
        sparse_control_col_constraints(input, name, datatype, acc).1.len() <= input.len(),
    decreases input.len(),
{
    if input.len() >= 1 {
        match input[0] {
            TokenView::Keyword(k) => {
                let r = input.drop_first();
                if k == Keyword::Primary {
                    if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Key) {
                        lemma_col_constraints_slen(r.drop_first(), name, datatype,
                            ColAcc { primary_key: true, ..acc });
                    }
                } else if k == Keyword::Null {
                    if !(acc.nullable is Some) {
                        lemma_col_constraints_slen(r, name, datatype,
                            ColAcc { nullable: Some(true), ..acc });
                    }
                } else if k == Keyword::Not {
                    if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Null) && !(acc.nullable is Some) {
                        lemma_col_constraints_slen(r.drop_first(), name, datatype,
                            ColAcc { nullable: Some(false), ..acc });
                    }
                } else if k == Keyword::Default {
                    verified_precedence::lemma_prec_slen(r, 0, expr_fuel(r));
                    match sparse_prec(r, 0, expr_fuel(r)) {
                        (Some(e), r6) => lemma_col_constraints_slen(r6, name, datatype,
                            ColAcc { default: Some(e), ..acc }),
                        (None, _) => {},
                    }
                } else if k == Keyword::Unique {
                    lemma_col_constraints_slen(r, name, datatype, ColAcc { unique: true, ..acc });
                } else if k == Keyword::Index {
                    lemma_col_constraints_slen(r, name, datatype, ColAcc { index: true, ..acc });
                } else if k == Keyword::References {
                    if r.len() >= 1 {
                        match r[0] {
                            TokenView::Ident(n) => lemma_col_constraints_slen(r.drop_first(), name, datatype,
                                ColAcc { references: Some(n), ..acc }),
                            _ => {},
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

/// Prepend already-consumed `done` columns onto a tail column-list parse,
/// routing `whole` through on rejection. Mirrors `group_list_prepend`.
pub open spec fn column_list_prepend(
    done: Seq<SColumn>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<SColumn>>, Seq<TokenView>),
) -> (Option<Seq<SColumn>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

/// `verified_stmt::view_columns` distributes over sequence concatenation.
pub proof fn lemma_view_columns_append(
    a: Seq<ast::Column>,
    b: Seq<ast::Column>,
)
    ensures
        verified_stmt::view_columns(a + b)
            == verified_stmt::view_columns(a) + verified_stmt::view_columns(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_columns, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_columns_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

/// Single-item view: `view_columns(seq![c]) == seq![view_column(c)]`.
pub proof fn lemma_view_columns_single(c: ast::Column)
    ensures
        verified_stmt::view_columns(seq![c]) == seq![verified_stmt::view_column(c)],
{
    reveal_with_fuel(verified_stmt::view_columns, 2);
    let s = seq![c];
    assert(s.len() == 1);
    assert(s[0] == c);
    assert(s.drop_first() =~= Seq::<ast::Column>::empty());
    assert(verified_stmt::view_columns(s.drop_first()) =~= Seq::<SColumn>::empty());
    assert(verified_stmt::view_columns(s) =~= seq![verified_stmt::view_column(c)]);
}

/// One-level unfold of `sparse_control_column_list(cur)` when a comma follows the
/// head column `c`: rewrites to prepending `[c]` and recursing at the post-comma
/// suffix. Mirrors `lemma_group_list_step`.
pub proof fn lemma_column_list_step(cur: Seq<TokenView>, c: SColumn, r: Seq<TokenView>)
    requires
        sparse_control_column(cur) == (Some(c), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_column_list(cur)
            == column_list_prepend(seq![c], cur, sparse_control_column_list(r.drop_first())),
{
    match sparse_control_column_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_column_list(cur) == (Some(seq![c] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_column_list(cur) == (None::<Seq<SColumn>>, cur));
        },
    }
}

/// Re-establishes the loop-resumption invariant after consuming one more column.
/// Pure `column_list_prepend` algebra. Mirrors `lemma_group_list_resume_step`.
pub proof fn lemma_column_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<SColumn>,
    sc: SColumn,
    whole: (Option<Seq<SColumn>>, Seq<TokenView>),
)
    requires
        whole == column_list_prepend(done, ls, sparse_control_column_list(cur)),
        sparse_control_column_list(cur)
            == column_list_prepend(seq![sc], cur, sparse_control_column_list(cur1)),
    ensures
        whole == column_list_prepend(done + seq![sc], ls, sparse_control_column_list(cur1)),
{
    match sparse_control_column_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![sc] + more) == (done + seq![sc]) + more);
        },
        None => {},
    }
}

/// Terminal step: no comma after the head column, so the list is the single item.
pub proof fn lemma_column_list_last(cur: Seq<TokenView>, c: SColumn, r: Seq<TokenView>)
    requires
        sparse_control_column(cur) == (Some(c), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_column_list(cur) == (Some(seq![c]), r),
{
}

/// Spec twin of `parse_create_at`. `input` is the suffix just past `CREATE`.
/// Grammar: `TABLE <ident> ( <column-list> )`.
pub open spec fn sparse_control_create(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Table) {
        (None, input)
    } else {
        let r0 = input.drop_first();
        if r0.len() < 1 {
            (None, input)
        } else {
            match r0[0] {
                TokenView::Ident(name) => {
                    let r1 = r0.drop_first();
                    if r1.len() < 1 || r1[0] != TokenView::OpenParen {
                        (None, input)
                    } else {
                        let r2 = r1.drop_first();
                        match sparse_control_column_list(r2) {
                            (Some(cols), r3) => {
                                if r3.len() >= 1 && r3[0] == TokenView::CloseParen {
                                    (Some(SStmt::CreateTable { name, columns: cols }), r3.drop_first())
                                } else {
                                    (None, input)
                                }
                            },
                            (None, _) => (None, input),
                        }
                    }
                },
                _ => (None, input),
            }
        }
    }
}

// ===========================================================================
// SELECT list  (spec twin of `verified_control::parse_select_list_at`)
//
// `input` is the suffix just past the leading `SELECT` keyword, where the
// comma-separated select list begins. Each item is `<expr> [[AS] <ident>]`:
// an expression (`sparse_prec`) followed by an optional alias, which is either
// `AS <ident>` or a bare `<ident>`. Aliasing `*` (the `SExpr::All` expression)
// is rejected. The view type mirrors `verified_stmt::view_select_list`:
// `Seq<(SExpr, Option<String>)>` — the alias string is carried unchanged.
// ===========================================================================

/// Resolve the optional alias that may follow a parsed select-list expression.
/// `e` is the expression already parsed, `r` the suffix just past it. Returns
/// `(Some((alias_opt, rest)))` on success, or `None` on a malformed alias
/// (aliasing `*`, EOF after `AS`, or a non-identifier where an alias name was
/// required). Mirrors the alias block of `parse_select_list_at`.
pub open spec fn sparse_control_select_alias(e: SExpr, r: Seq<TokenView>)
    -> Option<(Option<String>, Seq<TokenView>)> {
    let is_as = r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::As);
    let is_ident = r.len() >= 1 && (match r[0] {
        TokenView::Ident(_) => true,
        _ => false,
    });
    if is_as || is_ident {
        // Cannot alias `*`.
        if e == SExpr::All {
            None
        } else if is_as {
            // Consume `AS`; the next token must be an identifier.
            let r1 = r.drop_first();
            if r1.len() < 1 {
                None
            } else {
                match r1[0] {
                    TokenView::Ident(name) => Some((Some(name), r1.drop_first())),
                    _ => None,
                }
            }
        } else {
            // Bare identifier alias.
            match r[0] {
                TokenView::Ident(name) => Some((Some(name), r.drop_first())),
                _ => None,
            }
        }
    } else {
        Some((None, r))
    }
}

/// One-or-more comma-separated `<expr> [[AS] <ident>]` select-list items.
/// Recurses on the input length: the tail past the comma is strictly shorter
/// (`sparse_prec` never grows the input; the alias/comma steps only drop
/// tokens). Mirrors `sparse_control_order_list`.
pub open spec fn sparse_control_select_list(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_select_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            match sparse_control_select_alias(e, r) {
                Some((alias, r1)) => {
                    if r1.len() >= 1 && r1[0] == TokenView::Comma {
                        match sparse_control_select_list(r1.drop_first()) {
                            (Some(more), r2) => (Some(seq![(e, alias)] + more), r2),
                            (None, _) => (None, input),
                        }
                    } else {
                        (Some(seq![(e, alias)]), r1)
                    }
                },
                None => (None, input),
            }
        },
        (None, _) => (None, input),
    }
}

/// Termination witness for `sparse_control_select_list`: the recursive tail
/// (`r1.drop_first()`) is strictly shorter than `input`. `sparse_prec` never
/// grows its input (`lemma_prec_slen`); the alias resolution returns a suffix
/// no longer than `r`; and the comma step drops one more token.
#[via_fn]
proof fn sparse_control_select_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
}

/// `verified_stmt::view_select_list` distributes over sequence concatenation.
pub proof fn lemma_view_select_list_append(
    a: Seq<(ast::Expression, Option<String>)>,
    b: Seq<(ast::Expression, Option<String>)>,
)
    ensures
        verified_stmt::view_select_list(a + b)
            == verified_stmt::view_select_list(a) + verified_stmt::view_select_list(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_select_list, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_select_list_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

/// Single-item view: `view_select_list(seq![(expr, alias)]) ==
/// seq![(view_expr(expr), alias)]`.
pub proof fn lemma_view_select_list_single(expr: ast::Expression, alias: Option<String>)
    ensures
        verified_stmt::view_select_list(seq![(expr, alias)])
            == seq![(verified_roundtrip::view_expr(expr), alias)],
{
    reveal_with_fuel(verified_stmt::view_select_list, 2);
    let s = seq![(expr, alias)];
    assert(s.len() == 1);
    assert(s[0] == (expr, alias));
    assert(s.drop_first() =~= Seq::<(ast::Expression, Option<String>)>::empty());
    assert(verified_stmt::view_select_list(s.drop_first())
        =~= Seq::<(SExpr, Option<String>)>::empty());
    assert(verified_stmt::view_select_list(s)
        =~= seq![(verified_roundtrip::view_expr(expr), alias)]);
}

/// Prepend already-consumed `done` items onto a tail select-list parse, routing
/// `whole` through on rejection (matching how `sparse_control_select_list`
/// returns its top-level input on any inner reject).
pub open spec fn select_list_prepend(
    done: Seq<(SExpr, Option<String>)>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>),
) -> (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

/// One-level unfold of `sparse_control_select_list(cur)` when a comma follows
/// the head item `(e, alias)`: rewrites to prepending `[(e, alias)]` and
/// recursing at the post-comma suffix. Mirrors `lemma_order_list_step`.
pub proof fn lemma_select_list_step(
    cur: Seq<TokenView>,
    e: SExpr,
    alias: Option<String>,
    r: Seq<TokenView>,
    r1: Seq<TokenView>,
)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        sparse_control_select_alias(e, r) == Some((alias, r1)),
        r1.len() >= 1,
        r1[0] == TokenView::Comma,
    ensures
        sparse_control_select_list(cur)
            == select_list_prepend(seq![(e, alias)], cur, sparse_control_select_list(r1.drop_first())),
{
    match sparse_control_select_list(r1.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_select_list(cur) == (Some(seq![(e, alias)] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_select_list(cur)
                == (None::<Seq<(SExpr, Option<String>)>>, cur));
        },
    }
}

/// Re-establishes the loop-resumption invariant after consuming one more item.
/// Pure `select_list_prepend` algebra with sequence-append associativity.
/// Mirrors `lemma_order_list_resume_step`.
pub proof fn lemma_select_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<(SExpr, Option<String>)>,
    se: SExpr,
    alias: Option<String>,
    whole: (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>),
)
    requires
        whole == select_list_prepend(done, ls, sparse_control_select_list(cur)),
        sparse_control_select_list(cur)
            == select_list_prepend(seq![(se, alias)], cur, sparse_control_select_list(cur1)),
    ensures
        whole == select_list_prepend(done + seq![(se, alias)], ls, sparse_control_select_list(cur1)),
{
    match sparse_control_select_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![(se, alias)] + more) == (done + seq![(se, alias)]) + more);
        },
        None => {},
    }
}

/// Terminal step: no comma after the (aliased) head item, so the list is the
/// single item. Mirrors `lemma_order_list_last`.
pub proof fn lemma_select_list_last(
    cur: Seq<TokenView>,
    e: SExpr,
    alias: Option<String>,
    r: Seq<TokenView>,
    r1: Seq<TokenView>,
)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        sparse_control_select_alias(e, r) == Some((alias, r1)),
        !(r1.len() >= 1 && r1[0] == TokenView::Comma),
    ensures
        sparse_control_select_list(cur) == (Some(seq![(e, alias)]), r1),
{
}

} // verus!
