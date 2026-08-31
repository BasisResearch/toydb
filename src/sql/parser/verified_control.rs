//! Verified concrete parser for the **complete** toyDB statement grammar. Every
//! kind the legacy `parse_statement` dispatches is covered: `BEGIN` / `COMMIT` /
//! `ROLLBACK` (control), `CREATE TABLE` / `DROP TABLE` (DDL, with full column
//! definitions), the row-carrying DML `DELETE` / `INSERT` / `UPDATE` / `SELECT`
//! (whose predicates, values, and clause expressions are parsed by the verified
//! expression parser), and `EXPLAIN <statement>` (recursing through the entry
//! point, rejecting nested EXPLAIN). `SELECT` covers the full clause set: select
//! list with aliases, the `FROM` join tree (INNER/LEFT/RIGHT/CROSS, left-deep
//! folded), `WHERE`, `GROUP BY`, `HAVING`, `ORDER BY` (with direction), `LIMIT`,
//! and `OFFSET`. See `verus-parser-roundtrip-plan.md`. Each entry is a 1:1 port
//! of the corresponding `parser.rs` routine, producing the production
//! `ast::Statement` over `super::Token` and returning the position past the
//! consumed tokens (so the caller can check for a trailing semicolon / end of
//! input, exactly like the legacy path); on any malformed form it returns
//! `(None, pos)` and the retained legacy parser re-parses to own the error text.
//!
//! Verus proves no panic, no arithmetic overflow, and termination: every `Vec`
//! index is bounds-guarded, every `cur + 1` is bounded by the token count, and
//! every clause loop `decreases toks.len() - cur` on a strictly-advancing
//! cursor.
//!
//! Functional specification (phase 2, in progress): a subset of the clause
//! parsers additionally carry a *full refinement* against the spec twins in
//! `verified_stmt_prec`, whose expression positions are `sparse_prec` (unlike
//! `verified_stmt::sparse_stmt`, which uses the fully-parenthesised grammar).
//! `parse_delete_at`, `parse_drop_at`, `parse_begin_at`, `parse_order_by_at`,
//! and `parse_group_by_at` are proven to produce exactly the AST their spec twin
//! (`sparse_control_delete` / `_drop` / `_begin` / `_order_by` / `_group_by`)
//! computes, up to `verified_stmt::view_stmt` / `view_order_list` /
//! `verified_roundtrip::view_args`, with the leftover-token stream pinned — so
//! e.g. mis-defaulting an `ORDER BY` direction or dropping `IF EXISTS` now breaks
//! verification, not just the goldenscript suite. The remaining dispatch
//! (`parse_control_at`) and clause parsers (SELECT list, FROM join tree, INSERT
//! rows, UPDATE assignments, CREATE columns, EXPLAIN) still carry only the
//! no-panic/terminate/error-on-reject contract; their accepted ASTs and
//! rejection errors are pinned by the goldenscript suite. Embedded
//! expressions are parsed by `verified_precedence`, which additionally carries a
//! print/parse roundtrip proof. On rejection each parser returns a structured
//! [`super::parse_error::ParseError`], rendered to the production error string.

// Proof/verification scaffolding, not idiomatic library code.
#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::parse_error::ParseError;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, Token, ast, verified_integer, verified_precedence};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{verified_production, verified_roundtrip, verified_stmt, verified_stmt_prec};
use crate::sql::types::DataType;
use std::collections::BTreeMap;

verus! {

/// Parses a statement at `pos`, dispatching on the leading keyword, and returns
/// it with the position past its tokens — or `(None, pos)` if the token at `pos`
/// does not begin a statement, or the statement is malformed (so the caller
/// falls back to the legacy parser, which owns the specific error). This is the
/// module's entry point; it now covers every statement kind the legacy
/// `parse_statement` dispatches. The `decreases` measure pairs with
/// `parse_explain_at` for their mutual recursion (`EXPLAIN <statement>`): the
/// second component orders the two functions at an equal token position.
pub fn parse_control_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
    decreases toks.len() - pos, 0int,
{
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    match &toks[pos] {
        Token::Keyword(Keyword::Commit) => (Some(ast::Statement::Commit), pos + 1, None),
        Token::Keyword(Keyword::Rollback) => (Some(ast::Statement::Rollback), pos + 1, None),
        Token::Keyword(Keyword::Begin) => parse_begin_at(toks, pos + 1),
        Token::Keyword(Keyword::Drop) => parse_drop_at(toks, pos + 1),
        Token::Keyword(Keyword::Delete) => parse_delete_at(toks, pos + 1),
        Token::Keyword(Keyword::Insert) => parse_insert_at(toks, pos + 1),
        Token::Keyword(Keyword::Update) => parse_update_at(toks, pos + 1),
        Token::Keyword(Keyword::Create) => parse_create_at(toks, pos + 1),
        Token::Keyword(Keyword::Select) => parse_select_at(toks, pos + 1),
        Token::Keyword(Keyword::Explain) => parse_explain_at(toks, pos + 1),
        _ => (None, pos, Some(ParseError::UnexpectedToken(toks[pos].clone()))),
    }
}

/// Parses an `EXPLAIN <statement>` statement, having consumed `EXPLAIN`. The
/// inner statement is parsed by `parse_control_at`; a nested `EXPLAIN` is
/// rejected here (like the legacy parser, which errors) by yielding
/// `(None, pos)`. Mirrors `parse_explain`. The `decreases` second component
/// (`1int` vs `parse_control_at`'s `0int`) breaks the equal-position mutual
/// recursion: `parse_explain_at(pos)` calls `parse_control_at(pos)` at the same
/// `pos`, and `1int > 0int` makes that call strictly smaller.
fn parse_explain_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
    decreases toks.len() - pos, 1int,
{
    // Nested EXPLAIN is disallowed; defer to legacy for the specific error.
    if pos < toks.len() && matches!(toks[pos], Token::Keyword(Keyword::Explain)) {
        return (None, pos, Some(ParseError::NestedExplain));
    }
    let (opt, newpos, e) = parse_control_at(toks, pos);
    match opt {
        Some(inner) => (Some(ast::Statement::Explain(Box::new(inner))), newpos, None),
        None => (None, pos, e),
    }
}

/// Parses a required expression clause at `pos` (the caller has already consumed
/// the leading keyword), wrapping the verified expression parser with the
/// guarded fuel computation. `(None, pos)` on a parse failure or overflow.
fn parse_clause_expr_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Expression>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        // On a realistically-sized input, refines `sparse_prec` at the fuel the
        // caller (statement parser) always hands the expression parser.
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_precedence::sparse_prec(input, 0, verified_stmt_prec::expr_fuel(input));
            match r.0 {
                Some(e) => sopt is Some
                    && verified_roundtrip::view_expr(e) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let n = toks.len() - pos;
    if n > (usize::MAX - 3) / 2 {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let fuel = 2 * n + 3;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    verified_precedence::parse_expression_at(toks, pos, 0, fuel)
}

/// Parses a `SELECT` statement's clauses, having consumed the leading `SELECT`
/// keyword: the select list, then optional `FROM` / `WHERE` / `GROUP BY` /
/// `HAVING` / `ORDER BY` / `LIMIT` / `OFFSET`. Mirrors `parse_select`; a
/// malformed clause yields `(None, pos)` so the caller falls back to legacy.
fn parse_select_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
{
    // Select list (the `SELECT` keyword is already consumed).
    let (sopt, c1, serr) = parse_select_list_at(toks, pos);
    let select = match sopt {
        Some(s) => s,
        None => return (None, pos, serr),
    };
    let mut cur = c1;

    // FROM
    let (fopt, c2, ferr) = parse_from_clause_at(toks, cur);
    let from = match fopt {
        Some(f) => f,
        None => return (None, pos, ferr),
    };
    cur = c2;

    // WHERE
    let mut where_clause: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        cur = cur + 1;
        let (opt, c, werr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                where_clause = Some(e);
                cur = c;
            },
            None => return (None, pos, werr),
        }
    }

    // GROUP BY
    let (gopt, cg, gerr) = parse_group_by_at(toks, cur);
    let group_by = match gopt {
        Some(g) => g,
        None => return (None, pos, gerr),
    };
    cur = cg;

    // HAVING
    let mut having: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Having)) {
        cur = cur + 1;
        let (opt, c, herr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                having = Some(e);
                cur = c;
            },
            None => return (None, pos, herr),
        }
    }

    // ORDER BY
    let (oopt, co, oerr) = parse_order_by_at(toks, cur);
    let order_by = match oopt {
        Some(o) => o,
        None => return (None, pos, oerr),
    };
    cur = co;

    // LIMIT
    let mut limit: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Limit)) {
        cur = cur + 1;
        let (opt, c, lerr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                limit = Some(e);
                cur = c;
            },
            None => return (None, pos, lerr),
        }
    }

    // OFFSET
    let mut offset: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Offset)) {
        cur = cur + 1;
        let (opt, c, ferr2) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                offset = Some(e);
                cur = c;
            },
            None => return (None, pos, ferr2),
        }
    }

    let statement = ast::Statement::Select {
        select,
        from,
        where_clause,
        group_by,
        having,
        order_by,
        offset,
        limit,
    };
    (Some(statement), cur, None)
}

/// Parses the `SELECT` list (one or more `<expr> [[AS] <alias>]`, comma
/// separated), having consumed the `SELECT` keyword. `*` (the `All`
/// expression) cannot be aliased. Mirrors `parse_select_clause`.
fn parse_select_list_at(toks: &Vec<Token>, pos: usize) -> (r: (
    Option<Vec<(ast::Expression, Option<String>)>>,
    usize,
    Option<ParseError>,
))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
{
    let mut select: Vec<(ast::Expression, Option<String>)> = Vec::new();
    let mut cur = pos;
    loop
        invariant
            pos <= cur,
            cur <= toks.len(),
        decreases toks.len() - cur,
    {
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => return (None, pos, eerr),
        };
        cur = c;

        // Optional alias: `AS <ident>` or a bare `<ident>`.
        let is_as = cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As));
        let is_ident = cur < toks.len() && matches!(toks[cur], Token::Ident(_));
        let mut alias: Option<String> = None;
        if is_as || is_ident {
            if matches!(expr, ast::Expression::All) {
                return (None, pos, Some(ParseError::CantAliasStar)); // can't alias *
            }
            if is_as {
                cur = cur + 1;
                if cur >= toks.len() {
                    return (None, pos, Some(ParseError::UnexpectedEof));
                }
            }
            match &toks[cur] {
                Token::Ident(name) => {
                    alias = Some(name.clone());
                    cur = cur + 1;
                },
                _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
            }
        }
        select.push((expr, alias));

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            cur = cur + 1;
        } else {
            break;
        }
    }
    (Some(select), cur, None)
}

/// Parses an optional `FROM` clause: a comma-separated list of join trees.
/// Returns `(Some(vec![]), pos)` when no `FROM` keyword is present. Mirrors
/// `parse_from_clause` (including the left-deep join folding).
fn parse_from_clause_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<Vec<ast::From>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
{
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::From)) {
        return (Some(Vec::new()), pos, None);
    }
    let mut cur = pos + 1;
    let mut from: Vec<ast::From> = Vec::new();
    loop
        invariant
            pos < cur,
            cur <= toks.len(),
        decreases toks.len() - cur,
    {
        // Base table for this from-item.
        let (topt, tc, terr) = parse_from_table_at(toks, cur);
        let mut from_item = match topt {
            Some(t) => t,
            None => return (None, pos, terr),
        };
        cur = tc;

        // Snapshot the post-base-table position: the join loop only advances
        // `cur`, so the outer from-list loop's `decreases` sees strict progress.
        let ghost item_start = cur;
        // Fold any joins into a left-deep tree.
        loop
            invariant
                pos < item_start <= cur,
                cur <= toks.len(),
            decreases toks.len() - cur,
        {
            if cur >= toks.len() {
                break;
            }
            let join_type: ast::JoinType;
            let jc: usize;
            match &toks[cur] {
                Token::Keyword(Keyword::Join) => {
                    join_type = ast::JoinType::Inner;
                    jc = cur + 1;
                },
                Token::Keyword(Keyword::Cross) => {
                    if cur + 1 >= toks.len() {
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    if !matches!(toks[cur + 1], Token::Keyword(Keyword::Join)) {
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[cur + 1].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Cross;
                    jc = cur + 2;
                },
                Token::Keyword(Keyword::Inner) => {
                    if cur + 1 >= toks.len() {
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    if !matches!(toks[cur + 1], Token::Keyword(Keyword::Join)) {
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[cur + 1].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Inner;
                    jc = cur + 2;
                },
                Token::Keyword(Keyword::Left) => {
                    let mut c = cur + 1;
                    if c < toks.len() && matches!(toks[c], Token::Keyword(Keyword::Outer)) {
                        c = c + 1;
                    }
                    if c >= toks.len() {
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    if !matches!(toks[c], Token::Keyword(Keyword::Join)) {
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[c].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Left;
                    jc = c + 1;
                },
                Token::Keyword(Keyword::Right) => {
                    let mut c = cur + 1;
                    if c < toks.len() && matches!(toks[c], Token::Keyword(Keyword::Outer)) {
                        c = c + 1;
                    }
                    if c >= toks.len() {
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    if !matches!(toks[c], Token::Keyword(Keyword::Join)) {
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[c].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Right;
                    jc = c + 1;
                },
                _ => break, // no join keyword: this from-item is complete
            }

            // Right table of the join.
            let (ropt, rc, rerr) = parse_from_table_at(toks, jc);
            let right = match ropt {
                Some(t) => t,
                None => return (None, pos, rerr),
            };
            let mut cur2 = rc;

            // ON <predicate>, except for CROSS joins.
            let mut predicate: Option<ast::Expression> = None;
            if !matches!(join_type, ast::JoinType::Cross) {
                if cur2 >= toks.len() {
                    return (None, pos, Some(ParseError::UnexpectedEof));
                }
                if !matches!(toks[cur2], Token::Keyword(Keyword::On)) {
                    return (None, pos, Some(ParseError::ExpectedToken(
                        Token::Keyword(Keyword::On),
                        toks[cur2].clone(),
                    )));
                }
                cur2 = cur2 + 1;
                let (opt, c, perr) = parse_clause_expr_at(toks, cur2);
                match opt {
                    Some(e) => {
                        predicate = Some(e);
                        cur2 = c;
                    },
                    None => return (None, pos, perr),
                }
            }

            from_item = ast::From::Join {
                left: Box::new(from_item),
                right: Box::new(right),
                join_type,
                predicate,
            };
            cur = cur2;
        }

        from.push(from_item);
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            cur = cur + 1;
        } else {
            break;
        }
    }
    (Some(from), cur, None)
}

/// Parses a `FROM` table (`<name> [[AS] <alias>]`), strictly advancing on
/// success (a table always consumes its name). Mirrors `parse_from_table`.
fn parse_from_table_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::From>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
{
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let name = match &toks[pos] {
        Token::Ident(n) => n.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone()))),
    };
    let mut cur = pos + 1;

    // Optional alias: `AS <ident>` or a bare `<ident>`.
    let is_as = cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As));
    let is_ident = cur < toks.len() && matches!(toks[cur], Token::Ident(_));
    let mut alias: Option<String> = None;
    if is_as || is_ident {
        if is_as {
            cur = cur + 1;
            if cur >= toks.len() {
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
        }
        match &toks[cur] {
            Token::Ident(n) => {
                alias = Some(n.clone());
                cur = cur + 1;
            },
            _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
        }
    }
    (Some(ast::From::Table { name, alias }), cur, None)
}

/// Parses an optional `GROUP BY <expr> [, ...]` clause. Returns
/// `(Some(vec![]), pos)` when no `GROUP` keyword is present. Mirrors
/// `parse_group_by_clause`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_group_by_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<Vec<ast::Expression>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_group_by(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_roundtrip::view_args(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    }
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::Group)) {
        return (Some(Vec::new()), pos, None);
    }
    let mut cur = pos + 1;
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::By)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::By),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    proof {
        assert(toks@[pos as int] == Token::Keyword(Keyword::Group));
        assert(toks@[(pos + 1) as int] == Token::Keyword(Keyword::By));
    }
    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_group_list(list_start);
    proof {
        order_by_input_head(toks, pos);
        assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
        assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
        assert(list_start == input.drop_first().drop_first());
    }
    let mut group_by: Vec<ast::Expression> = Vec::new();
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Group),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_group_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == verified_stmt_prec::group_list_prepend(
                    verified_roundtrip::view_args(group_by@),
                    list_start,
                    verified_stmt_prec::sparse_control_group_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Group),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_group_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == (Some(verified_roundtrip::view_args(group_by@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_roundtrip::view_args(group_by@);
        let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => {
                proof {
                    if sized {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_group_list, 1);
                        assert(verified_stmt_prec::sparse_control_group_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        order_by_input_head(toks, pos);
                        group_by_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, eerr);
            },
        };
        let ghost r_after_expr = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_precedence::sparse_prec(cur_v, 0, verified_stmt_prec::expr_fuel(cur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            if sized && c < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, c as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int));
            }
        }
        cur = c;
        let ghost old_group = group_by@;
        group_by.push(expr);
        proof {
            verified_stmt_prec::lemma_view_args_append(old_group, seq![expr]);
            verified_stmt_prec::lemma_view_args_single(expr);
            assert(group_by@ == old_group + seq![expr]);
            assert(verified_roundtrip::view_args(group_by@)
                == done_v + seq![verified_roundtrip::view_expr(expr)]);
        }

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    verified_stmt_prec::lemma_group_list_step(
                        cur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_after_expr.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    assert(whole == verified_stmt_prec::group_list_prepend(
                        done_v, list_start, verified_stmt_prec::sparse_control_group_list(cur_v)));
                    assert(verified_stmt_prec::sparse_control_group_list(cur_v)
                        == verified_stmt_prec::group_list_prepend(
                            seq![verified_roundtrip::view_expr(expr)], cur_v,
                            verified_stmt_prec::sparse_control_group_list(r_after_expr.drop_first())));
                    verified_stmt_prec::lemma_group_list_resume_step(
                        list_start, cur_v, r_after_expr.drop_first(),
                        done_v, verified_roundtrip::view_expr(expr), whole);
                    assert(verified_roundtrip::view_args(group_by@)
                        == done_v + seq![verified_roundtrip::view_expr(expr)]);
                    assert(whole == verified_stmt_prec::group_list_prepend(
                        verified_roundtrip::view_args(group_by@),
                        list_start,
                        verified_stmt_prec::sparse_control_group_list(
                            verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)))));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_group_list_last(
                        cur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                    assert(verified_stmt_prec::sparse_control_group_list(cur_v)
                        == (Some(seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                    assert(whole == (Some(done_v
                        + seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                    assert(verified_roundtrip::view_args(group_by@)
                        == done_v + seq![verified_roundtrip::view_expr(expr)]);
                    assert(whole == (Some(verified_roundtrip::view_args(group_by@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
            break;
        }
    }
    proof {
        if toks.len() <= (usize::MAX - 3) / 2 {
            group_by_conclude_some(toks, pos, cur, list_start, whole,
                verified_roundtrip::view_args(group_by@));
        }
    }
    (Some(group_by), cur, None)
}

/// Head facts for the `parse_order_by_at` input at `pos` when at least two
/// tokens remain: relates `input[0]`/`input[1]` to the tokens and pins the
/// list-start suffix. Factored out to keep both the reject and accept exits of
/// `parse_order_by_at` small.
proof fn order_by_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 2 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 2,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
}

/// Concludes the reject case of `parse_order_by_at`: given the `ORDER BY` head
/// tokens and `whole` (the list parse from `list_start`) rejecting, the whole
/// `sparse_control_order_by(input)` rejects. Isolated so the deeply-nested loop
/// exit stays legible.
proof fn order_by_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<(verified_roundtrip::SExpr, ast::Direction)>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Order),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_order_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_order_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

/// Accept case: `sparse_control_order_by(input)` equals the final accumulated
/// list result `(Some(items), rest)`.
proof fn order_by_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<(verified_roundtrip::SExpr, ast::Direction)>>, Seq<verified_production::TokenView>),
    items: Seq<(verified_roundtrip::SExpr, ast::Direction)>,
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Order),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_order_list(list_start),
        whole == (Some(items),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_order_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(items),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

/// Concludes the reject case of `parse_group_by_at`: given the `GROUP BY` head
/// tokens and `whole` (the list parse from `list_start`) rejecting, the whole
/// `sparse_control_group_by(input)` rejects. Mirrors `order_by_conclude_none`.
proof fn group_by_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_roundtrip::SExpr>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Group),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_group_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_group_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

/// Accept case: `sparse_control_group_by(input)` equals the final accumulated
/// list result `(Some(items), rest)`. Mirrors `order_by_conclude_some`.
proof fn group_by_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_roundtrip::SExpr>>, Seq<verified_production::TokenView>),
    items: Seq<verified_roundtrip::SExpr>,
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Group),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_group_list(list_start),
        whole == (Some(items),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_group_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(items),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

/// Parses an optional `ORDER BY <expr> [ASC|DESC] [, ...]` clause. Returns
/// `(Some(vec![]), pos)` when no `ORDER` keyword is present. Mirrors
/// `parse_order_by_clause`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_order_by_at(toks: &Vec<Token>, pos: usize) -> (r: (
    Option<Vec<(ast::Expression, ast::Direction)>>,
    usize,
    Option<ParseError>,
))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_order_by(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_stmt::view_order_list(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    }
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::Order)) {
        return (Some(Vec::new()), pos, None);
    }
    let mut cur = pos + 1;
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::By)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::By),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    // Pin the `ORDER` / `BY` head tokens as structural facts (from the guards).
    proof {
        assert(toks@[pos as int] == Token::Keyword(Keyword::Order));
        assert(toks@[(pos + 1) as int] == Token::Keyword(Keyword::By));
    }
    // `list_start` — the suffix just past `ORDER BY`, where the item list begins.
    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_order_list(list_start);
    proof {
        order_by_input_head(toks, pos);
        assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
        assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
        assert(list_start == input.drop_first().drop_first());
    }
    let mut order_by: Vec<(ast::Expression, ast::Direction)> = Vec::new();
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Order),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_order_list(list_start),
            // Resumption: the whole list equals what's been consumed (`order_by`)
            // prepended onto the parse continuing at `cur`. Only meaningful on a
            // realistically-sized input (where the expression parser refines).
            // Holds each iteration but NOT at break (post-terminal-item `cur`
            // would start a fresh parse); the break state is pinned by `ensures`.
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == verified_stmt_prec::order_list_prepend(
                    verified_stmt::view_order_list(order_by@),
                    list_start,
                    verified_stmt_prec::sparse_control_order_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Order),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_order_list(list_start),
            // At break the accumulated list is final: the whole parse is exactly
            // `(Some(view_order_list(order_by@)), suffix-at-cur)`.
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == (Some(verified_stmt::view_order_list(order_by@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_order_list(order_by@);
        let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => {
                // `sparse_prec(cur_v) is None`, so `sparse_control_order_list(cur_v)`
                // is `(None, cur_v)`, hence `whole == (None, list_start)`, hence
                // `sparse_control_order_by(input) is None`.
                proof {
                    if sized {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_order_list, 1);
                        assert(verified_stmt_prec::sparse_control_order_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        order_by_input_head(toks, pos);
                        order_by_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, eerr);
            },
        };
        let ghost r_after_expr = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
        proof {
            // parse_clause_expr_at's (gated) refinement pins the sparse_prec result.
            if sized {
                assert(verified_precedence::sparse_prec(cur_v, 0, verified_stmt_prec::expr_fuel(cur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            if sized && c < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, c as int);  // r_after_expr head
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int));
            }
        }
        cur = c;

        // Optional direction; defaults to ascending. `dir_consumed` records
        // whether an ASC/DESC token was eaten, pinning `r1` for the spec lemmas.
        let mut direction = ast::Direction::Ascending;
        let ghost c_head_is_dir: bool = r_after_expr.len() >= 1
            && (r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Asc)
                || r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Desc));
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
            match &toks[cur] {
                Token::Keyword(Keyword::Asc) => {
                    direction = ast::Direction::Ascending;
                    cur = cur + 1;
                },
                Token::Keyword(Keyword::Desc) => {
                    direction = ast::Direction::Descending;
                    cur = cur + 1;
                },
                _ => {},
            }
        } else {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        }
        let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        proof {
            // Pin the direction/`r1` relations that the step/last lemmas require.
            // `r_after_expr[0] == token_view(toks[c])` (when c < len) drives the
            // exec match, so the ghost direction-guards agree with the exec choice.
            if sized {
                if c_head_is_dir {
                    // ASC or DESC was consumed: r1 == r_after_expr.drop_first().
                    assert(r1 == r_after_expr.drop_first());
                    assert(r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Asc)
                        ==> direction == ast::Direction::Ascending);
                    assert(r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Desc)
                        ==> direction == ast::Direction::Descending);
                } else {
                    // No direction token: r1 == r_after_expr, direction default.
                    assert(r1 == r_after_expr);
                    assert(direction == ast::Direction::Ascending);
                }
            }
        }
        let ghost old_order = order_by@;
        order_by.push((expr, direction));
        proof {
            // order_by view distributes: done_v ++ [(view_expr(expr), direction)].
            verified_stmt_prec::lemma_view_order_list_append(old_order, seq![(expr, direction)]);
            verified_stmt_prec::lemma_view_order_list_single(expr, direction);
            assert(order_by@ == old_order + seq![(expr, direction)]);
            assert(verified_stmt::view_order_list(order_by@)
                == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
        }

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    // Step: `sparse_control_order_list(cur_v)` prepends the item and
                    // recurses at the post-comma suffix.
                    verified_stmt_prec::lemma_order_list_step(
                        cur_v, verified_roundtrip::view_expr(expr), direction, r_after_expr, r1);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r1.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    // Precondition #1 (entry invariant) and #2 (step lemma) for resume_step.
                    assert(whole == verified_stmt_prec::order_list_prepend(
                        done_v, list_start, verified_stmt_prec::sparse_control_order_list(cur_v)));
                    assert(verified_stmt_prec::sparse_control_order_list(cur_v)
                        == verified_stmt_prec::order_list_prepend(
                            seq![(verified_roundtrip::view_expr(expr), direction)], cur_v,
                            verified_stmt_prec::sparse_control_order_list(r1.drop_first())));
                    // Re-establish the resumption invariant after appending one item.
                    verified_stmt_prec::lemma_order_list_resume_step(
                        list_start, cur_v, r1.drop_first(),
                        done_v, verified_roundtrip::view_expr(expr), direction, whole);
                    // Bridge the lemma's `done_v + [item]` to `view_order_list(order_by@)`
                    // and `r1.drop_first()` to the new current suffix.
                    assert(verified_stmt::view_order_list(order_by@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
                    assert(whole == verified_stmt_prec::order_list_prepend(
                        verified_stmt::view_order_list(order_by@),
                        list_start,
                        verified_stmt_prec::sparse_control_order_list(
                            verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)))));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_order_list_last(
                        cur_v, verified_roundtrip::view_expr(expr), direction, r_after_expr, r1);
                    // whole == prepend(done_v, ls, (Some([item]), r1)) == (Some(done_v+[item]), r1).
                    assert(verified_stmt_prec::sparse_control_order_list(cur_v)
                        == (Some(seq![(verified_roundtrip::view_expr(expr), direction)]), r1));
                    assert(whole == (Some(done_v
                        + seq![(verified_roundtrip::view_expr(expr), direction)]), r1));
                    assert(verified_stmt::view_order_list(order_by@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
                    // These survive the break as path facts (cur is final here).
                    assert(whole == (Some(verified_stmt::view_order_list(order_by@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
            break;
        }
    }
    proof {
        // `sparse_control_order_by` unfolds to `sparse_control_order_list(list_start)
        // == whole`, which the break-ensures pinned to the final list result.
        if toks.len() <= (usize::MAX - 3) / 2 {
            order_by_conclude_some(toks, pos, cur, list_start, whole,
                verified_stmt::view_order_list(order_by@));
        }
    }
    (Some(order_by), cur, None)
}

/// Parses a `CREATE TABLE <name> (<column>, ...)` statement, having consumed
/// `CREATE`. Each column definition is parsed by `parse_create_column_at`.
/// Mirrors `parse_create_table`; a malformed form yields `(None, pos)` so the
/// caller falls back to the legacy parser.
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_create_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        // Full refinement against `sparse_control_create`, up to `view_stmt`.
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_create(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }

    // TABLE
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); reveal(verified_production::token_view); }
    if !matches!(toks[pos], Token::Keyword(Keyword::Table)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Table),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    // Table name.
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    let name = match &toks[cur] {
        Token::Ident(n) => n.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    proof { assert(input[1] == verified_production::TokenView::Ident(name)); }
    cur = cur + 1;

    // Opening paren of the column list.
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    if !matches!(toks[cur], Token::OpenParen) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::OpenParen,
            toks[cur].clone(),
        )));
    }
    proof { assert(input[2] == verified_production::TokenView::OpenParen); }
    cur = cur + 1;

    // The column-list start suffix and its whole-parse against the spec twin.
    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_column_list(list_start);
    proof {
        assert(cur == pos + 3);
        create_input_head(toks, pos);
        assert(list_start == input.drop_first().drop_first().drop_first());
    }

    // One or more comma-separated column definitions.
    let mut columns: Vec<ast::Column> = Vec::new();
    loop
        invariant_except_break
            pos + 3 <= cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            input[0] == verified_production::TokenView::Keyword(Keyword::Table),
            input[1] == verified_production::TokenView::Ident(name),
            input[2] == verified_production::TokenView::OpenParen,
            toks@[pos as int] == Token::Keyword(Keyword::Table),
            toks@[(pos + 2) as int] == Token::OpenParen,
            list_start == verified_production::token_views(
                toks@.subrange((pos + 3) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_column_list(list_start),
            sized ==> whole == verified_stmt_prec::column_list_prepend(
                verified_stmt::view_columns(columns@),
                list_start,
                verified_stmt_prec::sparse_control_column_list(
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
        ensures
            pos + 3 <= cur,
            cur <= toks.len(),
            input[0] == verified_production::TokenView::Keyword(Keyword::Table),
            input[1] == verified_production::TokenView::Ident(name),
            input[2] == verified_production::TokenView::OpenParen,
            list_start == verified_production::token_views(
                toks@.subrange((pos + 3) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_column_list(list_start),
            sized ==> whole == (Some(verified_stmt::view_columns(columns@)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_columns(columns@);
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (copt, ncur, cerr) = parse_create_column_at(toks, cur);
        let column = match copt {
            Some(c) => c,
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_column(cur_v).0 is None);
                        assert(verified_stmt_prec::sparse_control_column_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        create_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, cerr);
            },
        };
        let ghost r_after_col = verified_production::token_views(toks@.subrange(ncur as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_column(cur_v)
                    == (Some(verified_stmt::view_column(column)), r_after_col));
            }
        }
        cur = ncur;
        let ghost old_cols = columns@;
        columns.push(column);
        proof {
            verified_stmt_prec::lemma_view_columns_append(old_cols, seq![column]);
            verified_stmt_prec::lemma_view_columns_single(column);
            assert(columns@ == old_cols + seq![column]);
            assert(verified_stmt::view_columns(columns@)
                == done_v + seq![verified_stmt::view_column(column)]);
        }
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                if sized {
                    verified_stmt_prec::lemma_column_list_step(
                        cur_v, verified_stmt::view_column(column), r_after_col);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_after_col.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    verified_stmt_prec::lemma_column_list_resume_step(
                        list_start, cur_v, r_after_col.drop_first(),
                        done_v, verified_stmt::view_column(column), whole);
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                    reveal(verified_production::token_view);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_column_list_last(
                        cur_v, verified_stmt::view_column(column), r_after_col);
                    assert(verified_stmt_prec::sparse_control_column_list(cur_v)
                        == (Some(seq![verified_stmt::view_column(column)]), r_after_col));
                }
            }
            break;
        }
    }
    let ghost after_list = cur;

    // Closing paren.
    proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
    if cur >= toks.len() {
        proof {
            if sized {
                create_conclude_reject_close(toks, pos, cur, list_start, whole,
                    verified_stmt::view_columns(columns@));
            }
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    if !matches!(toks[cur], Token::CloseParen) {
        proof {
            if sized {
                create_conclude_reject_close(toks, pos, cur, list_start, whole,
                    verified_stmt::view_columns(columns@));
            }
        }
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::CloseParen,
            toks[cur].clone(),
        )));
    }
    let ghost close_at = cur;
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    cur = cur + 1;

    proof {
        if sized {
            create_conclude_some(toks, pos, close_at, cur, list_start, whole,
                verified_stmt::view_columns(columns@), name);
        }
    }
    (Some(ast::Statement::CreateTable { name, columns }), cur, None)
}

/// Head facts for a `parse_create_at` input at `pos` when at least three tokens
/// remain: `input[0..2]` are `TABLE`, the table ident, and `(`, and the
/// column-list start is `input.drop_first()^3`.
proof fn create_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 3 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 3,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[2]
            == verified_production::token_view(toks@[(pos + 2) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 3) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 2) as int);
}

/// Reject bridge: the column list from `list_start` rejects, so
/// `sparse_control_create(input)` rejects.
proof fn create_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 3 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 2) as int] == Token::OpenParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
}

/// Reject bridge for a missing / wrong close paren after the accepted list.
proof fn create_conclude_reject_close(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
    cols: Seq<verified_stmt::SColumn>,
)
    requires
        pos + 3 <= toks.len(),
        cur <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 2) as int] == Token::OpenParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole == (Some(cols),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        !(cur < toks.len() && toks@[cur as int] == Token::CloseParen),
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
    let r3 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
    if cur < toks.len() {
        verified_roundtrip::token_views_suffix(toks@, cur as int);
        assert(r3[0] == verified_production::token_view(toks@[cur as int]));
        assert(r3[0] != verified_production::TokenView::CloseParen);
    } else {
        assert(r3.len() == 0);
    }
}

/// Accept bridge: the whole statement, with the close paren consumed at
/// `close_at`, equals `sparse_control_create(input) == (Some(CreateTable), rest)`.
proof fn create_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    close_at: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
    cols: Seq<verified_stmt::SColumn>,
    name: String,
)
    requires
        pos + 3 <= toks.len(),
        close_at < toks.len(),
        cur == close_at + 1,
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 1) as int] == Token::Ident(name),
        toks@[(pos + 2) as int] == Token::OpenParen,
        toks@[close_at as int] == Token::CloseParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole == (Some(cols),
            verified_production::token_views(toks@.subrange(close_at as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(verified_stmt::SStmt::CreateTable { name, columns: cols }),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[1] == verified_production::TokenView::Ident(name));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
    let r3 = verified_production::token_views(toks@.subrange(close_at as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, close_at as int);
    assert(r3[0] == verified_production::TokenView::CloseParen);
    assert(r3.drop_first() == verified_production::token_views(
        toks@.subrange(cur as int, toks@.len() as int)));
}

/// Parses a single `CREATE TABLE` column definition (`<name> <datatype>
/// <constraint>*`) at `pos`. Constraints are the keyword-led clauses
/// `PRIMARY KEY`, `[NOT] NULL`, `DEFAULT <expr>`, `UNIQUE`, `INDEX`, and
/// `REFERENCES <table>`; the clause loop ends at the first non-keyword token.
/// Returns `(None, pos)` on any malformed / unexpected keyword. Mirrors
/// `parse_create_table_column`; strictly advances on success (a column always
/// consumes at least its name and datatype).
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_create_column_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Column>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        // Full refinement: the produced column and leftover token stream agree
        // with the spec twin `sparse_control_column`, up to `view_column`.
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_column(input);
            match r.0 {
                Some(c) => sopt is Some
                    && verified_stmt::view_column(c) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }

    // Column name.
    if pos >= toks.len() {
        // Empty input: `sparse_control_column` rejects.
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); reveal(verified_production::token_view); }
    let name = match &toks[pos] {
        Token::Ident(n) => n.clone(),
        _ => {
            // `input[0]` is not an ident: `sparse_control_column` rejects.
            proof { assert(!(input[0] is Ident)); }
            return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone())));
        },
    };
    proof { assert(input[0] == verified_production::TokenView::Ident(name)); }
    let mut cur = pos + 1;

    // Datatype keyword.
    if cur >= toks.len() {
        // No token after the name: `input.drop_first().len() < 1`, reject.
        proof {
            verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
            verified_roundtrip::token_views_suffix(toks@, pos as int);
            assert(input.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        verified_roundtrip::token_views_suffix(toks@, cur as int);
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        reveal(verified_production::token_view);
        assert(input.drop_first() == verified_production::token_views(
            toks@.subrange(cur as int, toks@.len() as int)));
        assert(input[1] == verified_production::token_view(toks@[cur as int]));
    }
    let datatype = match &toks[cur] {
        Token::Keyword(Keyword::Bool) | Token::Keyword(Keyword::Boolean) => DataType::Boolean,
        Token::Keyword(Keyword::Float) | Token::Keyword(Keyword::Double) => DataType::Float,
        Token::Keyword(Keyword::Int) | Token::Keyword(Keyword::Integer) => DataType::Integer,
        Token::Keyword(Keyword::String)
        | Token::Keyword(Keyword::Text)
        | Token::Keyword(Keyword::Varchar) => DataType::String,
        _ => {
            // `input[1]` is not a datatype keyword: reject.
            proof { assert(verified_stmt_prec::parse_column_datatype_kw(input[1]) is None); }
            return (None, pos, Some(ParseError::UnexpectedToken(toks[cur].clone())));
        },
    };
    // The datatype keyword at `pos+1` maps to `datatype` under the spec mirror,
    // and the name at `pos` is `Ident(name)`; both pin `sparse_control_column`'s
    // prefix reduction.
    proof {
        reveal(verified_production::token_view);
        assert(verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_view(toks@[cur as int])) == Some(datatype));
    }
    cur = cur + 1;

    // Ghost: the constraint-loop start suffix, and the whole constraint parse
    // from it against the spec twin. `input[0]` is the name ident, `input[1]`
    // the datatype keyword, so the spec's `sparse_control_column` reduces to
    // `sparse_control_col_constraints(cstart, name, datatype, empty)`.
    let ghost cstart = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost cwhole = verified_stmt_prec::sparse_control_col_constraints(
        cstart, name, datatype, verified_stmt_prec::col_acc_empty());
    proof {
        assert(cur == pos + 2);
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
        assert(cstart == input.drop_first().drop_first());
        assert(input[0] == verified_production::token_view(toks@[pos as int]));
        assert(input[1] == verified_production::token_view(toks@[(pos + 1) as int]));
        assert(input[0] == verified_production::TokenView::Ident(name));
        assert(verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype));
    }

    // Column constraints; `cur` is now strictly past `pos` (name + datatype).
    let mut primary_key = false;
    let mut nullable: Option<bool> = None;
    let mut default: Option<ast::Expression> = None;
    let mut unique = false;
    let mut index = false;
    let mut references: Option<String> = None;
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            cstart == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            cwhole == verified_stmt_prec::sparse_control_col_constraints(
                cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
            input[0] == verified_production::TokenView::Ident(name),
            verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype),
            // The constraint parse from `cstart` equals continuing from the
            // current suffix with the accumulator reflecting the exec locals.
            sized ==> cwhole == verified_stmt_prec::sparse_control_col_constraints(
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                name, datatype,
                verified_stmt_prec::ColAcc {
                    primary_key,
                    nullable,
                    default: verified_stmt_prec::opt_view_expr(default),
                    unique,
                    index,
                    references,
                }),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            cstart == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            input[0] == verified_production::TokenView::Ident(name),
            verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype),
            // On exit, the whole constraint parse accepts, producing the final
            // column (view) and the current suffix as leftover.
            sized ==> cwhole == (
                Some(verified_stmt::view_column(ast::Column {
                    name, datatype, primary_key, nullable, default, unique, index, references,
                })),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost acc_cur = verified_stmt_prec::ColAcc {
            primary_key,
            nullable,
            default: verified_stmt_prec::opt_view_expr(default),
            unique,
            index,
            references,
        };
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        if cur >= toks.len() {
            // EOF ends the column: `sparse_control_col_constraints(empty, ..)`
            // accepts with `col_from_acc`, which is `view_column` of the column.
            proof {
                if sized {
                    assert(cur_v.len() == 0);
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == (Some(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)), cur_v));
                    assert(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)
                        == verified_stmt::view_column(ast::Column {
                            name, datatype, primary_key, nullable, default, unique, index, references,
                        }));
                }
            }
            break;
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
        // Constraints are keyword-led; a non-keyword token ends the column.
        let keyword = match &toks[cur] {
            Token::Keyword(k) => *k,
            _ => {
                proof {
                    if sized {
                        assert(!(cur_v[0] is Keyword));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                            == (Some(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)), cur_v));
                        assert(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)
                            == verified_stmt::view_column(ast::Column {
                                name, datatype, primary_key, nullable, default, unique, index, references,
                            }));
                    }
                }
                break;
            },
        };
        proof { assert(cur_v[0] == verified_production::TokenView::Keyword(keyword)); }
        let ghost r_after_kw = verified_production::token_views(toks@.subrange((cur + 1) as int, toks@.len() as int));
        proof { assert(cur_v.drop_first() == r_after_kw); }
        cur = cur + 1;
        if matches!(keyword, Keyword::Primary) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            if !matches!(toks[cur], Token::Keyword(Keyword::Key)) {
                proof {
                    if sized {
                        assert(r_after_kw[0] != verified_production::TokenView::Keyword(Keyword::Key));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::ExpectedToken(
                    Token::Keyword(Keyword::Key),
                    toks[cur].clone(),
                )));
            }
            proof {
                assert(r_after_kw[0] == verified_production::TokenView::Keyword(Keyword::Key));
                verified_roundtrip::token_views_suffix(toks@, cur as int);
            }
            cur = cur + 1;
            primary_key = true;
            proof {
                if sized {
                    assert(r_after_kw.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw.drop_first(), name, datatype,
                            verified_stmt_prec::ColAcc { primary_key: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Null) {
            if nullable.is_some() {
                proof {
                    if sized {
                        assert(acc_cur.nullable is Some);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::NullabilityAlreadySet(name.clone())));
            }
            nullable = Some(true);
            proof {
                if sized {
                    assert(!(acc_cur.nullable is Some));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { nullable: Some(true), ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Not) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            if !matches!(toks[cur], Token::Keyword(Keyword::Null)) {
                proof {
                    if sized {
                        assert(r_after_kw[0] != verified_production::TokenView::Keyword(Keyword::Null));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::ExpectedToken(
                    Token::Keyword(Keyword::Null),
                    toks[cur].clone(),
                )));
            }
            proof { assert(r_after_kw[0] == verified_production::TokenView::Keyword(Keyword::Null)); }
            cur = cur + 1;
            if nullable.is_some() {
                proof {
                    if sized {
                        assert(acc_cur.nullable is Some);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::NullabilityAlreadySet(name.clone())));
            }
            nullable = Some(false);
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                if sized {
                    assert(!(acc_cur.nullable is Some));
                    assert(r_after_kw.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw.drop_first(), name, datatype,
                            verified_stmt_prec::ColAcc { nullable: Some(false), ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Default) {
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                // Only reachable when the token count exceeds the spec's size
                // bound, i.e. `!sized`, so the refinement is vacuous here.
                proof { assert(!sized); }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            let (opt, consumed, derr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            match opt {
                Some(expr) => {
                    proof {
                        if sized {
                            let r_e = verified_production::token_views(toks@.subrange(consumed as int, toks@.len() as int));
                            assert(fuel == verified_stmt_prec::expr_fuel(r_after_kw));
                            assert(verified_precedence::sparse_prec(r_after_kw, 0, verified_stmt_prec::expr_fuel(r_after_kw))
                                == (Some(verified_roundtrip::view_expr(expr)), r_e));
                        }
                    }
                    default = Some(expr);
                    cur = consumed;
                    proof {
                        if sized {
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                                == verified_stmt_prec::sparse_control_col_constraints(
                                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                                    name, datatype,
                                    verified_stmt_prec::ColAcc {
                                        default: Some(verified_roundtrip::view_expr(expr)), ..acc_cur }));
                        }
                    }
                },
                None => {
                    proof {
                        if sized {
                            assert(verified_precedence::sparse_prec(r_after_kw, 0, verified_stmt_prec::expr_fuel(r_after_kw)).0 is None);
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                            col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                        }
                    }
                    return (None, pos, derr);
                },
            }
        } else if matches!(keyword, Keyword::Unique) {
            unique = true;
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { unique: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Index) {
            index = true;
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { index: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::References) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            match &toks[cur] {
                Token::Ident(nm) => {
                    let ghost nmv = nm@;
                    references = Some(nm.clone());
                    proof { assert(r_after_kw[0] == verified_production::TokenView::Ident(*nm)); }
                    cur = cur + 1;
                    proof {
                        verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                        if sized {
                            assert(r_after_kw.drop_first() == verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)));
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                                == verified_stmt_prec::sparse_control_col_constraints(
                                    r_after_kw.drop_first(), name, datatype,
                                    verified_stmt_prec::ColAcc { references: references, ..acc_cur }));
                        }
                    }
                },
                _ => {
                    proof {
                        if sized {
                            assert(!(r_after_kw[0] is Ident));
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                            col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                        }
                    }
                    return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone())));
                },
            }
        } else {
            // Unexpected keyword for a column definition: not one of the
            // recognised constraint keywords, so the spec rejects too.
            proof {
                if sized {
                    assert(keyword != Keyword::Primary && keyword != Keyword::Null
                        && keyword != Keyword::Not && keyword != Keyword::Default
                        && keyword != Keyword::Unique && keyword != Keyword::Index
                        && keyword != Keyword::References);
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                    col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedKeyword(keyword)));
        }
    }

    let column = ast::Column {
        name,
        datatype,
        primary_key,
        nullable,
        default,
        unique,
        index,
        references,
    };
    proof {
        if sized {
            col_constraints_accept(toks, pos, cur, cstart, cwhole, name, datatype, column);
        }
    }
    (Some(column), cur, None)
}

/// Reject bridge for `parse_create_column_at`: given the constraint parse from
/// `cur_v` (the current suffix) rejects, and the loop invariant relating it to
/// the whole parse `cwhole` from `cstart`, conclude `sparse_control_column`
/// rejects on the column's input. Isolated so the nested loop stays legible.
proof fn col_constraints_reject(
    toks: &Vec<Token>,
    pos: usize,
    cstart: Seq<verified_production::TokenView>,
    cwhole: (Option<verified_stmt::SColumn>, Seq<verified_production::TokenView>),
    cur_v: Seq<verified_production::TokenView>,
    name: String,
    datatype: DataType,
    acc_cur: verified_stmt_prec::ColAcc,
)
    requires
        pos + 2 <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        cstart == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::TokenView::Ident(name),
        verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]) == Some(datatype),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(
            cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur),
        verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None,
    ensures
        verified_stmt_prec::sparse_control_column(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    col_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(cstart == input.drop_first().drop_first());
    assert(cwhole.0 is None);
}

/// Accept bridge for `parse_create_column_at`: the loop-exit invariant (the
/// whole constraint parse produces `view_column(column)` and the current suffix)
/// lifts to `sparse_control_column(input) == (Some(view_column(column)), rest)`.
proof fn col_constraints_accept(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    cstart: Seq<verified_production::TokenView>,
    cwhole: (Option<verified_stmt::SColumn>, Seq<verified_production::TokenView>),
    name: String,
    datatype: DataType,
    column: ast::Column,
)
    requires
        pos + 2 <= toks.len(),
        cur <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        cstart == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::TokenView::Ident(name),
        verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]) == Some(datatype),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(
            cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
        column.name == name,
        column.datatype == datatype,
        cwhole == (
            Some(verified_stmt::view_column(column)),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_column(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(verified_stmt::view_column(column)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    col_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(cstart == input.drop_first().drop_first());
}

/// Head facts for a `parse_create_column_at` input at `pos` when at least two
/// tokens remain: `input[0]` is the name ident, `input[1]` the datatype keyword,
/// and the constraint-loop start is `input.drop_first().drop_first()`. Pins the
/// prefix so `sparse_control_column` reduces to the constraint parse.
proof fn col_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 2 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 2,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
}

/// Parses an `UPDATE <table> SET <col> = <expr|DEFAULT> [, ...] [WHERE <expr>]`
/// statement, having consumed `UPDATE`. Assignment values and the optional
/// `WHERE` predicate are parsed by the verified expression parser; `DEFAULT`
/// maps to `None`. A duplicate column, like any malformed form, yields
/// `(None, pos)` so the caller falls back to the legacy parser (which also
/// carries the specific error text). Mirrors `parse_update`.
fn parse_update_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
{
    // Table name.
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let table = match &toks[pos] {
        Token::Ident(name) => name.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone()))),
    };
    let mut cur = pos + 1;

    // SET
    if cur >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    if !matches!(toks[cur], Token::Keyword(Keyword::Set)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Set),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;

    // One or more comma-separated `<col> = <value>` assignments.
    let mut set: BTreeMap<String, Option<ast::Expression>> = BTreeMap::new();
    loop
        invariant
            pos <= cur,
            cur <= toks.len(),
        decreases toks.len() - cur,
    {
        // Column name.
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        let column = match &toks[cur] {
            Token::Ident(name) => name.clone(),
            _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
        };
        cur = cur + 1;

        // `=`
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        if !matches!(toks[cur], Token::Equal) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::Equal,
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;

        // Value: the `DEFAULT` keyword maps to `None`; otherwise an expression.
        let value: Option<ast::Expression>;
        if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Default)) {
            cur = cur + 1;
            value = None;
        } else {
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            let (opt, consumed, verr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            match opt {
                Some(expr) => {
                    value = Some(expr);
                    cur = consumed;
                },
                None => return (None, pos, verr),
            }
        }

        // Reject a column set twice (legacy owns the error text).
        if set.contains_key(&column) {
            return (None, pos, Some(ParseError::DuplicateColumn(column.clone())));
        }
        set.insert(column, value);

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            cur = cur + 1;
        } else {
            break;
        }
    }

    // Optional WHERE <expr>.
    let mut where_clause: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        cur = cur + 1;
        let n = toks.len() - cur;
        if n > (usize::MAX - 3) / 2 {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        let fuel = 2 * n + 3;
        let (opt, consumed, werr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
        match opt {
            Some(expr) => {
                where_clause = Some(expr);
                cur = consumed;
            },
            None => return (None, pos, werr),
        }
    }

    (Some(ast::Statement::Update { table, set, where_clause }), cur, None)
}

/// Parses an `INSERT INTO <table> [(<col>, ...)] VALUES (<expr>, ...), ...`
/// statement, having consumed `INSERT`. The row values are parsed by the
/// verified expression parser. Mirrors `parse_insert`; a malformed form yields
/// `(None, pos)` so the caller falls back to the legacy parser.
fn parse_insert_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
{
    // INTO
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    if !matches!(toks[pos], Token::Keyword(Keyword::Into)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Into),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    // Table name.
    if cur >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let table = match &toks[cur] {
        Token::Ident(name) => name.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    cur = cur + 1;

    // Optional parenthesised column list.
    let mut columns: Option<Vec<String>> = None;
    if cur < toks.len() && matches!(toks[cur], Token::OpenParen) {
        cur = cur + 1;
        let mut cols: Vec<String> = Vec::new();
        loop
            invariant
                pos <= cur,
                cur <= toks.len(),
            decreases toks.len() - cur,
        {
            if cur >= toks.len() {
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            match &toks[cur] {
                Token::Ident(name) => {
                    cols.push(name.clone());
                    cur = cur + 1;
                },
                _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
            }
            if cur < toks.len() && matches!(toks[cur], Token::Comma) {
                cur = cur + 1;
            } else {
                break;
            }
        }
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        if !matches!(toks[cur], Token::CloseParen) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::CloseParen,
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        columns = Some(cols);
    }

    // VALUES
    if cur >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    if !matches!(toks[cur], Token::Keyword(Keyword::Values)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Values),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;

    // One or more comma-separated parenthesised rows of expressions.
    let mut values: Vec<Vec<ast::Expression>> = Vec::new();
    loop
        invariant
            pos <= cur,
            cur <= toks.len(),
        decreases toks.len() - cur,
    {
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        if !matches!(toks[cur], Token::OpenParen) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::OpenParen,
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        // Snapshot the post-`(` position: the inner loop only advances `cur`, so
        // the outer loop's `decreases` sees strict progress across a row.
        let ghost row_start = cur;
        let mut row: Vec<ast::Expression> = Vec::new();
        loop
            invariant
                pos <= row_start <= cur,
                cur <= toks.len(),
            decreases toks.len() - cur,
        {
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            let (opt, consumed, verr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            match opt {
                Some(expr) => {
                    row.push(expr);
                    cur = consumed;
                },
                None => return (None, pos, verr),
            }
            if cur < toks.len() && matches!(toks[cur], Token::Comma) {
                cur = cur + 1;
            } else {
                break;
            }
        }
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        if !matches!(toks[cur], Token::CloseParen) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::CloseParen,
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        values.push(row);
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            cur = cur + 1;
        } else {
            break;
        }
    }

    (Some(ast::Statement::Insert { table, columns, values }), cur, None)
}

/// Parses a `DELETE FROM <table> [WHERE <expr>]` statement, having consumed
/// `DELETE`. The optional `WHERE` predicate is parsed by the Verus-verified
/// expression parser. Mirrors `parse_delete`; a malformed form yields
/// `(None, pos)` so the caller falls back to the legacy parser.
#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
fn parse_delete_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_delete(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    // FROM
    if pos >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], Token::Keyword(Keyword::From)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::From),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    // Table name (an identifier).
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    let table = match &toks[cur] {
        Token::Ident(name) => name.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    cur = cur + 1;

    // Position just past `FROM <ident>` — matches the spec twin's `r`.
    let ghost r_spec = input.drop_first().drop_first();
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
        assert(r_spec == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
    }

    // Optional WHERE <expr>, parsed by the verified expression parser.
    let mut where_clause: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        // Fuel the verified parser needs (`2*(len-pos)+3`); guard the arithmetic.
        let n = toks.len() - cur;
        if n > (usize::MAX - 3) / 2 {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        let fuel = 2 * n + 3;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, consumed, werr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
        match opt {
            Some(expr) => {
                where_clause = Some(expr);
                cur = consumed;
            },
            None => return (None, pos, werr),
        }
    } else {
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        } else {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        }
    }

    (Some(ast::Statement::Delete { table, where_clause }), cur, None)
}

/// Parses a `DROP TABLE [IF EXISTS] <name>` statement, having consumed `DROP`
/// (so `pos` points just past it). Mirrors `parse_drop_table`; a malformed form
/// yields `(None, pos)` so the caller falls back to the legacy parser.
#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
fn parse_drop_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_drop(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], Token::Keyword(Keyword::Table)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Table),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    // Optional IF EXISTS.
    let mut if_exists = false;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::If)) {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int); verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Exists)) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Exists),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if_exists = true;
    } else {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        }
    }

    // Table name (an identifier).
    if cur >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    match &toks[cur] {
        Token::Ident(name) => (
            Some(ast::Statement::DropTable { name: name.clone(), if_exists }),
            cur + 1,
            None,
        ),
        _ => (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    }
}

/// Parses a `BEGIN` statement's optional clauses, having consumed the `BEGIN`
/// keyword (so `pos` points just past it): an optional `TRANSACTION`, an optional
/// `READ ONLY` / `READ WRITE`, and an optional `AS OF SYSTEM TIME <number>`.
/// Mirrors `parse_begin`; a malformed clause yields `(None, begin_pos)` so the
/// caller falls back to the legacy parser for the specific error.
#[verifier::spinoff_prover]
#[verifier::rlimit(80000)]
fn parse_begin_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_begin(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    // `pos` is just past BEGIN; on any malformed clause we return this position so
    // the caller's cursor is unchanged and legacy re-parses from BEGIN.
    let begin_pos = pos;
    let mut cur = pos;

    // Optional TRANSACTION.
    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Transaction)) {
        cur = cur + 1;
    }
    // Ghost: `r0` = spec suffix just past the optional TRANSACTION.
    let ghost r0 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));

    // Optional READ ONLY / READ WRITE.
    let mut read_only = false;
    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Read)) {
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        match &toks[cur] {
            Token::Keyword(Keyword::Only) => {
                read_only = true;
                cur = cur + 1;
            },
            Token::Keyword(Keyword::Write) => {
                cur = cur + 1;
            },
            _ => return (None, begin_pos, Some(ParseError::UnexpectedToken(toks[cur].clone()))),
        }
    }
    // Ghost: `r2` = spec suffix just past the optional READ clause.
    let ghost r2 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));

    // Optional AS OF SYSTEM TIME <number>.
    let mut as_of: Option<u64> = None;
    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As)) {
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Of)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Of),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::System)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::System),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Time)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Time),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        match &toks[cur] {
            Token::Number(n) => match verified_integer::parse_u64(n.as_slice()) {
                Some(version) => {
                    as_of = Some(version);
                    cur = cur + 1;
                },
                None => return (None, begin_pos, Some(ParseError::InvalidSystemTime(n.clone()))),
            },
            _ => return (None, begin_pos, Some(ParseError::WantedNumber(toks[cur].clone()))),
        }
    }

    (Some(ast::Statement::Begin { read_only, as_of }), cur, None)
}

} // verus!
