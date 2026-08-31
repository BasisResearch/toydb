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

} // verus!
