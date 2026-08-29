//! Verified concrete parser for the simple keyword-driven statements the cutover
//! has reached so far — `BEGIN` / `COMMIT` / `ROLLBACK` (control) and
//! `DROP TABLE` (DDL). These are the statement-structure cutover's first bricks
//! (see `verus-parser-roundtrip-plan.md`). Each is a 1:1 port of the
//! corresponding `parser.rs` routine, producing the production `ast::Statement`
//! over `super::Token` and returning the position past the consumed tokens (so
//! the statement parser can check for a trailing semicolon / end of input,
//! exactly like the legacy path).
//!
//! Verus proves no panic, no arithmetic overflow, and termination (no recursion
//! or loops; every `Vec` index is bounds-guarded, every `cur + 1` is bounded by
//! the token count). There is no functional specification: behavioural
//! equivalence to the trusted legacy parser is established by the differential
//! harness (`sql::parser::differential`), not by proof — the same contract as
//! `verified_precedence`.

// Proof/verification scaffolding, not idiomatic library code.
#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, Token, ast, verified_integer};

verus! {

/// Parses a control statement (`BEGIN` / `COMMIT` / `ROLLBACK`) at `pos`,
/// returning it and the position past its tokens, or `(None, pos)` if the token
/// at `pos` does not begin a control statement (or the `BEGIN` clauses are
/// malformed). Mirrors the `Begin`/`Commit`/`Rollback` arms of `parse_statement`.
pub fn parse_control_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
{
    if pos >= toks.len() {
        return (None, pos);
    }
    match &toks[pos] {
        Token::Keyword(Keyword::Commit) => (Some(ast::Statement::Commit), pos + 1),
        Token::Keyword(Keyword::Rollback) => (Some(ast::Statement::Rollback), pos + 1),
        Token::Keyword(Keyword::Begin) => parse_begin_at(toks, pos + 1),
        Token::Keyword(Keyword::Drop) => parse_drop_at(toks, pos + 1),
        _ => (None, pos),
    }
}

/// Parses a `DROP TABLE [IF EXISTS] <name>` statement, having consumed `DROP`
/// (so `pos` points just past it). Mirrors `parse_drop_table`; a malformed form
/// yields `(None, pos)` so the caller falls back to the legacy parser.
fn parse_drop_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
{
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::Table)) {
        return (None, pos);
    }
    let mut cur = pos + 1;

    // Optional IF EXISTS.
    let mut if_exists = false;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::If)) {
        cur = cur + 1;
        if cur >= toks.len() || !matches!(toks[cur], Token::Keyword(Keyword::Exists)) {
            return (None, pos);
        }
        cur = cur + 1;
        if_exists = true;
    }

    // Table name (an identifier).
    if cur >= toks.len() {
        return (None, pos);
    }
    match &toks[cur] {
        Token::Ident(name) => (
            Some(ast::Statement::DropTable { name: name.clone(), if_exists }),
            cur + 1,
        ),
        _ => (None, pos),
    }
}

/// Parses a `BEGIN` statement's optional clauses, having consumed the `BEGIN`
/// keyword (so `pos` points just past it): an optional `TRANSACTION`, an optional
/// `READ ONLY` / `READ WRITE`, and an optional `AS OF SYSTEM TIME <number>`.
/// Mirrors `parse_begin`; a malformed clause yields `(None, begin_pos)` so the
/// caller falls back to the legacy parser for the specific error.
fn parse_begin_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
{
    // `pos` is just past BEGIN; on any malformed clause we return this position so
    // the caller's cursor is unchanged and legacy re-parses from BEGIN.
    let begin_pos = pos;
    let mut cur = pos;

    // Optional TRANSACTION.
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Transaction)) {
        cur = cur + 1;
    }

    // Optional READ ONLY / READ WRITE.
    let mut read_only = false;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Read)) {
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos);
        }
        match &toks[cur] {
            Token::Keyword(Keyword::Only) => {
                read_only = true;
                cur = cur + 1;
            },
            Token::Keyword(Keyword::Write) => {
                cur = cur + 1;
            },
            _ => return (None, begin_pos),
        }
    }

    // Optional AS OF SYSTEM TIME <number>.
    let mut as_of: Option<u64> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As)) {
        cur = cur + 1;
        if cur >= toks.len() || !matches!(toks[cur], Token::Keyword(Keyword::Of)) {
            return (None, begin_pos);
        }
        cur = cur + 1;
        if cur >= toks.len() || !matches!(toks[cur], Token::Keyword(Keyword::System)) {
            return (None, begin_pos);
        }
        cur = cur + 1;
        if cur >= toks.len() || !matches!(toks[cur], Token::Keyword(Keyword::Time)) {
            return (None, begin_pos);
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos);
        }
        match &toks[cur] {
            Token::Number(n) => match verified_integer::parse_u64(n.as_slice()) {
                Some(version) => {
                    as_of = Some(version);
                    cur = cur + 1;
                },
                None => return (None, begin_pos),
            },
            _ => return (None, begin_pos),
        }
    }

    (Some(ast::Statement::Begin { read_only, as_of }), cur)
}

} // verus!
