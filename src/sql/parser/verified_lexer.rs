//! Verified production lexer — first brick (L0).
//!
//! The grammar layer (`verified_stmt` etc.) operates on a clean `Token` stream.
//! This module begins the from-scratch production lexer that will eventually
//! produce that stream from raw bytes, scanning `Seq<u8>` with an explicit
//! cursor and producing the *real* production `Token` (not the Phase-0 toy in
//! `verified.rs`). L0 covers the munch-free single-character punctuation — the
//! tokens that are never a prefix of a two-character token (so no maximal-munch
//! reasoning is needed yet). `<`, `>`, `!` and the two-char operators (`<=`,
//! `>=`, `<>`, `!=`) are deferred to L1 (maximal munch); numbers, strings,
//! identifiers and keywords to later bricks.

#![allow(dead_code)]

use vstd::prelude::*;

#[allow(unused_imports)]
use super::Token;

verus! {

/// The munch-free single-character punctuation tokens: each is exactly one ASCII
/// byte and is never the first byte of a longer token, so scanning is a single
/// unambiguous byte read.
pub open spec fn is_punct1(t: Token) -> bool {
    match t {
        Token::Period
        | Token::Equal
        | Token::Plus
        | Token::Minus
        | Token::Asterisk
        | Token::Slash
        | Token::Caret
        | Token::Percent
        | Token::Question
        | Token::Comma
        | Token::Semicolon
        | Token::OpenParen
        | Token::CloseParen => true,
        _ => false,
    }
}

/// The ASCII byte a munch-free punctuation token prints as.
pub open spec fn punct1_byte(t: Token) -> u8 {
    match t {
        Token::Period => 46,       // .
        Token::Equal => 61,        // =
        Token::Plus => 43,         // +
        Token::Minus => 45,        // -
        Token::Asterisk => 42,     // *
        Token::Slash => 47,        // /
        Token::Caret => 94,        // ^
        Token::Percent => 37,      // %
        Token::Question => 63,     // ?
        Token::Comma => 44,        // ,
        Token::Semicolon => 59,    // ;
        Token::OpenParen => 40,    // (
        Token::CloseParen => 41,   // )
        _ => 0,
    }
}

/// Byte -> token for the munch-free set. `None` for any other byte (including
/// `<`, `>`, `!`, which begin two-character tokens handled in L1).
pub open spec fn scan_punct1(b: u8) -> Option<Token> {
    if b == 46 { Some(Token::Period) }
    else if b == 61 { Some(Token::Equal) }
    else if b == 43 { Some(Token::Plus) }
    else if b == 45 { Some(Token::Minus) }
    else if b == 42 { Some(Token::Asterisk) }
    else if b == 47 { Some(Token::Slash) }
    else if b == 94 { Some(Token::Caret) }
    else if b == 37 { Some(Token::Percent) }
    else if b == 63 { Some(Token::Question) }
    else if b == 44 { Some(Token::Comma) }
    else if b == 59 { Some(Token::Semicolon) }
    else if b == 40 { Some(Token::OpenParen) }
    else if b == 41 { Some(Token::CloseParen) }
    else { None }
}

/// Canonical byte print of a single munch-free punctuation token.
pub open spec fn lex_print1(t: Token) -> Seq<u8> {
    seq![punct1_byte(t)]
}

/// The L0 byte-cursor scanner: at `pos`, read one munch-free punctuation byte.
/// Returns the token and the advanced cursor, or `None` at end / on any byte
/// outside the munch-free set.
pub open spec fn lscan1(input: Seq<u8>, pos: int) -> (Option<Token>, int) {
    if 0 <= pos < input.len() {
        match scan_punct1(input[pos]) {
            Some(t) => (Some(t), pos + 1),
            None => (None, pos),
        }
    } else {
        (None, pos)
    }
}

/// The scanner inverts the printer for every munch-free punctuation token: the
/// byte it prints scans straight back to it, regardless of the trailing bytes
/// (these tokens are never a prefix of a longer token, so no lookahead matters).
pub proof fn lemma_lscan1_lex_print1(t: Token, tail: Seq<u8>)
    requires
        is_punct1(t),
    ensures
        lscan1(lex_print1(t) + tail, 0) == (Some(t), 1int),
{
    let input = lex_print1(t) + tail;
    assert(input.len() >= 1);
    assert(input[0] == punct1_byte(t));
    assert(scan_punct1(punct1_byte(t)) == Some(t));
}

/// Executable L0 scanner, refining `lscan1` at the byte level. `input[pos]` is a
/// real byte from the source; the returned token matches the spec exactly.
pub fn scan_punct1_exec(input: &Vec<u8>, pos: usize) -> (r: (Option<Token>, usize))
    requires
        pos <= input.len(),
    ensures
        r.0 == lscan1(input@, pos as int).0,
        r.1 == lscan1(input@, pos as int).1,
{
    if pos < input.len() {
        let b = input[pos];
        let t: Option<Token> = if b == 46u8 { Some(Token::Period) }
            else if b == 61u8 { Some(Token::Equal) }
            else if b == 43u8 { Some(Token::Plus) }
            else if b == 45u8 { Some(Token::Minus) }
            else if b == 42u8 { Some(Token::Asterisk) }
            else if b == 47u8 { Some(Token::Slash) }
            else if b == 94u8 { Some(Token::Caret) }
            else if b == 37u8 { Some(Token::Percent) }
            else if b == 63u8 { Some(Token::Question) }
            else if b == 44u8 { Some(Token::Comma) }
            else if b == 59u8 { Some(Token::Semicolon) }
            else if b == 40u8 { Some(Token::OpenParen) }
            else if b == 41u8 { Some(Token::CloseParen) }
            else { None };
        match t {
            Some(tok) => (Some(tok), pos + 1),
            None => (None, pos),
        }
    } else {
        (None, pos)
    }
}

// -- L1: maximal-munch operators (`<` `>` `!` and `<=` `>=` `<>` `!=`) ---------
//
// These are the first tokens where a byte can begin more than one token, so the
// scanner must look one byte ahead and commit to the longest match. The two-char
// forms roundtrip for any tail (nothing extends them). The single-char forms
// (`<`, `>`, `!`) need a byte-level boundary condition on the tail: a printed `<`
// followed by `=` or `>` would re-scan as `<=`/`<>`, so the roundtrip holds only
// when the next byte is not one that extends the operator — the same boundary
// reasoning the grammar used at the token level, here at the byte level.

/// The maximal-munch operator tokens.
pub open spec fn is_op(t: Token) -> bool {
    match t {
        Token::LessThan
        | Token::LessThanOrEqual
        | Token::LessOrGreaterThan
        | Token::GreaterThan
        | Token::GreaterThanOrEqual
        | Token::Exclamation
        | Token::NotEqual => true,
        _ => false,
    }
}

/// Canonical byte print of an operator token (1 or 2 ASCII bytes).
pub open spec fn lex_print_op(t: Token) -> Seq<u8> {
    match t {
        Token::LessThan => seq![60u8],                    // <
        Token::LessThanOrEqual => seq![60u8, 61u8],       // <=
        Token::LessOrGreaterThan => seq![60u8, 62u8],     // <>
        Token::GreaterThan => seq![62u8],                 // >
        Token::GreaterThanOrEqual => seq![62u8, 61u8],    // >=
        Token::Exclamation => seq![33u8],                 // !
        Token::NotEqual => seq![33u8, 61u8],              // !=
        _ => Seq::empty(),
    }
}

/// Maximal-munch scanner for the operator lead bytes `<` `>` `!`: look one byte
/// ahead and commit to the longest operator.
pub open spec fn lscan_op(input: Seq<u8>, pos: int) -> (Option<Token>, int) {
    if 0 <= pos < input.len() {
        let b0 = input[pos];
        let has1 = pos + 1 < input.len();
        if b0 == 60 {  // <
            if has1 && input[pos + 1] == 61 { (Some(Token::LessThanOrEqual), pos + 2) }
            else if has1 && input[pos + 1] == 62 { (Some(Token::LessOrGreaterThan), pos + 2) }
            else { (Some(Token::LessThan), pos + 1) }
        } else if b0 == 62 {  // >
            if has1 && input[pos + 1] == 61 { (Some(Token::GreaterThanOrEqual), pos + 2) }
            else { (Some(Token::GreaterThan), pos + 1) }
        } else if b0 == 33 {  // !
            if has1 && input[pos + 1] == 61 { (Some(Token::NotEqual), pos + 2) }
            else { (Some(Token::Exclamation), pos + 1) }
        } else {
            (None, pos)
        }
    } else {
        (None, pos)
    }
}

/// Byte-level boundary condition for a single-char operator's tail: the next byte
/// must not extend it into a two-char operator. Two-char operators impose nothing
/// (nothing extends them), so this is vacuously true for them.
pub open spec fn op_tail_ok(t: Token, tail: Seq<u8>) -> bool {
    match t {
        Token::LessThan => tail.len() == 0 || (tail[0] != 61 && tail[0] != 62),
        Token::GreaterThan => tail.len() == 0 || tail[0] != 61,
        Token::Exclamation => tail.len() == 0 || tail[0] != 61,
        _ => true,
    }
}

/// Maximal-munch roundtrip: scanning the print of any operator recovers it and
/// advances by its byte length, given the tail respects the operator's boundary
/// (always satisfied for the two-char forms).
pub proof fn lemma_lscan_op(t: Token, tail: Seq<u8>)
    requires
        is_op(t),
        op_tail_ok(t, tail),
    ensures
        lscan_op(lex_print_op(t) + tail, 0) == (Some(t), lex_print_op(t).len() as int),
{
    let input = lex_print_op(t) + tail;
    match t {
        Token::LessThanOrEqual => {
            assert(input[0] == 60 && input[1] == 61);
        },
        Token::LessOrGreaterThan => {
            assert(input[0] == 60 && input[1] == 62);
        },
        Token::GreaterThanOrEqual => {
            assert(input[0] == 62 && input[1] == 61);
        },
        Token::NotEqual => {
            assert(input[0] == 33 && input[1] == 61);
        },
        Token::LessThan => {
            assert(input[0] == 60);
            assert(input.len() > 1 ==> (input[1] != 61 && input[1] != 62)) by {
                if input.len() > 1 { assert(input[1] == tail[0]); }
            }
        },
        Token::GreaterThan => {
            assert(input[0] == 62);
            assert(input.len() > 1 ==> input[1] != 61) by {
                if input.len() > 1 { assert(input[1] == tail[0]); }
            }
        },
        Token::Exclamation => {
            assert(input[0] == 33);
            assert(input.len() > 1 ==> input[1] != 61) by {
                if input.len() > 1 { assert(input[1] == tail[0]); }
            }
        },
        _ => { assert(false); },
    }
}

/// Executable maximal-munch operator scanner, refining `lscan_op` on real bytes.
pub fn scan_op_exec(input: &Vec<u8>, pos: usize) -> (r: (Option<Token>, usize))
    requires
        pos <= input.len(),
    ensures
        r.0 == lscan_op(input@, pos as int).0,
        r.1 == lscan_op(input@, pos as int).1,
{
    if pos < input.len() {
        let b0 = input[pos];
        let has1 = pos + 1 < input.len();
        if b0 == 60u8 {
            if has1 && input[pos + 1] == 61u8 { (Some(Token::LessThanOrEqual), pos + 2) }
            else if has1 && input[pos + 1] == 62u8 { (Some(Token::LessOrGreaterThan), pos + 2) }
            else { (Some(Token::LessThan), pos + 1) }
        } else if b0 == 62u8 {
            if has1 && input[pos + 1] == 61u8 { (Some(Token::GreaterThanOrEqual), pos + 2) }
            else { (Some(Token::GreaterThan), pos + 1) }
        } else if b0 == 33u8 {
            if has1 && input[pos + 1] == 61u8 { (Some(Token::NotEqual), pos + 2) }
            else { (Some(Token::Exclamation), pos + 1) }
        } else {
            (None, pos)
        }
    } else {
        (None, pos)
    }
}

} // verus!
