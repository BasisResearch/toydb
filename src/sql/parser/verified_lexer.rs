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

} // verus!
