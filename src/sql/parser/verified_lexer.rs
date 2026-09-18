//! Verified symbol scanner.
//!
//! `scan_symbol_bytes` is the production lexer's punctuation/operator scanner:
//! `lexer.rs` calls it for every symbol token it reads. It is proved to agree
//! with `lscan_sym`, the spec-level maximal-munch scan over `Seq<u8>`, by
//! `lemma_lscan_sym`; `lemma_lscan_op` carries the maximal-munch argument for
//! the three multi-byte leads (`<` `>` `!`).
//!
//! Scope: this module covers the symbol class only. Numbers are scanned by
//! `scan_number_bytes` in `lexer.rs`; identifiers, keywords, strings and quoted
//! identifiers are plain unverified Rust in `Lexer::scan`. So the parser's
//! functional guarantees remain stated at the *token* level, and the
//! string -> token stage sits outside them except for these two scanners.
//!
//! History: this module used to also carry a ~90-function token-level *model* of
//! the whole lexer -- a `TokenView`/`MTok` token model with whole-input
//! round-trip theorems (`lemma_lex_all_seq_roundtrip`,
//! `lemma_lex_mtok_seq_roundtrip`). That model was never wired to the production
//! `Lexer`: the executable twin it refined was deleted in phase 4, leaving it a
//! spec of nothing, and it was 90 of the 91 verified functions the coverage gate
//! counted as unreachable. It was deleted rather than marked
//! `#[verifier::reach_root]`, because marking it would have satisfied a gate
//! whose whole purpose is to find verified code nothing reaches by annotating
//! the code it exists to find. If the lexer cutover is ever taken up (issue 1 of
//! verus-parser-coverage-issues.md, option 2 -- wire `Lexer::scan` through a
//! model), the theorems are recoverable from git history; the scope caveat that
//! bounded their value stands on the record: `printable_tv` set `Ident => false`
//! and `String => false`, so the round trip proved nothing about identifiers or
//! string literals in the first place.

#![allow(dead_code)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

use vstd::prelude::*;

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

/// Canonical byte print of a symbol token (punctuation or operator).
pub open spec fn lex_print_sym(t: Token) -> Seq<u8> {
    if is_op(t) {
        lex_print_op(t)
    } else {
        lex_print1(t)
    }
}

/// Scan one symbol token: operators (maximal munch) on the `< > !` leads,
/// otherwise munch-free punctuation.
pub open spec fn lscan_sym(input: Seq<u8>, pos: int) -> (Option<Token>, int) {
    if 0 <= pos < input.len() {
        let b = input[pos];
        if b == 60 || b == 62 || b == 33 {
            lscan_op(input, pos)
        } else {
            match scan_punct1(b) {
                Some(t) => (Some(t), pos + 1),
                None => (None, pos),
            }
        }
    } else {
        (None, pos)
    }
}

/// Combined symbol roundtrip: scanning the print of any symbol token recovers it
/// and advances by its byte length, under the operator boundary (vacuous for
/// punctuation and the two-char operators).
#[cfg_attr(verus_reach, verifier::reach_root)]
pub proof fn lemma_lscan_sym(t: Token, tail: Seq<u8>)
    requires
        is_punct1(t) || is_op(t),
        op_tail_ok(t, tail),
    ensures
        lscan_sym(lex_print_sym(t) + tail, 0) == (Some(t), lex_print_sym(t).len() as int),
{
    let input = lex_print_sym(t) + tail;
    if is_op(t) {
        assert(lex_print_sym(t) == lex_print_op(t));
        // The operator lead byte is one of `< > !` (60/62/33).
        assert(input[0] == 60 || input[0] == 62 || input[0] == 33) by {
            match t {
                Token::LessThan => assert(input[0] == 60),
                Token::LessThanOrEqual => assert(input[0] == 60),
                Token::LessOrGreaterThan => assert(input[0] == 60),
                Token::GreaterThan => assert(input[0] == 62),
                Token::GreaterThanOrEqual => assert(input[0] == 62),
                Token::Exclamation => assert(input[0] == 33),
                Token::NotEqual => assert(input[0] == 33),
                _ => assert(false),
            }
        }
        lemma_lscan_op(t, tail);
    } else {
        assert(is_punct1(t));
        assert(lex_print_sym(t) == lex_print1(t));
        assert(input[0] == punct1_byte(t));
        // Punctuation bytes are never an operator lead (`< > !`).
        assert(input[0] != 60 && input[0] != 62 && input[0] != 33);
        assert(scan_punct1(punct1_byte(t)) == Some(t));
    }
}

pub fn scan_symbol_bytes(input: &[u8], pos: usize) -> (r: (Option<Token>, usize))
    requires
        pos <= input.len(),
    ensures
        r.0 == lscan_sym(input@, pos as int).0,
        r.1 == lscan_sym(input@, pos as int).1,
{
    if pos >= input.len() {
        return (None, pos);
    }
    let b = input[pos];
    let has1 = pos + 1 < input.len();
    if b == 60u8 {
        if has1 && input[pos + 1] == 61u8 {
            (Some(Token::LessThanOrEqual), pos + 2)
        } else if has1 && input[pos + 1] == 62u8 {
            (Some(Token::LessOrGreaterThan), pos + 2)
        } else {
            (Some(Token::LessThan), pos + 1)
        }
    } else if b == 62u8 {
        if has1 && input[pos + 1] == 61u8 {
            (Some(Token::GreaterThanOrEqual), pos + 2)
        } else {
            (Some(Token::GreaterThan), pos + 1)
        }
    } else if b == 33u8 {
        if has1 && input[pos + 1] == 61u8 {
            (Some(Token::NotEqual), pos + 2)
        } else {
            (Some(Token::Exclamation), pos + 1)
        }
    } else {
        let t: Option<Token> =
            if b == 46u8 { Some(Token::Period) }
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
    }
}

} // verus!
