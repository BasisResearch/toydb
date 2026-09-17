//! Token-level lexer model.
//!
//! A ghost/spec model of tokenization. Every theorem here is stated at the token
//! level, over `Seq<u8>` input and a `TokenView`/`MTok` token model.
//!
//! The headline theorems are the whole-input round trips: printing a token list
//! with single-space separators and re-lexing recovers the list exactly --
//! `lemma_lex_all_seq_roundtrip` for the byte-determined classes (numbers,
//! keywords, all symbols) and `lemma_lex_mtok_seq_roundtrip` for the unified
//! model that adds identifiers, strings and quoted identifiers. Both are
//! axiom-free. A space is a universal separator: it satisfies every token's
//! boundary condition (`num_tail_ok`, the keyword non-continuation boundary,
//! `op_tail_ok`), so no per-adjacency canonicalisation is needed.
//!
//! LIMIT, stated plainly: this model is NOT wired to the production `Lexer`. The
//! only lexer code that actually runs verified is `scan_symbol_bytes` (here,
//! under `lemma_lscan_sym`) and `scan_number_bytes` (in `lexer.rs`); the rest of
//! the production `Lexer`'s string -> token stage is plain Rust. So the parser's
//! functional guarantees are stated at the *token* level and the string -> token
//! stage sits outside them. The round-trip theorems above are kept as *stated
//! theorems* for the lexer-cutover milestone, which would otherwise have to
//! restate them (see commit 455d790, which kept this layer for that reason).
//!
//! The executable twin these once refined was deleted in phase 4, and the
//! position-local lemmas that served only it (`lemma_*_local`, `*_bounds`,
//! `lex_from`, `lex_all_ends`, `lex_token_end`) went with the parser-coverage
//! cleanup; the seq-based layer the theorems above rest on is what remains.

#![allow(dead_code)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

use vstd::prelude::*;

#[allow(unused_imports)]
use super::Keyword;
#[allow(unused_imports)]
use super::Token;
#[allow(unused_imports)]
use super::verified_production::TokenView;
// `token_view`/`token_views` are `spec fn` and `token_views_concat` is a `proof fn`;
// under a plain (non-Verus) `cargo build` these ghost items are stripped, so the
// import only resolves when Verus keeps ghost code.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_production::{token_view, token_views, token_views_concat};

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

/// ASCII whitespace: space, tab, newline, carriage return.
pub open spec fn is_ws(b: u8) -> bool {
    b == 32 || b == 9 || b == 10 || b == 13
}

/// Advance past a maximal run of whitespace bytes starting at `pos`.
pub open spec fn skip_ws(input: Seq<u8>, pos: int) -> int
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_ws(input[pos]) {
        skip_ws(input, pos + 1)
    } else {
        pos
    }
}

/// `skip_ws` never moves backward and never past the end.
pub proof fn lemma_skip_ws_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        pos <= skip_ws(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_ws(input[pos]) {
        lemma_skip_ws_bounds(input, pos + 1);
    }
}

/// When the current byte is not whitespace, `skip_ws` is a no-op — so printing a
/// token whose first byte is non-whitespace (all L0/L1 tokens) means a preceding
/// `skip_ws` leaves the cursor exactly on it.
pub proof fn lemma_skip_ws_nonws(input: Seq<u8>, pos: int)
    requires
        0 <= pos < input.len(),
        !is_ws(input[pos]),
    ensures
        skip_ws(input, pos) == pos,
{
}

/// ASCII digit `0`-`9`.
pub open spec fn is_digit(b: u8) -> bool {
    48 <= b <= 57
}

/// End of the maximal digit run starting at `pos`.
pub open spec fn scan_digits_end(input: Seq<u8>, pos: int) -> int
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_digit(input[pos]) {
        scan_digits_end(input, pos + 1)
    } else {
        pos
    }
}

/// Maximal-run characterization: if `[pos, k)` are all digits and position `k` is
/// end-of-input or a non-digit, the scan stops exactly at `k`.
pub proof fn lemma_scan_digits_end_run(input: Seq<u8>, pos: int, k: int)
    requires
        0 <= pos <= k <= input.len(),
        forall|i: int| pos <= i < k ==> is_digit(#[trigger] input[i]),
        k == input.len() || !is_digit(input[k]),
    ensures
        scan_digits_end(input, pos) == k,
    decreases k - pos,
{
    if pos < k {
        assert(is_digit(input[pos]));
        lemma_scan_digits_end_run(input, pos + 1, k);
    }
}

/// Identifier start byte: `A`-`Z`, `a`-`z`, or `_`.
pub open spec fn is_ident_start(b: u8) -> bool {
    (65 <= b <= 90) || (97 <= b <= 122) || b == 95
}

/// Identifier continuation byte: a start byte or a digit.
pub open spec fn is_ident_cont(b: u8) -> bool {
    is_ident_start(b) || is_digit(b)
}

/// Every byte after the first is an identifier-continuation byte, and the first
/// is an identifier-start byte (the shape of a well-formed unquoted identifier).
pub open spec fn is_ident_bytes(s: Seq<u8>) -> bool {
    s.len() >= 1 && is_ident_start(s[0])
        && (forall|i: int| 0 <= i < s.len() ==> is_ident_cont(#[trigger] s[i]))
}

/// End of the maximal identifier-continuation run starting at `pos`.
pub open spec fn scan_ident_end(input: Seq<u8>, pos: int) -> int
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_ident_cont(input[pos]) {
        scan_ident_end(input, pos + 1)
    } else {
        pos
    }
}

/// Maximal-run characterization for identifiers (mirrors `lemma_scan_digits_end_run`).
pub proof fn lemma_scan_ident_end_run(input: Seq<u8>, pos: int, k: int)
    requires
        0 <= pos <= k <= input.len(),
        forall|i: int| pos <= i < k ==> is_ident_cont(#[trigger] input[i]),
        k == input.len() || !is_ident_cont(input[k]),
    ensures
        scan_ident_end(input, pos) == k,
    decreases k - pos,
{
    if pos < k {
        assert(is_ident_cont(input[pos]));
        lemma_scan_ident_end_run(input, pos + 1, k);
    }
}

/// Identifier roundtrip: a well-formed identifier byte run followed by a
/// non-continuation boundary byte (or end) re-scans to exactly itself.
pub proof fn lemma_scan_ident_roundtrip(d: Seq<u8>, tail: Seq<u8>)
    requires
        is_ident_bytes(d),
        tail.len() == 0 || !is_ident_cont(tail[0]),
    ensures
        scan_ident_end(d + tail, 0) == d.len(),
{
    let input = d + tail;
    assert forall|i: int| 0 <= i < d.len() implies is_ident_cont(#[trigger] input[i]) by {
        assert(input[i] == d[i]);
    }
    if tail.len() == 0 {
        assert(input.len() == d.len());
    } else {
        assert(input[d.len() as int] == tail[0]);
    }
    lemma_scan_ident_end_run(input, 0, d.len() as int);
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
#[verifier::reach_root]
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

/// End of a `digits[.digits]` number scan starting at a digit position: consume
/// the integer run, then (if a `.` follows) the fraction run.
pub open spec fn scan_num_dec_end(input: Seq<u8>, pos: int) -> int {
    let d1 = scan_digits_end(input, pos);
    if 0 <= d1 < input.len() && input[d1] == 46 {
        scan_digits_end(input, d1 + 1)
    } else {
        d1
    }
}

/// Exponent marker byte: `e` or `E`.
pub open spec fn is_exp(b: u8) -> bool {
    b == 101 || b == 69
}

/// Exponent sign byte: `+` or `-`.
pub open spec fn is_num_sign(b: u8) -> bool {
    b == 43 || b == 45
}

/// End of a full number scan starting at a digit: integer run, optional `.`
/// fraction, optional `(e|E)[+|-]digits` exponent. Mirrors `scan_number_bytes`.
pub open spec fn scan_num_full_end(input: Seq<u8>, pos: int) -> int {
    let p = scan_num_dec_end(input, pos);
    if 0 <= p < input.len() && is_exp(input[p]) {
        let q0 = p + 1;
        let q = if 0 <= q0 < input.len() && is_num_sign(input[q0]) { q0 + 1 } else { q0 };
        scan_digits_end(input, q)
    } else {
        p
    }
}

/// A tail that does not extend a printed number: not a digit (would join the
/// run), not `.` (would start a fraction), not `e`/`E` (would start an exponent).
/// This is the maximal-munch boundary for numbers, the analogue of `op_tail_ok`.
pub open spec fn num_tail_ok(tail: Seq<u8>) -> bool {
    tail.len() == 0 || (!is_digit(tail[0]) && tail[0] != 46 && !is_exp(tail[0]))
}

/// Scan a full number, producing the `Number` token value carrying the raw bytes.
pub open spec fn lscan_num_full(input: Seq<u8>, pos: int) -> (Option<TokenView>, int) {
    if 0 <= pos < input.len() && is_digit(input[pos]) {
        let e = scan_num_full_end(input, pos);
        (Some(TokenView::Number(input.subrange(pos, e))), e)
    } else {
        (None, pos)
    }
}

/// Canonical lowercase keyword bytes — the classification key (what the
/// production lexer matches after lowercasing an identifier run).
pub open spec fn kw_text(k: Keyword) -> Seq<u8> {
    match k {
        Keyword::As => seq![97u8, 115u8],
        Keyword::Asc => seq![97u8, 115u8, 99u8],
        Keyword::And => seq![97u8, 110u8, 100u8],
        Keyword::Begin => seq![98u8, 101u8, 103u8, 105u8, 110u8],
        Keyword::Bool => seq![98u8, 111u8, 111u8, 108u8],
        Keyword::Boolean => seq![98u8, 111u8, 111u8, 108u8, 101u8, 97u8, 110u8],
        Keyword::By => seq![98u8, 121u8],
        Keyword::Commit => seq![99u8, 111u8, 109u8, 109u8, 105u8, 116u8],
        Keyword::Create => seq![99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Keyword::Cross => seq![99u8, 114u8, 111u8, 115u8, 115u8],
        Keyword::Default => seq![100u8, 101u8, 102u8, 97u8, 117u8, 108u8, 116u8],
        Keyword::Delete => seq![100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        Keyword::Desc => seq![100u8, 101u8, 115u8, 99u8],
        Keyword::Double => seq![100u8, 111u8, 117u8, 98u8, 108u8, 101u8],
        Keyword::Drop => seq![100u8, 114u8, 111u8, 112u8],
        Keyword::Exists => seq![101u8, 120u8, 105u8, 115u8, 116u8, 115u8],
        Keyword::Explain => seq![101u8, 120u8, 112u8, 108u8, 97u8, 105u8, 110u8],
        Keyword::False => seq![102u8, 97u8, 108u8, 115u8, 101u8],
        Keyword::Float => seq![102u8, 108u8, 111u8, 97u8, 116u8],
        Keyword::From => seq![102u8, 114u8, 111u8, 109u8],
        Keyword::Group => seq![103u8, 114u8, 111u8, 117u8, 112u8],
        Keyword::Having => seq![104u8, 97u8, 118u8, 105u8, 110u8, 103u8],
        Keyword::If => seq![105u8, 102u8],
        Keyword::Index => seq![105u8, 110u8, 100u8, 101u8, 120u8],
        Keyword::Infinity => seq![105u8, 110u8, 102u8, 105u8, 110u8, 105u8, 116u8, 121u8],
        Keyword::Inner => seq![105u8, 110u8, 110u8, 101u8, 114u8],
        Keyword::Insert => seq![105u8, 110u8, 115u8, 101u8, 114u8, 116u8],
        Keyword::Int => seq![105u8, 110u8, 116u8],
        Keyword::Integer => seq![105u8, 110u8, 116u8, 101u8, 103u8, 101u8, 114u8],
        Keyword::Into => seq![105u8, 110u8, 116u8, 111u8],
        Keyword::Is => seq![105u8, 115u8],
        Keyword::Join => seq![106u8, 111u8, 105u8, 110u8],
        Keyword::Key => seq![107u8, 101u8, 121u8],
        Keyword::Left => seq![108u8, 101u8, 102u8, 116u8],
        Keyword::Like => seq![108u8, 105u8, 107u8, 101u8],
        Keyword::Limit => seq![108u8, 105u8, 109u8, 105u8, 116u8],
        Keyword::NaN => seq![110u8, 97u8, 110u8],
        Keyword::Not => seq![110u8, 111u8, 116u8],
        Keyword::Null => seq![110u8, 117u8, 108u8, 108u8],
        Keyword::Of => seq![111u8, 102u8],
        Keyword::Offset => seq![111u8, 102u8, 102u8, 115u8, 101u8, 116u8],
        Keyword::On => seq![111u8, 110u8],
        Keyword::Only => seq![111u8, 110u8, 108u8, 121u8],
        Keyword::Or => seq![111u8, 114u8],
        Keyword::Order => seq![111u8, 114u8, 100u8, 101u8, 114u8],
        Keyword::Outer => seq![111u8, 117u8, 116u8, 101u8, 114u8],
        Keyword::Primary => seq![112u8, 114u8, 105u8, 109u8, 97u8, 114u8, 121u8],
        Keyword::Read => seq![114u8, 101u8, 97u8, 100u8],
        Keyword::References => seq![114u8, 101u8, 102u8, 101u8, 114u8, 101u8, 110u8, 99u8, 101u8, 115u8],
        Keyword::Right => seq![114u8, 105u8, 103u8, 104u8, 116u8],
        Keyword::Rollback => seq![114u8, 111u8, 108u8, 108u8, 98u8, 97u8, 99u8, 107u8],
        Keyword::Select => seq![115u8, 101u8, 108u8, 101u8, 99u8, 116u8],
        Keyword::Set => seq![115u8, 101u8, 116u8],
        Keyword::String => seq![115u8, 116u8, 114u8, 105u8, 110u8, 103u8],
        Keyword::System => seq![115u8, 121u8, 115u8, 116u8, 101u8, 109u8],
        Keyword::Table => seq![116u8, 97u8, 98u8, 108u8, 101u8],
        Keyword::Text => seq![116u8, 101u8, 120u8, 116u8],
        Keyword::Time => seq![116u8, 105u8, 109u8, 101u8],
        Keyword::Transaction => seq![116u8, 114u8, 97u8, 110u8, 115u8, 97u8, 99u8, 116u8, 105u8, 111u8, 110u8],
        Keyword::True => seq![116u8, 114u8, 117u8, 101u8],
        Keyword::Unique => seq![117u8, 110u8, 105u8, 113u8, 117u8, 101u8],
        Keyword::Update => seq![117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Keyword::Values => seq![118u8, 97u8, 108u8, 117u8, 101u8, 115u8],
        Keyword::Varchar => seq![118u8, 97u8, 114u8, 99u8, 104u8, 97u8, 114u8],
        Keyword::Where => seq![119u8, 104u8, 101u8, 114u8, 101u8],
        Keyword::Write => seq![119u8, 114u8, 105u8, 116u8, 101u8],
    }
}

/// Byte at index, or an out-of-range sentinel (256) past the end. Lets the
/// classifier decide on integer comparisons (length + indexed bytes) rather
/// than whole-`Seq` equality, which Verus does not resolve automatically.
pub open spec fn byte_at(s: Seq<u8>, i: int) -> int {
    if 0 <= i < s.len() { s[i] as int } else { 256 }
}

/// Classify a (lowercase) identifier byte-run as a keyword, or `None` for a
/// plain identifier. Mirrors `Keyword::try_from(&str)` exactly.
pub open spec fn classify_kw(s: Seq<u8>) -> Option<Keyword> {
    if s.len() == 2 && byte_at(s, 0) == 97 && byte_at(s, 1) == 115 { Some(Keyword::As) }
    else if s.len() == 3 && byte_at(s, 0) == 97 && byte_at(s, 1) == 115 && byte_at(s, 2) == 99 { Some(Keyword::Asc) }
    else if s.len() == 3 && byte_at(s, 0) == 97 && byte_at(s, 1) == 110 && byte_at(s, 2) == 100 { Some(Keyword::And) }
    else if s.len() == 5 && byte_at(s, 0) == 98 && byte_at(s, 1) == 101 && byte_at(s, 2) == 103 && byte_at(s, 3) == 105 && byte_at(s, 4) == 110 { Some(Keyword::Begin) }
    else if s.len() == 4 && byte_at(s, 0) == 98 && byte_at(s, 1) == 111 && byte_at(s, 2) == 111 && byte_at(s, 3) == 108 { Some(Keyword::Bool) }
    else if s.len() == 7 && byte_at(s, 0) == 98 && byte_at(s, 1) == 111 && byte_at(s, 2) == 111 && byte_at(s, 3) == 108 && byte_at(s, 4) == 101 && byte_at(s, 5) == 97 && byte_at(s, 6) == 110 { Some(Keyword::Boolean) }
    else if s.len() == 2 && byte_at(s, 0) == 98 && byte_at(s, 1) == 121 { Some(Keyword::By) }
    else if s.len() == 6 && byte_at(s, 0) == 99 && byte_at(s, 1) == 111 && byte_at(s, 2) == 109 && byte_at(s, 3) == 109 && byte_at(s, 4) == 105 && byte_at(s, 5) == 116 { Some(Keyword::Commit) }
    else if s.len() == 6 && byte_at(s, 0) == 99 && byte_at(s, 1) == 114 && byte_at(s, 2) == 101 && byte_at(s, 3) == 97 && byte_at(s, 4) == 116 && byte_at(s, 5) == 101 { Some(Keyword::Create) }
    else if s.len() == 5 && byte_at(s, 0) == 99 && byte_at(s, 1) == 114 && byte_at(s, 2) == 111 && byte_at(s, 3) == 115 && byte_at(s, 4) == 115 { Some(Keyword::Cross) }
    else if s.len() == 7 && byte_at(s, 0) == 100 && byte_at(s, 1) == 101 && byte_at(s, 2) == 102 && byte_at(s, 3) == 97 && byte_at(s, 4) == 117 && byte_at(s, 5) == 108 && byte_at(s, 6) == 116 { Some(Keyword::Default) }
    else if s.len() == 6 && byte_at(s, 0) == 100 && byte_at(s, 1) == 101 && byte_at(s, 2) == 108 && byte_at(s, 3) == 101 && byte_at(s, 4) == 116 && byte_at(s, 5) == 101 { Some(Keyword::Delete) }
    else if s.len() == 4 && byte_at(s, 0) == 100 && byte_at(s, 1) == 101 && byte_at(s, 2) == 115 && byte_at(s, 3) == 99 { Some(Keyword::Desc) }
    else if s.len() == 6 && byte_at(s, 0) == 100 && byte_at(s, 1) == 111 && byte_at(s, 2) == 117 && byte_at(s, 3) == 98 && byte_at(s, 4) == 108 && byte_at(s, 5) == 101 { Some(Keyword::Double) }
    else if s.len() == 4 && byte_at(s, 0) == 100 && byte_at(s, 1) == 114 && byte_at(s, 2) == 111 && byte_at(s, 3) == 112 { Some(Keyword::Drop) }
    else if s.len() == 6 && byte_at(s, 0) == 101 && byte_at(s, 1) == 120 && byte_at(s, 2) == 105 && byte_at(s, 3) == 115 && byte_at(s, 4) == 116 && byte_at(s, 5) == 115 { Some(Keyword::Exists) }
    else if s.len() == 7 && byte_at(s, 0) == 101 && byte_at(s, 1) == 120 && byte_at(s, 2) == 112 && byte_at(s, 3) == 108 && byte_at(s, 4) == 97 && byte_at(s, 5) == 105 && byte_at(s, 6) == 110 { Some(Keyword::Explain) }
    else if s.len() == 5 && byte_at(s, 0) == 102 && byte_at(s, 1) == 97 && byte_at(s, 2) == 108 && byte_at(s, 3) == 115 && byte_at(s, 4) == 101 { Some(Keyword::False) }
    else if s.len() == 5 && byte_at(s, 0) == 102 && byte_at(s, 1) == 108 && byte_at(s, 2) == 111 && byte_at(s, 3) == 97 && byte_at(s, 4) == 116 { Some(Keyword::Float) }
    else if s.len() == 4 && byte_at(s, 0) == 102 && byte_at(s, 1) == 114 && byte_at(s, 2) == 111 && byte_at(s, 3) == 109 { Some(Keyword::From) }
    else if s.len() == 5 && byte_at(s, 0) == 103 && byte_at(s, 1) == 114 && byte_at(s, 2) == 111 && byte_at(s, 3) == 117 && byte_at(s, 4) == 112 { Some(Keyword::Group) }
    else if s.len() == 6 && byte_at(s, 0) == 104 && byte_at(s, 1) == 97 && byte_at(s, 2) == 118 && byte_at(s, 3) == 105 && byte_at(s, 4) == 110 && byte_at(s, 5) == 103 { Some(Keyword::Having) }
    else if s.len() == 2 && byte_at(s, 0) == 105 && byte_at(s, 1) == 102 { Some(Keyword::If) }
    else if s.len() == 5 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 100 && byte_at(s, 3) == 101 && byte_at(s, 4) == 120 { Some(Keyword::Index) }
    else if s.len() == 8 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 102 && byte_at(s, 3) == 105 && byte_at(s, 4) == 110 && byte_at(s, 5) == 105 && byte_at(s, 6) == 116 && byte_at(s, 7) == 121 { Some(Keyword::Infinity) }
    else if s.len() == 5 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 110 && byte_at(s, 3) == 101 && byte_at(s, 4) == 114 { Some(Keyword::Inner) }
    else if s.len() == 6 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 115 && byte_at(s, 3) == 101 && byte_at(s, 4) == 114 && byte_at(s, 5) == 116 { Some(Keyword::Insert) }
    else if s.len() == 3 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 116 { Some(Keyword::Int) }
    else if s.len() == 7 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 116 && byte_at(s, 3) == 101 && byte_at(s, 4) == 103 && byte_at(s, 5) == 101 && byte_at(s, 6) == 114 { Some(Keyword::Integer) }
    else if s.len() == 4 && byte_at(s, 0) == 105 && byte_at(s, 1) == 110 && byte_at(s, 2) == 116 && byte_at(s, 3) == 111 { Some(Keyword::Into) }
    else if s.len() == 2 && byte_at(s, 0) == 105 && byte_at(s, 1) == 115 { Some(Keyword::Is) }
    else if s.len() == 4 && byte_at(s, 0) == 106 && byte_at(s, 1) == 111 && byte_at(s, 2) == 105 && byte_at(s, 3) == 110 { Some(Keyword::Join) }
    else if s.len() == 3 && byte_at(s, 0) == 107 && byte_at(s, 1) == 101 && byte_at(s, 2) == 121 { Some(Keyword::Key) }
    else if s.len() == 4 && byte_at(s, 0) == 108 && byte_at(s, 1) == 101 && byte_at(s, 2) == 102 && byte_at(s, 3) == 116 { Some(Keyword::Left) }
    else if s.len() == 4 && byte_at(s, 0) == 108 && byte_at(s, 1) == 105 && byte_at(s, 2) == 107 && byte_at(s, 3) == 101 { Some(Keyword::Like) }
    else if s.len() == 5 && byte_at(s, 0) == 108 && byte_at(s, 1) == 105 && byte_at(s, 2) == 109 && byte_at(s, 3) == 105 && byte_at(s, 4) == 116 { Some(Keyword::Limit) }
    else if s.len() == 3 && byte_at(s, 0) == 110 && byte_at(s, 1) == 97 && byte_at(s, 2) == 110 { Some(Keyword::NaN) }
    else if s.len() == 3 && byte_at(s, 0) == 110 && byte_at(s, 1) == 111 && byte_at(s, 2) == 116 { Some(Keyword::Not) }
    else if s.len() == 4 && byte_at(s, 0) == 110 && byte_at(s, 1) == 117 && byte_at(s, 2) == 108 && byte_at(s, 3) == 108 { Some(Keyword::Null) }
    else if s.len() == 2 && byte_at(s, 0) == 111 && byte_at(s, 1) == 102 { Some(Keyword::Of) }
    else if s.len() == 6 && byte_at(s, 0) == 111 && byte_at(s, 1) == 102 && byte_at(s, 2) == 102 && byte_at(s, 3) == 115 && byte_at(s, 4) == 101 && byte_at(s, 5) == 116 { Some(Keyword::Offset) }
    else if s.len() == 2 && byte_at(s, 0) == 111 && byte_at(s, 1) == 110 { Some(Keyword::On) }
    else if s.len() == 4 && byte_at(s, 0) == 111 && byte_at(s, 1) == 110 && byte_at(s, 2) == 108 && byte_at(s, 3) == 121 { Some(Keyword::Only) }
    else if s.len() == 2 && byte_at(s, 0) == 111 && byte_at(s, 1) == 114 { Some(Keyword::Or) }
    else if s.len() == 5 && byte_at(s, 0) == 111 && byte_at(s, 1) == 114 && byte_at(s, 2) == 100 && byte_at(s, 3) == 101 && byte_at(s, 4) == 114 { Some(Keyword::Order) }
    else if s.len() == 5 && byte_at(s, 0) == 111 && byte_at(s, 1) == 117 && byte_at(s, 2) == 116 && byte_at(s, 3) == 101 && byte_at(s, 4) == 114 { Some(Keyword::Outer) }
    else if s.len() == 7 && byte_at(s, 0) == 112 && byte_at(s, 1) == 114 && byte_at(s, 2) == 105 && byte_at(s, 3) == 109 && byte_at(s, 4) == 97 && byte_at(s, 5) == 114 && byte_at(s, 6) == 121 { Some(Keyword::Primary) }
    else if s.len() == 4 && byte_at(s, 0) == 114 && byte_at(s, 1) == 101 && byte_at(s, 2) == 97 && byte_at(s, 3) == 100 { Some(Keyword::Read) }
    else if s.len() == 10 && byte_at(s, 0) == 114 && byte_at(s, 1) == 101 && byte_at(s, 2) == 102 && byte_at(s, 3) == 101 && byte_at(s, 4) == 114 && byte_at(s, 5) == 101 && byte_at(s, 6) == 110 && byte_at(s, 7) == 99 && byte_at(s, 8) == 101 && byte_at(s, 9) == 115 { Some(Keyword::References) }
    else if s.len() == 5 && byte_at(s, 0) == 114 && byte_at(s, 1) == 105 && byte_at(s, 2) == 103 && byte_at(s, 3) == 104 && byte_at(s, 4) == 116 { Some(Keyword::Right) }
    else if s.len() == 8 && byte_at(s, 0) == 114 && byte_at(s, 1) == 111 && byte_at(s, 2) == 108 && byte_at(s, 3) == 108 && byte_at(s, 4) == 98 && byte_at(s, 5) == 97 && byte_at(s, 6) == 99 && byte_at(s, 7) == 107 { Some(Keyword::Rollback) }
    else if s.len() == 6 && byte_at(s, 0) == 115 && byte_at(s, 1) == 101 && byte_at(s, 2) == 108 && byte_at(s, 3) == 101 && byte_at(s, 4) == 99 && byte_at(s, 5) == 116 { Some(Keyword::Select) }
    else if s.len() == 3 && byte_at(s, 0) == 115 && byte_at(s, 1) == 101 && byte_at(s, 2) == 116 { Some(Keyword::Set) }
    else if s.len() == 6 && byte_at(s, 0) == 115 && byte_at(s, 1) == 116 && byte_at(s, 2) == 114 && byte_at(s, 3) == 105 && byte_at(s, 4) == 110 && byte_at(s, 5) == 103 { Some(Keyword::String) }
    else if s.len() == 6 && byte_at(s, 0) == 115 && byte_at(s, 1) == 121 && byte_at(s, 2) == 115 && byte_at(s, 3) == 116 && byte_at(s, 4) == 101 && byte_at(s, 5) == 109 { Some(Keyword::System) }
    else if s.len() == 5 && byte_at(s, 0) == 116 && byte_at(s, 1) == 97 && byte_at(s, 2) == 98 && byte_at(s, 3) == 108 && byte_at(s, 4) == 101 { Some(Keyword::Table) }
    else if s.len() == 4 && byte_at(s, 0) == 116 && byte_at(s, 1) == 101 && byte_at(s, 2) == 120 && byte_at(s, 3) == 116 { Some(Keyword::Text) }
    else if s.len() == 4 && byte_at(s, 0) == 116 && byte_at(s, 1) == 105 && byte_at(s, 2) == 109 && byte_at(s, 3) == 101 { Some(Keyword::Time) }
    else if s.len() == 11 && byte_at(s, 0) == 116 && byte_at(s, 1) == 114 && byte_at(s, 2) == 97 && byte_at(s, 3) == 110 && byte_at(s, 4) == 115 && byte_at(s, 5) == 97 && byte_at(s, 6) == 99 && byte_at(s, 7) == 116 && byte_at(s, 8) == 105 && byte_at(s, 9) == 111 && byte_at(s, 10) == 110 { Some(Keyword::Transaction) }
    else if s.len() == 4 && byte_at(s, 0) == 116 && byte_at(s, 1) == 114 && byte_at(s, 2) == 117 && byte_at(s, 3) == 101 { Some(Keyword::True) }
    else if s.len() == 6 && byte_at(s, 0) == 117 && byte_at(s, 1) == 110 && byte_at(s, 2) == 105 && byte_at(s, 3) == 113 && byte_at(s, 4) == 117 && byte_at(s, 5) == 101 { Some(Keyword::Unique) }
    else if s.len() == 6 && byte_at(s, 0) == 117 && byte_at(s, 1) == 112 && byte_at(s, 2) == 100 && byte_at(s, 3) == 97 && byte_at(s, 4) == 116 && byte_at(s, 5) == 101 { Some(Keyword::Update) }
    else if s.len() == 6 && byte_at(s, 0) == 118 && byte_at(s, 1) == 97 && byte_at(s, 2) == 108 && byte_at(s, 3) == 117 && byte_at(s, 4) == 101 && byte_at(s, 5) == 115 { Some(Keyword::Values) }
    else if s.len() == 7 && byte_at(s, 0) == 118 && byte_at(s, 1) == 97 && byte_at(s, 2) == 114 && byte_at(s, 3) == 99 && byte_at(s, 4) == 104 && byte_at(s, 5) == 97 && byte_at(s, 6) == 114 { Some(Keyword::Varchar) }
    else if s.len() == 5 && byte_at(s, 0) == 119 && byte_at(s, 1) == 104 && byte_at(s, 2) == 101 && byte_at(s, 3) == 114 && byte_at(s, 4) == 101 { Some(Keyword::Where) }
    else if s.len() == 5 && byte_at(s, 0) == 119 && byte_at(s, 1) == 114 && byte_at(s, 2) == 105 && byte_at(s, 3) == 116 && byte_at(s, 4) == 101 { Some(Keyword::Write) }
    else { None }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g0(k: Keyword)
    requires k == Keyword::As || k == Keyword::Asc || k == Keyword::And || k == Keyword::Begin || k == Keyword::Bool || k == Keyword::Boolean || k == Keyword::By || k == Keyword::Commit || k == Keyword::Create || k == Keyword::Cross || k == Keyword::Default,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::As => assert(classify_kw(kw_text(Keyword::As)) == Some(Keyword::As)),
        Keyword::Asc => assert(classify_kw(kw_text(Keyword::Asc)) == Some(Keyword::Asc)),
        Keyword::And => assert(classify_kw(kw_text(Keyword::And)) == Some(Keyword::And)),
        Keyword::Begin => assert(classify_kw(kw_text(Keyword::Begin)) == Some(Keyword::Begin)),
        Keyword::Bool => assert(classify_kw(kw_text(Keyword::Bool)) == Some(Keyword::Bool)),
        Keyword::Boolean => assert(classify_kw(kw_text(Keyword::Boolean)) == Some(Keyword::Boolean)),
        Keyword::By => assert(classify_kw(kw_text(Keyword::By)) == Some(Keyword::By)),
        Keyword::Commit => assert(classify_kw(kw_text(Keyword::Commit)) == Some(Keyword::Commit)),
        Keyword::Create => assert(classify_kw(kw_text(Keyword::Create)) == Some(Keyword::Create)),
        Keyword::Cross => assert(classify_kw(kw_text(Keyword::Cross)) == Some(Keyword::Cross)),
        Keyword::Default => assert(classify_kw(kw_text(Keyword::Default)) == Some(Keyword::Default)),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g1(k: Keyword)
    requires k == Keyword::Delete || k == Keyword::Desc || k == Keyword::Double || k == Keyword::Drop || k == Keyword::Exists || k == Keyword::Explain || k == Keyword::False || k == Keyword::Float || k == Keyword::From || k == Keyword::Group || k == Keyword::Having,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::Delete => assert(classify_kw(kw_text(Keyword::Delete)) == Some(Keyword::Delete)),
        Keyword::Desc => assert(classify_kw(kw_text(Keyword::Desc)) == Some(Keyword::Desc)),
        Keyword::Double => assert(classify_kw(kw_text(Keyword::Double)) == Some(Keyword::Double)),
        Keyword::Drop => assert(classify_kw(kw_text(Keyword::Drop)) == Some(Keyword::Drop)),
        Keyword::Exists => assert(classify_kw(kw_text(Keyword::Exists)) == Some(Keyword::Exists)),
        Keyword::Explain => assert(classify_kw(kw_text(Keyword::Explain)) == Some(Keyword::Explain)),
        Keyword::False => assert(classify_kw(kw_text(Keyword::False)) == Some(Keyword::False)),
        Keyword::Float => assert(classify_kw(kw_text(Keyword::Float)) == Some(Keyword::Float)),
        Keyword::From => assert(classify_kw(kw_text(Keyword::From)) == Some(Keyword::From)),
        Keyword::Group => assert(classify_kw(kw_text(Keyword::Group)) == Some(Keyword::Group)),
        Keyword::Having => assert(classify_kw(kw_text(Keyword::Having)) == Some(Keyword::Having)),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g2(k: Keyword)
    requires k == Keyword::If || k == Keyword::Index || k == Keyword::Infinity || k == Keyword::Inner || k == Keyword::Insert || k == Keyword::Int || k == Keyword::Integer || k == Keyword::Into || k == Keyword::Is || k == Keyword::Join || k == Keyword::Key,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::If => assert(classify_kw(kw_text(Keyword::If)) == Some(Keyword::If)),
        Keyword::Index => assert(classify_kw(kw_text(Keyword::Index)) == Some(Keyword::Index)),
        Keyword::Infinity => assert(classify_kw(kw_text(Keyword::Infinity)) == Some(Keyword::Infinity)),
        Keyword::Inner => assert(classify_kw(kw_text(Keyword::Inner)) == Some(Keyword::Inner)),
        Keyword::Insert => assert(classify_kw(kw_text(Keyword::Insert)) == Some(Keyword::Insert)),
        Keyword::Int => assert(classify_kw(kw_text(Keyword::Int)) == Some(Keyword::Int)),
        Keyword::Integer => assert(classify_kw(kw_text(Keyword::Integer)) == Some(Keyword::Integer)),
        Keyword::Into => assert(classify_kw(kw_text(Keyword::Into)) == Some(Keyword::Into)),
        Keyword::Is => assert(classify_kw(kw_text(Keyword::Is)) == Some(Keyword::Is)),
        Keyword::Join => assert(classify_kw(kw_text(Keyword::Join)) == Some(Keyword::Join)),
        Keyword::Key => assert(classify_kw(kw_text(Keyword::Key)) == Some(Keyword::Key)),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g3(k: Keyword)
    requires k == Keyword::Left || k == Keyword::Like || k == Keyword::Limit || k == Keyword::NaN || k == Keyword::Not || k == Keyword::Null || k == Keyword::Of || k == Keyword::Offset || k == Keyword::On || k == Keyword::Only || k == Keyword::Or,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::Left => assert(classify_kw(kw_text(Keyword::Left)) == Some(Keyword::Left)),
        Keyword::Like => assert(classify_kw(kw_text(Keyword::Like)) == Some(Keyword::Like)),
        Keyword::Limit => assert(classify_kw(kw_text(Keyword::Limit)) == Some(Keyword::Limit)),
        Keyword::NaN => assert(classify_kw(kw_text(Keyword::NaN)) == Some(Keyword::NaN)),
        Keyword::Not => assert(classify_kw(kw_text(Keyword::Not)) == Some(Keyword::Not)),
        Keyword::Null => assert(classify_kw(kw_text(Keyword::Null)) == Some(Keyword::Null)),
        Keyword::Of => assert(classify_kw(kw_text(Keyword::Of)) == Some(Keyword::Of)),
        Keyword::Offset => assert(classify_kw(kw_text(Keyword::Offset)) == Some(Keyword::Offset)),
        Keyword::On => assert(classify_kw(kw_text(Keyword::On)) == Some(Keyword::On)),
        Keyword::Only => assert(classify_kw(kw_text(Keyword::Only)) == Some(Keyword::Only)),
        Keyword::Or => assert(classify_kw(kw_text(Keyword::Or)) == Some(Keyword::Or)),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g4(k: Keyword)
    requires k == Keyword::Order || k == Keyword::Outer || k == Keyword::Primary || k == Keyword::Read || k == Keyword::References || k == Keyword::Right || k == Keyword::Rollback || k == Keyword::Select || k == Keyword::Set || k == Keyword::String || k == Keyword::System,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::Order => assert(classify_kw(kw_text(Keyword::Order)) == Some(Keyword::Order)),
        Keyword::Outer => assert(classify_kw(kw_text(Keyword::Outer)) == Some(Keyword::Outer)),
        Keyword::Primary => assert(classify_kw(kw_text(Keyword::Primary)) == Some(Keyword::Primary)),
        Keyword::Read => assert(classify_kw(kw_text(Keyword::Read)) == Some(Keyword::Read)),
        Keyword::References => assert(classify_kw(kw_text(Keyword::References)) == Some(Keyword::References)),
        Keyword::Right => assert(classify_kw(kw_text(Keyword::Right)) == Some(Keyword::Right)),
        Keyword::Rollback => assert(classify_kw(kw_text(Keyword::Rollback)) == Some(Keyword::Rollback)),
        Keyword::Select => assert(classify_kw(kw_text(Keyword::Select)) == Some(Keyword::Select)),
        Keyword::Set => assert(classify_kw(kw_text(Keyword::Set)) == Some(Keyword::Set)),
        Keyword::String => assert(classify_kw(kw_text(Keyword::String)) == Some(Keyword::String)),
        Keyword::System => assert(classify_kw(kw_text(Keyword::System)) == Some(Keyword::System)),
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_classify_kw_text_g5(k: Keyword)
    requires k == Keyword::Table || k == Keyword::Text || k == Keyword::Time || k == Keyword::Transaction || k == Keyword::True || k == Keyword::Unique || k == Keyword::Update || k == Keyword::Values || k == Keyword::Varchar || k == Keyword::Where || k == Keyword::Write,
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::Table => assert(classify_kw(kw_text(Keyword::Table)) == Some(Keyword::Table)),
        Keyword::Text => assert(classify_kw(kw_text(Keyword::Text)) == Some(Keyword::Text)),
        Keyword::Time => assert(classify_kw(kw_text(Keyword::Time)) == Some(Keyword::Time)),
        Keyword::Transaction => assert(classify_kw(kw_text(Keyword::Transaction)) == Some(Keyword::Transaction)),
        Keyword::True => assert(classify_kw(kw_text(Keyword::True)) == Some(Keyword::True)),
        Keyword::Unique => assert(classify_kw(kw_text(Keyword::Unique)) == Some(Keyword::Unique)),
        Keyword::Update => assert(classify_kw(kw_text(Keyword::Update)) == Some(Keyword::Update)),
        Keyword::Values => assert(classify_kw(kw_text(Keyword::Values)) == Some(Keyword::Values)),
        Keyword::Varchar => assert(classify_kw(kw_text(Keyword::Varchar)) == Some(Keyword::Varchar)),
        Keyword::Where => assert(classify_kw(kw_text(Keyword::Where)) == Some(Keyword::Where)),
        Keyword::Write => assert(classify_kw(kw_text(Keyword::Write)) == Some(Keyword::Write)),
        _ => {},
    }
}

/// The keyword table round-trips: classifying a keyword's own text recovers
/// it (the table is injective on its domain). Split into grouped helpers so
/// each SMT query stays under the resource limit.
pub proof fn lemma_classify_kw_text(k: Keyword)
    ensures classify_kw(kw_text(k)) == Some(k),
{
    match k {
        Keyword::As | Keyword::Asc | Keyword::And | Keyword::Begin | Keyword::Bool | Keyword::Boolean | Keyword::By | Keyword::Commit | Keyword::Create | Keyword::Cross | Keyword::Default => lemma_classify_kw_text_g0(k),
        Keyword::Delete | Keyword::Desc | Keyword::Double | Keyword::Drop | Keyword::Exists | Keyword::Explain | Keyword::False | Keyword::Float | Keyword::From | Keyword::Group | Keyword::Having => lemma_classify_kw_text_g1(k),
        Keyword::If | Keyword::Index | Keyword::Infinity | Keyword::Inner | Keyword::Insert | Keyword::Int | Keyword::Integer | Keyword::Into | Keyword::Is | Keyword::Join | Keyword::Key => lemma_classify_kw_text_g2(k),
        Keyword::Left | Keyword::Like | Keyword::Limit | Keyword::NaN | Keyword::Not | Keyword::Null | Keyword::Of | Keyword::Offset | Keyword::On | Keyword::Only | Keyword::Or => lemma_classify_kw_text_g3(k),
        Keyword::Order | Keyword::Outer | Keyword::Primary | Keyword::Read | Keyword::References | Keyword::Right | Keyword::Rollback | Keyword::Select | Keyword::Set | Keyword::String | Keyword::System => lemma_classify_kw_text_g4(k),
        Keyword::Table | Keyword::Text | Keyword::Time | Keyword::Transaction | Keyword::True | Keyword::Unique | Keyword::Update | Keyword::Values | Keyword::Varchar | Keyword::Where | Keyword::Write => lemma_classify_kw_text_g5(k),
    }
}

/// ASCII lowercase of one byte (upper-case letters map down 32; others fixed).
pub open spec fn ascii_lower(b: u8) -> u8 {
    if 65 <= b <= 90 { (b + 32) as u8 } else { b }
}

/// A lowercase ASCII letter.
pub open spec fn is_lower_letter(b: u8) -> bool {
    97 <= b <= 122
}

/// Every byte is a lowercase ASCII letter.
pub open spec fn all_lower_letters(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_lower_letter(#[trigger] s[i])
}

/// ASCII-lowercase a byte sequence, pointwise.
pub open spec fn ascii_lower_seq(s: Seq<u8>) -> Seq<u8> {
    Seq::new(s.len(), |i: int| ascii_lower(s[i]))
}

/// Lowercasing an already-lowercase-letter run is the identity.
pub proof fn lemma_ascii_lower_idem(t: Seq<u8>)
    requires
        all_lower_letters(t),
    ensures
        ascii_lower_seq(t) == t,
{
    assert forall|i: int| 0 <= i < t.len() implies ascii_lower_seq(t)[i] == t[i] by {
        assert(is_lower_letter(t[i]));
    }
    assert(ascii_lower_seq(t) =~= t);
}

/// A non-empty lowercase-letter run is a well-formed identifier byte run.
pub proof fn lemma_lower_letters_ident_bytes(t: Seq<u8>)
    requires
        t.len() >= 1,
        all_lower_letters(t),
    ensures
        is_ident_bytes(t),
{
    assert(is_lower_letter(t[0]));
    assert(is_ident_start(t[0]));
    assert forall|i: int| 0 <= i < t.len() implies is_ident_cont(#[trigger] t[i]) by {
        assert(is_lower_letter(t[i]));
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g0(k: Keyword)
    requires k == Keyword::As || k == Keyword::Asc || k == Keyword::And || k == Keyword::Begin || k == Keyword::Bool || k == Keyword::Boolean || k == Keyword::By || k == Keyword::Commit || k == Keyword::Create || k == Keyword::Cross || k == Keyword::Default,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::As => {
            assert(kw_text(Keyword::As).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::As)));
        },
        Keyword::Asc => {
            assert(kw_text(Keyword::Asc).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Asc)));
        },
        Keyword::And => {
            assert(kw_text(Keyword::And).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::And)));
        },
        Keyword::Begin => {
            assert(kw_text(Keyword::Begin).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Begin)));
        },
        Keyword::Bool => {
            assert(kw_text(Keyword::Bool).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Bool)));
        },
        Keyword::Boolean => {
            assert(kw_text(Keyword::Boolean).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Boolean)));
        },
        Keyword::By => {
            assert(kw_text(Keyword::By).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::By)));
        },
        Keyword::Commit => {
            assert(kw_text(Keyword::Commit).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Commit)));
        },
        Keyword::Create => {
            assert(kw_text(Keyword::Create).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Create)));
        },
        Keyword::Cross => {
            assert(kw_text(Keyword::Cross).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Cross)));
        },
        Keyword::Default => {
            assert(kw_text(Keyword::Default).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Default)));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g1(k: Keyword)
    requires k == Keyword::Delete || k == Keyword::Desc || k == Keyword::Double || k == Keyword::Drop || k == Keyword::Exists || k == Keyword::Explain || k == Keyword::False || k == Keyword::Float || k == Keyword::From || k == Keyword::Group || k == Keyword::Having,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::Delete => {
            assert(kw_text(Keyword::Delete).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Delete)));
        },
        Keyword::Desc => {
            assert(kw_text(Keyword::Desc).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Desc)));
        },
        Keyword::Double => {
            assert(kw_text(Keyword::Double).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Double)));
        },
        Keyword::Drop => {
            assert(kw_text(Keyword::Drop).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Drop)));
        },
        Keyword::Exists => {
            assert(kw_text(Keyword::Exists).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Exists)));
        },
        Keyword::Explain => {
            assert(kw_text(Keyword::Explain).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Explain)));
        },
        Keyword::False => {
            assert(kw_text(Keyword::False).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::False)));
        },
        Keyword::Float => {
            assert(kw_text(Keyword::Float).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Float)));
        },
        Keyword::From => {
            assert(kw_text(Keyword::From).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::From)));
        },
        Keyword::Group => {
            assert(kw_text(Keyword::Group).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Group)));
        },
        Keyword::Having => {
            assert(kw_text(Keyword::Having).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Having)));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g2(k: Keyword)
    requires k == Keyword::If || k == Keyword::Index || k == Keyword::Infinity || k == Keyword::Inner || k == Keyword::Insert || k == Keyword::Int || k == Keyword::Integer || k == Keyword::Into || k == Keyword::Is || k == Keyword::Join || k == Keyword::Key,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::If => {
            assert(kw_text(Keyword::If).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::If)));
        },
        Keyword::Index => {
            assert(kw_text(Keyword::Index).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Index)));
        },
        Keyword::Infinity => {
            assert(kw_text(Keyword::Infinity).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Infinity)));
        },
        Keyword::Inner => {
            assert(kw_text(Keyword::Inner).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Inner)));
        },
        Keyword::Insert => {
            assert(kw_text(Keyword::Insert).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Insert)));
        },
        Keyword::Int => {
            assert(kw_text(Keyword::Int).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Int)));
        },
        Keyword::Integer => {
            assert(kw_text(Keyword::Integer).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Integer)));
        },
        Keyword::Into => {
            assert(kw_text(Keyword::Into).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Into)));
        },
        Keyword::Is => {
            assert(kw_text(Keyword::Is).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Is)));
        },
        Keyword::Join => {
            assert(kw_text(Keyword::Join).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Join)));
        },
        Keyword::Key => {
            assert(kw_text(Keyword::Key).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Key)));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g3(k: Keyword)
    requires k == Keyword::Left || k == Keyword::Like || k == Keyword::Limit || k == Keyword::NaN || k == Keyword::Not || k == Keyword::Null || k == Keyword::Of || k == Keyword::Offset || k == Keyword::On || k == Keyword::Only || k == Keyword::Or,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::Left => {
            assert(kw_text(Keyword::Left).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Left)));
        },
        Keyword::Like => {
            assert(kw_text(Keyword::Like).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Like)));
        },
        Keyword::Limit => {
            assert(kw_text(Keyword::Limit).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Limit)));
        },
        Keyword::NaN => {
            assert(kw_text(Keyword::NaN).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::NaN)));
        },
        Keyword::Not => {
            assert(kw_text(Keyword::Not).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Not)));
        },
        Keyword::Null => {
            assert(kw_text(Keyword::Null).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Null)));
        },
        Keyword::Of => {
            assert(kw_text(Keyword::Of).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Of)));
        },
        Keyword::Offset => {
            assert(kw_text(Keyword::Offset).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Offset)));
        },
        Keyword::On => {
            assert(kw_text(Keyword::On).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::On)));
        },
        Keyword::Only => {
            assert(kw_text(Keyword::Only).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Only)));
        },
        Keyword::Or => {
            assert(kw_text(Keyword::Or).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Or)));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g4(k: Keyword)
    requires k == Keyword::Order || k == Keyword::Outer || k == Keyword::Primary || k == Keyword::Read || k == Keyword::References || k == Keyword::Right || k == Keyword::Rollback || k == Keyword::Select || k == Keyword::Set || k == Keyword::String || k == Keyword::System,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::Order => {
            assert(kw_text(Keyword::Order).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Order)));
        },
        Keyword::Outer => {
            assert(kw_text(Keyword::Outer).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Outer)));
        },
        Keyword::Primary => {
            assert(kw_text(Keyword::Primary).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Primary)));
        },
        Keyword::Read => {
            assert(kw_text(Keyword::Read).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Read)));
        },
        Keyword::References => {
            assert(kw_text(Keyword::References).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::References)));
        },
        Keyword::Right => {
            assert(kw_text(Keyword::Right).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Right)));
        },
        Keyword::Rollback => {
            assert(kw_text(Keyword::Rollback).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Rollback)));
        },
        Keyword::Select => {
            assert(kw_text(Keyword::Select).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Select)));
        },
        Keyword::Set => {
            assert(kw_text(Keyword::Set).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Set)));
        },
        Keyword::String => {
            assert(kw_text(Keyword::String).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::String)));
        },
        Keyword::System => {
            assert(kw_text(Keyword::System).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::System)));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_kw_text_shape_g5(k: Keyword)
    requires k == Keyword::Table || k == Keyword::Text || k == Keyword::Time || k == Keyword::Transaction || k == Keyword::True || k == Keyword::Unique || k == Keyword::Update || k == Keyword::Values || k == Keyword::Varchar || k == Keyword::Where || k == Keyword::Write,
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::Table => {
            assert(kw_text(Keyword::Table).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Table)));
        },
        Keyword::Text => {
            assert(kw_text(Keyword::Text).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Text)));
        },
        Keyword::Time => {
            assert(kw_text(Keyword::Time).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Time)));
        },
        Keyword::Transaction => {
            assert(kw_text(Keyword::Transaction).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Transaction)));
        },
        Keyword::True => {
            assert(kw_text(Keyword::True).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::True)));
        },
        Keyword::Unique => {
            assert(kw_text(Keyword::Unique).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Unique)));
        },
        Keyword::Update => {
            assert(kw_text(Keyword::Update).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Update)));
        },
        Keyword::Values => {
            assert(kw_text(Keyword::Values).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Values)));
        },
        Keyword::Varchar => {
            assert(kw_text(Keyword::Varchar).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Varchar)));
        },
        Keyword::Where => {
            assert(kw_text(Keyword::Where).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Where)));
        },
        Keyword::Write => {
            assert(kw_text(Keyword::Write).len() >= 1);
            assert(all_lower_letters(kw_text(Keyword::Write)));
        },
        _ => {},
    }
}

/// Every keyword's text is a non-empty run of lowercase ASCII letters (so it
/// scans as one identifier and lowercasing it is the identity).
pub proof fn lemma_kw_text_shape(k: Keyword)
    ensures
        kw_text(k).len() >= 1,
        all_lower_letters(kw_text(k)),
{
    match k {
        Keyword::As | Keyword::Asc | Keyword::And | Keyword::Begin | Keyword::Bool | Keyword::Boolean | Keyword::By | Keyword::Commit | Keyword::Create | Keyword::Cross | Keyword::Default => lemma_kw_text_shape_g0(k),
        Keyword::Delete | Keyword::Desc | Keyword::Double | Keyword::Drop | Keyword::Exists | Keyword::Explain | Keyword::False | Keyword::Float | Keyword::From | Keyword::Group | Keyword::Having => lemma_kw_text_shape_g1(k),
        Keyword::If | Keyword::Index | Keyword::Infinity | Keyword::Inner | Keyword::Insert | Keyword::Int | Keyword::Integer | Keyword::Into | Keyword::Is | Keyword::Join | Keyword::Key => lemma_kw_text_shape_g2(k),
        Keyword::Left | Keyword::Like | Keyword::Limit | Keyword::NaN | Keyword::Not | Keyword::Null | Keyword::Of | Keyword::Offset | Keyword::On | Keyword::Only | Keyword::Or => lemma_kw_text_shape_g3(k),
        Keyword::Order | Keyword::Outer | Keyword::Primary | Keyword::Read | Keyword::References | Keyword::Right | Keyword::Rollback | Keyword::Select | Keyword::Set | Keyword::String | Keyword::System => lemma_kw_text_shape_g4(k),
        Keyword::Table | Keyword::Text | Keyword::Time | Keyword::Transaction | Keyword::True | Keyword::Unique | Keyword::Update | Keyword::Values | Keyword::Varchar | Keyword::Where | Keyword::Write => lemma_kw_text_shape_g5(k),
    }
}

/// Scan an identifier run as a *keyword*: if it starts an identifier, take the
/// maximal run, lowercase it, and classify. `None` here means "not a keyword"
/// (a plain identifier — a later brick, needing the `String` trust bridge).
pub open spec fn lscan_keyword(input: Seq<u8>, pos: int) -> (Option<Keyword>, int) {
    if 0 <= pos < input.len() && is_ident_start(input[pos]) {
        let e = scan_ident_end(input, pos);
        (classify_kw(ascii_lower_seq(input.subrange(pos, e))), e)
    } else {
        (None, pos)
    }
}

/// Keyword roundtrip: an identifier run equal to a keyword's lowercase text,
/// followed by a non-continuation boundary, scans back to that keyword and
/// advances past it. Fully axiom-free.
pub proof fn lemma_lscan_keyword(kw: Keyword, tail: Seq<u8>)
    requires
        tail.len() == 0 || !is_ident_cont(tail[0]),
    ensures
        lscan_keyword(kw_text(kw) + tail, 0) == (Some(kw), kw_text(kw).len() as int),
{
    let d = kw_text(kw);
    let input = d + tail;
    lemma_kw_text_shape(kw);
    lemma_lower_letters_ident_bytes(d);
    assert(input[0] == d[0]);
    assert(is_ident_start(input[0]));
    lemma_scan_ident_roundtrip(d, tail);
    assert(scan_ident_end(input, 0) == d.len());
    assert(input.subrange(0, d.len() as int) =~= d);
    lemma_ascii_lower_idem(d);
    lemma_classify_kw_text(kw);
}

/// Map a symbol `TokenView` back to its `Token` (unit variants; safe because
/// symbols carry no payload). Non-symbol views map to `Period` (unused).
pub open spec fn sym_token_of(tv: TokenView) -> Token {
    match tv {
        TokenView::Period => Token::Period,
        TokenView::Equal => Token::Equal,
        TokenView::NotEqual => Token::NotEqual,
        TokenView::GreaterThan => Token::GreaterThan,
        TokenView::GreaterThanOrEqual => Token::GreaterThanOrEqual,
        TokenView::LessThan => Token::LessThan,
        TokenView::LessThanOrEqual => Token::LessThanOrEqual,
        TokenView::LessOrGreaterThan => Token::LessOrGreaterThan,
        TokenView::Plus => Token::Plus,
        TokenView::Minus => Token::Minus,
        TokenView::Asterisk => Token::Asterisk,
        TokenView::Slash => Token::Slash,
        TokenView::Caret => Token::Caret,
        TokenView::Percent => Token::Percent,
        TokenView::Exclamation => Token::Exclamation,
        TokenView::Question => Token::Question,
        TokenView::Comma => Token::Comma,
        TokenView::Semicolon => Token::Semicolon,
        TokenView::OpenParen => Token::OpenParen,
        TokenView::CloseParen => Token::CloseParen,
        _ => Token::Period,
    }
}

/// A symbol token view (punctuation or operator — not number/keyword/ident/string).
pub open spec fn is_sym_view(tv: TokenView) -> bool {
    match tv {
        TokenView::Number(_) => false,
        TokenView::Keyword(_) => false,
        TokenView::Ident(_) => false,
        TokenView::String(_) => false,
        _ => true,
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_sym_token_props(tv: TokenView)
    requires is_sym_view(tv),
    ensures
        token_view(sym_token_of(tv)) == tv,
        is_punct1(sym_token_of(tv)) || is_op(sym_token_of(tv)),
        lex_print_sym(sym_token_of(tv)).len() >= 1,
        !is_digit(lex_print_sym(sym_token_of(tv))[0]),
        !is_ident_start(lex_print_sym(sym_token_of(tv))[0]),
        !is_ws(lex_print_sym(sym_token_of(tv))[0]),
        lex_print_sym(sym_token_of(tv))[0] != 39,
{
    match tv {
        TokenView::Period => {
            let t = Token::Period;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Equal => {
            let t = Token::Equal;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::NotEqual => {
            let t = Token::NotEqual;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::GreaterThan => {
            let t = Token::GreaterThan;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::GreaterThanOrEqual => {
            let t = Token::GreaterThanOrEqual;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::LessThan => {
            let t = Token::LessThan;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::LessThanOrEqual => {
            let t = Token::LessThanOrEqual;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::LessOrGreaterThan => {
            let t = Token::LessOrGreaterThan;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Plus => {
            let t = Token::Plus;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Minus => {
            let t = Token::Minus;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Asterisk => {
            let t = Token::Asterisk;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Slash => {
            let t = Token::Slash;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Caret => {
            let t = Token::Caret;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Percent => {
            let t = Token::Percent;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Exclamation => {
            let t = Token::Exclamation;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Question => {
            let t = Token::Question;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Comma => {
            let t = Token::Comma;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::Semicolon => {
            let t = Token::Semicolon;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::OpenParen => {
            let t = Token::OpenParen;
            assert(lex_print_sym(t).len() >= 1);
        },
        TokenView::CloseParen => {
            let t = Token::CloseParen;
            assert(lex_print_sym(t).len() >= 1);
        },
        _ => {},
    }
}

/// Canonical byte print of a byte-determined token view. Numbers print their raw
/// bytes; keywords print their lowercase text (the lexer lowercases before
/// classifying, so lowercase re-lexes exactly — the uppercase `Display` form is a
/// string-level printer concern); symbols delegate to `lex_print_sym`. `Ident`
/// and `String` carry `String` payloads and are handled by the deferred trust
/// bridge, so they print empty here.
pub open spec fn lex_print_tv(tv: TokenView) -> Seq<u8> {
    match tv {
        TokenView::Number(v) => v,
        TokenView::Keyword(kw) => kw_text(kw),
        TokenView::Ident(_) => Seq::empty(),
        TokenView::String(_) => Seq::empty(),
        _ => lex_print_sym(sym_token_of(tv)),
    }
}

/// A number byte-run re-scans to itself under any number boundary. Both printed
/// number forms (pure integer run, `digits.digits`) satisfy this; carrying it as
/// a predicate lets the token roundtrip stay agnostic to which form a number is.
pub open spec fn rescans_num(v: Seq<u8>) -> bool {
    forall|tail: Seq<u8>| num_tail_ok(tail) ==> #[trigger] scan_num_full_end(v + tail, 0) == v.len()
}

/// A byte-determined, printable token view: numbers are a non-empty digit-led
/// self-rescanning run; keywords and symbols are always printable; `Ident`/`String`
/// need the deferred trust bridge.
pub open spec fn printable_tv(tv: TokenView) -> bool {
    match tv {
        TokenView::Number(v) => v.len() >= 1 && is_digit(v[0]) && rescans_num(v),
        TokenView::Ident(_) => false,
        TokenView::String(_) => false,
        _ => true,
    }
}

/// The boundary a token's printed bytes need for an exact re-scan: numbers need a
/// number boundary, keywords a non-continuation byte, symbols the operator
/// boundary (vacuous for punctuation and two-char operators).
pub open spec fn token_tail_ok(tv: TokenView, tail: Seq<u8>) -> bool {
    match tv {
        TokenView::Number(_) => num_tail_ok(tail),
        TokenView::Keyword(_) => tail.len() == 0 || !is_ident_cont(tail[0]),
        _ => op_tail_ok(sym_token_of(tv), tail),
    }
}

/// Scan one whole token value: skip whitespace, then dispatch on the first byte
/// to the number / keyword / symbol scanner. `None` with a non-advancing (ident)
/// or non-symbol lead marks a class handled by a later brick.
pub open spec fn lscan_token(input: Seq<u8>, pos: int) -> (Option<TokenView>, int) {
    let p = skip_ws(input, pos);
    if 0 <= p < input.len() {
        let b = input[p];
        if is_digit(b) {
            lscan_num_full(input, p)
        } else if is_ident_start(b) {
            let r = lscan_keyword(input, p);
            match r.0 {
                Some(kw) => (Some(TokenView::Keyword(kw)), r.1),
                None => (None, r.1),
            }
        } else {
            let r = lscan_sym(input, p);
            match r.0 {
                Some(t) => (Some(token_view(t)), r.1),
                None => (None, r.1),
            }
        }
    } else {
        (None, p)
    }
}

/// Single-token roundtrip over every byte-determined token class (numbers,
/// keywords, all symbols): scanning a printable token's print, under its
/// boundary, recovers exactly that token and advances past it. Axiom-free.
pub proof fn lemma_lscan_token(tv: TokenView, tail: Seq<u8>)
    requires
        printable_tv(tv),
        token_tail_ok(tv, tail),
    ensures
        lscan_token(lex_print_tv(tv) + tail, 0) == (Some(tv), lex_print_tv(tv).len() as int),
{
    let bytes = lex_print_tv(tv);
    let input = bytes + tail;
    match tv {
        TokenView::Number(v) => {
            assert(bytes == v);
            assert(input[0] == v[0]);
            assert(!is_ws(input[0])) by { assert(is_digit(v[0])); }
            assert(skip_ws(input, 0) == 0);
            assert(scan_num_full_end(input, 0) == v.len()) by {
                assert(rescans_num(v));
                assert(num_tail_ok(tail));
            }
            assert(input.subrange(0, v.len() as int) =~= v);
        }
        TokenView::Keyword(kw) => {
            assert(bytes == kw_text(kw));
            lemma_kw_text_shape(kw);
            assert(input[0] == kw_text(kw)[0]);
            assert(is_lower_letter(kw_text(kw)[0]));
            assert(!is_ws(input[0]));
            assert(!is_digit(input[0]));
            assert(is_ident_start(input[0]));
            assert(skip_ws(input, 0) == 0);
            lemma_lscan_keyword(kw, tail);
        }
        TokenView::Ident(_) => { assert(false); }
        TokenView::String(_) => { assert(false); }
        _ => {
            lemma_sym_token_props(tv);
            let t = sym_token_of(tv);
            assert(bytes == lex_print_sym(t));
            assert(input[0] == lex_print_sym(t)[0]);
            assert(!is_ws(input[0]));
            assert(!is_digit(input[0]));
            assert(!is_ident_start(input[0]));
            assert(skip_ws(input, 0) == 0);
            lemma_lscan_sym(t, tail);
        }
    }
}

/// Every token in the list is byte-determined and printable.
pub open spec fn all_printable_tv(ts: Seq<TokenView>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> printable_tv(#[trigger] ts[i])
}

/// Print a token list: each token's bytes followed by a single space separator.
pub open spec fn lex_print_list(ts: Seq<TokenView>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        lex_print_tv(ts[0]) + seq![32u8] + lex_print_list(ts.drop_first())
    }
}

/// Drop the leading whitespace run of a byte sequence (a seq slice at `skip_ws`).
pub open spec fn skip_ws_seq(input: Seq<u8>) -> Seq<u8> {
    input.subrange(skip_ws(input, 0), input.len() as int)
}

/// A printable byte-determined token prints to a non-empty run whose first byte
/// is never whitespace (so a preceding `skip_ws` lands exactly on it).
pub proof fn lemma_lex_print_tv_head(tv: TokenView)
    requires
        printable_tv(tv),
    ensures
        lex_print_tv(tv).len() >= 1,
        !is_ws(lex_print_tv(tv)[0]),
{
    match tv {
        TokenView::Number(v) => {
            assert(is_digit(v[0]));
        }
        TokenView::Keyword(kw) => {
            lemma_kw_text_shape(kw);
            assert(is_lower_letter(kw_text(kw)[0]));
        }
        TokenView::Ident(_) => { assert(false); }
        TokenView::String(_) => { assert(false); }
        _ => {
            lemma_sym_token_props(tv);
        }
    }
}

/// A single space is a valid tail boundary for every byte-determined token.
pub proof fn lemma_space_token_tail_ok(tv: TokenView, rest: Seq<u8>)
    requires
        printable_tv(tv),
    ensures
        token_tail_ok(tv, seq![32u8] + rest),
{
    let tail = seq![32u8] + rest;
    assert(tail[0] == 32);
    match tv {
        TokenView::Number(_) => {}
        TokenView::Keyword(_) => {}
        TokenView::Ident(_) => { assert(false); }
        TokenView::String(_) => { assert(false); }
        _ => {
            // op_tail_ok(sym_token_of(tv), tail): 32 extends no operator.
        }
    }
}

/// `skip_ws` shifted by a whitespace prefix byte: scanning `[c] ++ y` from `j+1`
/// is one past scanning `y` from `j`.
pub proof fn lemma_skip_ws_shift_ws(c: u8, y: Seq<u8>, j: int)
    requires
        is_ws(c),
        0 <= j <= y.len(),
    ensures
        skip_ws(seq![c] + y, j + 1) == 1 + skip_ws(y, j),
    decreases y.len() - j,
{
    let input = seq![c] + y;
    if j < y.len() {
        assert(input[j + 1] == y[j]);
        if is_ws(y[j]) {
            lemma_skip_ws_shift_ws(c, y, j + 1);
        }
    }
}

/// Stripping leading whitespace ignores a leading whitespace byte.
pub proof fn lemma_skip_ws_seq_prepend_ws(c: u8, y: Seq<u8>)
    requires
        is_ws(c),
    ensures
        skip_ws_seq(seq![c] + y) == skip_ws_seq(y),
{
    let input = seq![c] + y;
    assert(input[0] == c);
    lemma_skip_ws_shift_ws(c, y, 0);
    // skip_ws(input, 0) == skip_ws(input, 1) == 1 + skip_ws(y, 0)
    assert(skip_ws(input, 0) == 1 + skip_ws(y, 0));
    let a = skip_ws(y, 0);
    lemma_skip_ws_bounds(y, 0);
    assert(input.subrange(1 + a, input.len() as int) =~= y.subrange(a, y.len() as int));
}

/// Scan a whole input into a token list: strip leading whitespace, scan one
/// token at position 0, recurse on the remainder. `fuel` bounds the token count.
pub open spec fn lex_all_seq(input: Seq<u8>, fuel: nat) -> Seq<TokenView>
    decreases fuel,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        let stripped = skip_ws_seq(input);
        if stripped.len() == 0 {
            Seq::empty()
        } else {
            let r = lscan_token(stripped, 0);
            match r.0 {
                Some(tv) => seq![tv] + lex_all_seq(stripped.subrange(r.1, stripped.len() as int), (fuel - 1) as nat),
                None => Seq::empty(),
            }
        }
    }
}

/// `lex_all_seq` depends on its input only through `skip_ws_seq`.
pub proof fn lemma_lex_all_seq_congr(a: Seq<u8>, b: Seq<u8>, fuel: nat)
    requires
        skip_ws_seq(a) == skip_ws_seq(b),
    ensures
        lex_all_seq(a, fuel) == lex_all_seq(b, fuel),
{
    if fuel != 0 {
        assert(lex_all_seq(a, fuel) == lex_all_seq(b, fuel));
    }
}

/// Whole-input token-list roundtrip (byte-determined classes). Printing a
/// printable token list and re-lexing recovers it, given enough fuel.
#[verifier::reach_root]
pub proof fn lemma_lex_all_seq_roundtrip(ts: Seq<TokenView>, fuel: nat)
    requires
        all_printable_tv(ts),
        fuel >= ts.len(),
    ensures
        lex_all_seq(lex_print_list(ts), fuel) == ts,
    decreases ts.len(),
{
    if ts.len() == 0 {
        assert(lex_print_list(ts) =~= Seq::<u8>::empty());
        assert(skip_ws_seq(lex_print_list(ts)) =~= Seq::<u8>::empty());
    } else {
        let t = ts[0];
        let rest = ts.drop_first();
        assert(printable_tv(t));
        assert(all_printable_tv(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies printable_tv(#[trigger] rest[i]) by {
                assert(rest[i] == ts[i + 1]);
            }
        }
        let input = lex_print_list(ts);
        let tail = seq![32u8] + lex_print_list(rest);
        assert(input == lex_print_tv(t) + seq![32u8] + lex_print_list(rest));
        assert(input == lex_print_tv(t) + tail) by {
            assert((lex_print_tv(t) + seq![32u8]) + lex_print_list(rest)
                =~= lex_print_tv(t) + (seq![32u8] + lex_print_list(rest)));
        }
        lemma_lex_print_tv_head(t);
        // strip leading ws: none, so stripped == input
        assert(input[0] == lex_print_tv(t)[0]);
        assert(!is_ws(input[0]));
        lemma_skip_ws_nonws(input, 0);
        assert(skip_ws_seq(input) =~= input);
        // scan the first token
        lemma_space_token_tail_ok(t, lex_print_list(rest));
        lemma_lscan_token(t, tail);
        let e = lex_print_tv(t).len() as int;
        assert(lscan_token(input, 0) == (Some(t), e));
        // remainder is the space + printed rest
        assert(input.subrange(e, input.len() as int) =~= tail);
        // recurse: lex_all_seq(tail, fuel-1) == lex_all_seq(lex_print_list(rest), fuel-1)
        lemma_skip_ws_seq_prepend_ws(32u8, lex_print_list(rest));
        lemma_lex_all_seq_congr(tail, lex_print_list(rest), (fuel - 1) as nat);
        lemma_lex_all_seq_roundtrip(rest, (fuel - 1) as nat);
    }
}

/// Char seq -> bytes: each char truncated to its low byte (exact for ASCII).
pub open spec fn ascii_bytes(cs: Seq<char>) -> Seq<u8> {
    Seq::new(cs.len(), |i: int| cs[i] as u8)
}

/// Bytes -> char seq: each byte as a char.
pub open spec fn ascii_chars(bytes: Seq<u8>) -> Seq<char> {
    Seq::new(bytes.len(), |i: int| bytes[i] as char)
}

/// `char`->`u8`->`char` round-trips for ASCII (Verus proves the casts natively).
pub proof fn lemma_char_u8_char(c: char)
    requires
        (c as u32) < 128,
    ensures
        (c as u8) as char == c,
{
}

/// An ASCII char's `u8` cast preserves its value.
pub proof fn lemma_char_u8_val(c: char)
    requires
        (c as u32) < 128,
    ensures
        (c as u8) as u32 == (c as u32),
{
}

/// Every char is ASCII (fits in one byte).
pub open spec fn all_ascii_chars(cs: Seq<char>) -> bool {
    forall|i: int| 0 <= i < cs.len() ==> (cs[i] as u32) < 128
}

/// Every byte is ASCII.
pub open spec fn all_ascii_bytes(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len() ==> (#[trigger] bytes[i]) < 128
}

/// ASCII char seq re-encodes exactly: decoding its bytes recovers it.
pub proof fn lemma_ascii_chars_bytes(cs: Seq<char>)
    requires
        all_ascii_chars(cs),
    ensures
        ascii_chars(ascii_bytes(cs)) == cs,
{
    assert forall|i: int| 0 <= i < cs.len() implies ascii_chars(ascii_bytes(cs))[i] == cs[i] by {
        let c = cs[i];
        assert((c as u32) < 128);
        lemma_char_u8_char(c);
        assert(ascii_bytes(cs)[i] == (c as u8));
    }
    assert(ascii_chars(ascii_bytes(cs)) =~= cs);
}

/// Every char is a lowercase ASCII letter.
pub open spec fn all_lower_letter_chars(cs: Seq<char>) -> bool {
    forall|i: int| 0 <= i < cs.len() ==> 97 <= (#[trigger] cs[i]) as u32 <= 122
}

/// Scan an identifier, producing its lowercased char-sequence view — or `None`
/// when the run classifies as a keyword (handled by `lscan_keyword`) or there is
/// no identifier at `pos`.
pub open spec fn lscan_ident_m(input: Seq<u8>, pos: int) -> (Option<Seq<char>>, int) {
    if 0 <= pos < input.len() && is_ident_start(input[pos]) {
        let e = scan_ident_end(input, pos);
        let low = ascii_lower_seq(input.subrange(pos, e));
        if classify_kw(low) is None {
            (Some(ascii_chars(low)), e)
        } else {
            (None, e)
        }
    } else {
        (None, pos)
    }
}

/// A lowercase-letter char run is all lowercase-letter bytes once encoded.
pub proof fn lemma_ident_bytes_lower(cs: Seq<char>)
    requires
        all_lower_letter_chars(cs),
    ensures
        all_lower_letters(ascii_bytes(cs)),
        all_ascii_bytes(ascii_bytes(cs)),
{
    assert forall|i: int| 0 <= i < ascii_bytes(cs).len() implies
        is_lower_letter(#[trigger] ascii_bytes(cs)[i]) && ascii_bytes(cs)[i] < 128 by {
        let c = cs[i];
        assert(97 <= (c as u32) <= 122);
        lemma_char_u8_val(c);
        assert(ascii_bytes(cs)[i] == (c as u8));
        assert(97 <= (c as u8) <= 122);
    }
}

/// Identifier roundtrip at the char-view level: printing a non-empty
/// lowercase-letter char run that is not a keyword, then re-scanning under a
/// non-continuation boundary, recovers exactly that char sequence. Axiom-free.
pub proof fn lemma_lscan_ident_m(cs: Seq<char>, tail: Seq<u8>)
    requires
        cs.len() >= 1,
        all_lower_letter_chars(cs),
        classify_kw(ascii_bytes(cs)) is None,
        tail.len() == 0 || !is_ident_cont(tail[0]),
    ensures
        lscan_ident_m(ascii_bytes(cs) + tail, 0) == (Some(cs), cs.len() as int),
{
    let d = ascii_bytes(cs);
    let input = d + tail;
    lemma_ident_bytes_lower(cs);
    // d is a well-formed identifier byte run
    lemma_lower_letters_ident_bytes(d);
    assert(input[0] == d[0]);
    assert(is_ident_start(input[0]));
    lemma_scan_ident_roundtrip(d, tail);
    assert(scan_ident_end(input, 0) == d.len());
    assert(input.subrange(0, d.len() as int) =~= d);
    // lowercasing the (already lowercase) run is the identity
    lemma_ascii_lower_idem(d);
    assert(ascii_lower_seq(d) == d);
    // classify is None ⟹ Ident arm; its char view is cs
    lemma_ascii_chars_bytes(cs);
    assert(ascii_chars(d) == cs);
}

/// First index at or after `pos` holding a quote byte `'` (39), or end of input.
pub open spec fn scan_to_quote(input: Seq<u8>, pos: int) -> int
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && input[pos] != 39 {
        scan_to_quote(input, pos + 1)
    } else {
        pos
    }
}

/// Maximal-run characterization for `scan_to_quote` (mirrors the digit/ident runs).
pub proof fn lemma_scan_to_quote_run(input: Seq<u8>, pos: int, k: int)
    requires
        0 <= pos <= k <= input.len(),
        forall|i: int| pos <= i < k ==> input[i] != 39,
        k == input.len() || input[k] == 39,
    ensures
        scan_to_quote(input, pos) == k,
    decreases k - pos,
{
    if pos < k {
        lemma_scan_to_quote_run(input, pos + 1, k);
    }
}

/// Scan a quoted string, producing its char-sequence view. `None` if there is no
/// opening quote or the string is unterminated.
pub open spec fn lscan_string_m(input: Seq<u8>, pos: int) -> (Option<Seq<char>>, int) {
    if 0 <= pos < input.len() && input[pos] == 39 {
        let close = scan_to_quote(input, pos + 1);
        if close < input.len() {
            (Some(ascii_chars(input.subrange(pos + 1, close))), close + 1)
        } else {
            (None, pos)
        }
    } else {
        (None, pos)
    }
}

/// A no-quote ASCII char run encodes to bytes with no quote byte.
pub proof fn lemma_string_bytes_noquote(cs: Seq<char>)
    requires
        all_ascii_chars(cs),
        forall|i: int| 0 <= i < cs.len() ==> (#[trigger] cs[i]) as u32 != 39,
    ensures
        all_ascii_bytes(ascii_bytes(cs)),
        forall|i: int| 0 <= i < ascii_bytes(cs).len() ==> (#[trigger] ascii_bytes(cs)[i]) != 39,
{
    assert forall|i: int| 0 <= i < ascii_bytes(cs).len() implies
        ascii_bytes(cs)[i] < 128 && ascii_bytes(cs)[i] != 39 by {
        let c = cs[i];
        assert((c as u32) < 128);
        assert((c as u32) != 39);
        lemma_char_u8_val(c);
        assert(ascii_bytes(cs)[i] == (c as u8));
    }
}

/// Quoted-string roundtrip at the char-view level: printing `'` + a quote-free
/// ASCII char run + `'` and re-scanning recovers exactly that char sequence
/// (self-delimiting, so any tail follows). Axiom-free.
pub proof fn lemma_lscan_string_m(cs: Seq<char>, tail: Seq<u8>)
    requires
        all_ascii_chars(cs),
        forall|i: int| 0 <= i < cs.len() ==> (#[trigger] cs[i]) as u32 != 39,
    ensures
        lscan_string_m(seq![39u8] + ascii_bytes(cs) + seq![39u8] + tail, 0)
            == (Some(cs), (cs.len() + 2) as int),
{
    let q = seq![39u8];
    let d = ascii_bytes(cs);
    let input = q + d + q + tail;
    lemma_string_bytes_noquote(cs);
    assert(input[0] == 39);
    // inner run [1, 1+d.len()) has no quote, closing quote at 1+d.len()
    assert forall|i: int| 1 <= i < 1 + d.len() implies input[i] != 39 by {
        assert(input[i] == d[i - 1]);
    }
    let close = (1 + d.len()) as int;
    assert(input[close] == 39) by {
        assert(input[close] == q[0]);
    }
    lemma_scan_to_quote_run(input, 1, close);
    assert(scan_to_quote(input, 1) == close);
    assert(close < input.len());
    assert(input.subrange(1, close) =~= d);
    lemma_ascii_chars_bytes(cs);
    assert(ascii_chars(d) == cs);
}

/// Spec mirror of a production `Token`: `String` payloads become their char view.
pub enum MTok {
    MNum(Seq<u8>),
    MKw(Keyword),
    MIdent(Seq<char>),
    MString(Seq<char>),
    MSym(TokenView),
}

/// Unified single-token dispatcher over all five classes, producing an `MTok`.
pub open spec fn lscan_mtok(input: Seq<u8>, pos: int) -> (Option<MTok>, int) {
    let p = skip_ws(input, pos);
    if 0 <= p < input.len() {
        let b = input[p];
        if b == 39 {
            let r = lscan_string_m(input, p);
            match r.0 {
                Some(cv) => (Some(MTok::MString(cv)), r.1),
                None => (None, r.1),
            }
        } else if is_digit(b) {
            let r = lscan_num_full(input, p);
            match r.0 {
                Some(TokenView::Number(v)) => (Some(MTok::MNum(v)), r.1),
                _ => (None, r.1),
            }
        } else if is_ident_start(b) {
            let rk = lscan_keyword(input, p);
            match rk.0 {
                Some(kw) => (Some(MTok::MKw(kw)), rk.1),
                None => {
                    let ri = lscan_ident_m(input, p);
                    match ri.0 {
                        Some(cv) => (Some(MTok::MIdent(cv)), ri.1),
                        None => (None, ri.1),
                    }
                }
            }
        } else {
            let r = lscan_sym(input, p);
            match r.0 {
                Some(t) => (Some(MTok::MSym(token_view(t))), r.1),
                None => (None, r.1),
            }
        }
    } else {
        (None, p)
    }
}

/// Canonical byte print of a mirror token.
pub open spec fn mprint(mt: MTok) -> Seq<u8> {
    match mt {
        MTok::MNum(v) => v,
        MTok::MKw(kw) => kw_text(kw),
        MTok::MIdent(cs) => ascii_bytes(cs),
        MTok::MString(cs) => seq![39u8] + ascii_bytes(cs) + seq![39u8],
        MTok::MSym(tv) => lex_print_sym(sym_token_of(tv)),
    }
}

/// A printable mirror token: each class's re-scan precondition.
pub open spec fn printable_mtok(mt: MTok) -> bool {
    match mt {
        MTok::MNum(v) => v.len() >= 1 && is_digit(v[0]) && rescans_num(v),
        MTok::MKw(_) => true,
        MTok::MIdent(cs) => cs.len() >= 1 && all_lower_letter_chars(cs)
            && classify_kw(ascii_bytes(cs)) is None,
        MTok::MString(cs) => all_ascii_chars(cs)
            && (forall|i: int| 0 <= i < cs.len() ==> (#[trigger] cs[i]) as u32 != 39),
        MTok::MSym(tv) => is_sym_view(tv),
    }
}

/// The tail boundary each mirror token needs (strings are self-delimiting).
pub open spec fn tail_ok_mtok(mt: MTok, tail: Seq<u8>) -> bool {
    match mt {
        MTok::MNum(_) => num_tail_ok(tail),
        MTok::MKw(_) => tail.len() == 0 || !is_ident_cont(tail[0]),
        MTok::MIdent(_) => tail.len() == 0 || !is_ident_cont(tail[0]),
        MTok::MString(_) => true,
        MTok::MSym(tv) => op_tail_ok(sym_token_of(tv), tail),
    }
}

/// Unified single-token roundtrip over all five classes. Axiom-free.
pub proof fn lemma_lscan_mtok(mt: MTok, tail: Seq<u8>)
    requires
        printable_mtok(mt),
        tail_ok_mtok(mt, tail),
    ensures
        lscan_mtok(mprint(mt) + tail, 0) == (Some(mt), mprint(mt).len() as int),
{
    let input = mprint(mt) + tail;
    match mt {
        MTok::MNum(v) => {
            assert(mprint(mt) == v);
            assert(input[0] == v[0]);
            assert(is_digit(input[0]));
            assert(!is_ws(input[0]));
            assert(skip_ws(input, 0) == 0);
            assert(input[0] != 39);
            // number arm
            assert(rescans_num(v));
            assert(num_tail_ok(tail));
            assert(scan_num_full_end(input, 0) == v.len());
            assert(input.subrange(0, v.len() as int) =~= v);
        }
        MTok::MKw(kw) => {
            lemma_kw_text_shape(kw);
            assert(mprint(mt) == kw_text(kw));
            assert(input[0] == kw_text(kw)[0]);
            assert(is_lower_letter(kw_text(kw)[0]));
            assert(!is_ws(input[0]) && !is_digit(input[0]) && is_ident_start(input[0]));
            assert(input[0] != 39);
            assert(skip_ws(input, 0) == 0);
            lemma_lscan_keyword(kw, tail);
        }
        MTok::MIdent(cs) => {
            lemma_ident_bytes_lower(cs);
            assert(mprint(mt) == ascii_bytes(cs));
            assert(cs.len() >= 1);
            assert(ascii_bytes(cs).len() == cs.len());
            assert(input[0] == ascii_bytes(cs)[0]);
            assert(is_lower_letter(ascii_bytes(cs)[0]));
            assert(is_ident_start(input[0]) && !is_digit(input[0]) && !is_ws(input[0]));
            assert(input[0] != 39);
            assert(skip_ws(input, 0) == 0);
            // keyword arm returns None (cs not a keyword), then ident arm
            lemma_ascii_lower_idem(ascii_bytes(cs));
            lemma_lower_letters_ident_bytes(ascii_bytes(cs));
            lemma_scan_ident_roundtrip(ascii_bytes(cs), tail);
            assert(input.subrange(0, ascii_bytes(cs).len() as int) =~= ascii_bytes(cs));
            assert(classify_kw(ascii_lower_seq(input.subrange(0, scan_ident_end(input, 0)))) is None);
            lemma_lscan_ident_m(cs, tail);
        }
        MTok::MString(cs) => {
            assert(mprint(mt) == seq![39u8] + ascii_bytes(cs) + seq![39u8]);
            assert(input == seq![39u8] + ascii_bytes(cs) + seq![39u8] + tail) by {
                assert((seq![39u8] + ascii_bytes(cs) + seq![39u8]) + tail
                    =~= seq![39u8] + ascii_bytes(cs) + seq![39u8] + tail);
            }
            assert(input[0] == 39);
            assert(!is_ws(input[0]));
            assert(skip_ws(input, 0) == 0);
            lemma_lscan_string_m(cs, tail);
        }
        MTok::MSym(tv) => {
            lemma_sym_token_props(tv);
            let t = sym_token_of(tv);
            assert(mprint(mt) == lex_print_sym(t));
            assert(input[0] == lex_print_sym(t)[0]);
            assert(!is_ws(input[0]) && !is_digit(input[0]) && !is_ident_start(input[0]));
            assert(input[0] != 39);
            assert(skip_ws(input, 0) == 0);
            lemma_lscan_sym(t, tail);
        }
    }
}

/// Every mirror token in the list is printable.
pub open spec fn all_printable_mtok(ms: Seq<MTok>) -> bool {
    forall|i: int| 0 <= i < ms.len() ==> printable_mtok(#[trigger] ms[i])
}

/// Print a mirror-token list: each token's bytes then a single space separator.
pub open spec fn mprint_list(ms: Seq<MTok>) -> Seq<u8>
    decreases ms.len(),
{
    if ms.len() == 0 {
        Seq::empty()
    } else {
        mprint(ms[0]) + seq![32u8] + mprint_list(ms.drop_first())
    }
}

/// A printable mirror token prints to a non-empty run with a non-whitespace head.
pub proof fn lemma_mprint_head(mt: MTok)
    requires
        printable_mtok(mt),
    ensures
        mprint(mt).len() >= 1,
        !is_ws(mprint(mt)[0]),
{
    match mt {
        MTok::MNum(v) => { assert(is_digit(v[0])); }
        MTok::MKw(kw) => {
            lemma_kw_text_shape(kw);
            assert(is_lower_letter(kw_text(kw)[0]));
        }
        MTok::MIdent(cs) => {
            lemma_ident_bytes_lower(cs);
            assert(mprint(mt).len() == cs.len());
            assert(is_lower_letter(ascii_bytes(cs)[0]));
        }
        MTok::MString(cs) => {
            assert(mprint(mt)[0] == 39);
        }
        MTok::MSym(tv) => { lemma_sym_token_props(tv); }
    }
}

/// A single space is a valid tail boundary for every printable mirror token.
pub proof fn lemma_space_tail_ok_mtok(mt: MTok, rest: Seq<u8>)
    requires
        printable_mtok(mt),
    ensures
        tail_ok_mtok(mt, seq![32u8] + rest),
{
    let tail = seq![32u8] + rest;
    assert(tail[0] == 32);
}

/// Whole-input scanner over MTok: strip leading whitespace, scan one token at 0,
/// recurse on the remainder.
pub open spec fn lex_mtok_seq(input: Seq<u8>, fuel: nat) -> Seq<MTok>
    decreases fuel,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        let stripped = skip_ws_seq(input);
        if stripped.len() == 0 {
            Seq::empty()
        } else {
            let r = lscan_mtok(stripped, 0);
            match r.0 {
                Some(mt) => seq![mt] + lex_mtok_seq(stripped.subrange(r.1, stripped.len() as int), (fuel - 1) as nat),
                None => Seq::empty(),
            }
        }
    }
}

/// `lex_mtok_seq` depends on its input only through `skip_ws_seq`.
pub proof fn lemma_lex_mtok_seq_congr(a: Seq<u8>, b: Seq<u8>, fuel: nat)
    requires
        skip_ws_seq(a) == skip_ws_seq(b),
    ensures
        lex_mtok_seq(a, fuel) == lex_mtok_seq(b, fuel),
{
    if fuel != 0 {
        assert(lex_mtok_seq(a, fuel) == lex_mtok_seq(b, fuel));
    }
}

/// Whole-input unified token-list roundtrip (all five classes). Axiom-free.
#[verifier::reach_root]
pub proof fn lemma_lex_mtok_seq_roundtrip(ms: Seq<MTok>, fuel: nat)
    requires
        all_printable_mtok(ms),
        fuel >= ms.len(),
    ensures
        lex_mtok_seq(mprint_list(ms), fuel) == ms,
    decreases ms.len(),
{
    if ms.len() == 0 {
        assert(mprint_list(ms) =~= Seq::<u8>::empty());
        assert(skip_ws_seq(mprint_list(ms)) =~= Seq::<u8>::empty());
    } else {
        let mt = ms[0];
        let rest = ms.drop_first();
        assert(printable_mtok(mt));
        assert(all_printable_mtok(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies printable_mtok(#[trigger] rest[i]) by {
                assert(rest[i] == ms[i + 1]);
            }
        }
        let input = mprint_list(ms);
        let tail = seq![32u8] + mprint_list(rest);
        assert(input == mprint(mt) + seq![32u8] + mprint_list(rest));
        assert(input == mprint(mt) + tail) by {
            assert((mprint(mt) + seq![32u8]) + mprint_list(rest)
                =~= mprint(mt) + (seq![32u8] + mprint_list(rest)));
        }
        lemma_mprint_head(mt);
        assert(input[0] == mprint(mt)[0]);
        assert(!is_ws(input[0]));
        lemma_skip_ws_nonws(input, 0);
        assert(skip_ws_seq(input) =~= input);
        lemma_space_tail_ok_mtok(mt, mprint_list(rest));
        lemma_lscan_mtok(mt, tail);
        let e = mprint(mt).len() as int;
        assert(lscan_mtok(input, 0) == (Some(mt), e));
        assert(input.subrange(e, input.len() as int) =~= tail);
        lemma_skip_ws_seq_prepend_ws(32u8, mprint_list(rest));
        lemma_lex_mtok_seq_congr(tail, mprint_list(rest), (fuel - 1) as nat);
        lemma_lex_mtok_seq_roundtrip(rest, (fuel - 1) as nat);
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
