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

// -- L2: whitespace skipping --------------------------------------------------
//
// The lexer skips ASCII whitespace before each token. `skip_ws` advances the
// cursor past a maximal run of whitespace bytes; the token scanners run at the
// returned position. This is the first piece of the inter-token machinery the
// whole-input token-list roundtrip will need.

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

/// `skip_ws` lands on end-of-input or a non-whitespace byte (its defining
/// fixpoint): the token scanner that runs there never faces leading whitespace.
pub proof fn lemma_skip_ws_fixpoint(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        skip_ws(input, pos) == input.len()
            || !is_ws(input[skip_ws(input, pos)]),
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_ws(input[pos]) {
        lemma_skip_ws_fixpoint(input, pos + 1);
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

/// Executable whitespace skip, refining `skip_ws`.
pub fn skip_ws_exec(input: &Vec<u8>, pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        r == skip_ws(input@, pos as int),
    decreases input.len() - pos,
{
    if pos < input.len() {
        let b = input[pos];
        if b == 32u8 || b == 9u8 || b == 10u8 || b == 13u8 {
            skip_ws_exec(input, pos + 1)
        } else {
            pos
        }
    } else {
        pos
    }
}

// -- L3: number scanning (integer core) ---------------------------------------
//
// `Number` is the first token with a payload. The production `scan_number_bytes`
// (in `lexer.rs`, already verified) consumes digits then an optional `.`-fraction
// and `e`-exponent, storing the raw bytes. This brick proves the spec-level
// roundtrip for the integer core: a maximal digit run re-scans to exactly itself,
// given the following byte does not continue the run. Decimal/exponent extension
// is deferred to a later brick; the boundary reasoning is identical to L1.

/// ASCII digit `0`-`9`.
pub open spec fn is_digit(b: u8) -> bool {
    48 <= b <= 57
}

/// Every byte of the sequence is a digit.
pub open spec fn all_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i])
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

/// Integer roundtrip: a non-empty digit run followed by a non-digit boundary byte
/// (or end) re-scans to exactly itself. This is the number analogue of L1's
/// maximal-munch boundary — the tail must not start with a byte that extends the
/// run (here, another digit; decimal/exponent bytes are the deferred extension).
pub proof fn lemma_scan_digits_roundtrip(d: Seq<u8>, tail: Seq<u8>)
    requires
        d.len() >= 1,
        all_digits(d),
        tail.len() == 0 || !is_digit(tail[0]),
    ensures
        scan_digits_end(d + tail, 0) == d.len(),
{
    let input = d + tail;
    assert forall|i: int| 0 <= i < d.len() implies is_digit(#[trigger] input[i]) by {
        assert(input[i] == d[i]);
    }
    if tail.len() == 0 {
        assert(input.len() == d.len());
    } else {
        assert(input[d.len() as int] == tail[0]);
    }
    lemma_scan_digits_end_run(input, 0, d.len() as int);
}

/// Executable maximal digit-run scanner, refining `scan_digits_end`.
pub fn scan_digits_exec(input: &Vec<u8>, pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        r == scan_digits_end(input@, pos as int),
    decreases input.len() - pos,
{
    if pos < input.len() {
        let b = input[pos];
        if 48u8 <= b && b <= 57u8 {
            scan_digits_exec(input, pos + 1)
        } else {
            pos
        }
    } else {
        pos
    }
}

// -- L4: identifier scanning (unquoted char-run) ------------------------------
//
// An unquoted identifier is `[A-Za-z_][A-Za-z0-9_]*`. The production lexer then
// lowercases it and classifies it as a keyword if it matches the keyword table;
// that canonicalisation (lowercasing, keyword lookup) is a later brick. This
// brick proves the char-run core: a maximal identifier run re-scans to itself
// under an identifier-continuation boundary — the same shape as L3.

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

/// Executable maximal identifier-run scanner, refining `scan_ident_end`.
pub fn scan_ident_exec(input: &Vec<u8>, pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        r == scan_ident_end(input@, pos as int),
    decreases input.len() - pos,
{
    if pos < input.len() {
        let b = input[pos];
        let cont = ((65u8 <= b && b <= 90u8) || (97u8 <= b && b <= 122u8) || b == 95u8)
            || (48u8 <= b && b <= 57u8);
        if cont {
            scan_ident_exec(input, pos + 1)
        } else {
            pos
        }
    } else {
        pos
    }
}

// -- L5: single-token dispatcher ----------------------------------------------
//
// Composes L0-L4: skip whitespace, then dispatch on the first byte to the right
// scanner and return the end position of that one token. This is the backbone of
// the whole-input token-list scanner (repeatedly apply until end). Deferred token
// classes (strings, quoted identifiers, comments) yield "no advance" for now, so
// the dispatcher is total but not yet complete — later bricks fill those arms.

/// Monotonicity/bounds for the digit run (needed to show the dispatcher advances).
pub proof fn lemma_scan_digits_end_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        pos <= scan_digits_end(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_digit(input[pos]) {
        lemma_scan_digits_end_bounds(input, pos + 1);
    }
}

/// Monotonicity/bounds for the identifier run.
pub proof fn lemma_scan_ident_end_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        pos <= scan_ident_end(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && is_ident_cont(input[pos]) {
        lemma_scan_ident_end_bounds(input, pos + 1);
    }
}

/// A byte that begins a token the dispatcher currently recognizes: digit
/// (number), ident-start (identifier), operator lead (`< > !`), or munch-free
/// punctuation. Excludes the deferred classes (`'`/`"` strings and quoted idents,
/// `-`-comment lead handling, etc. — later bricks).
pub open spec fn is_token_start(b: u8) -> bool {
    is_digit(b) || is_ident_start(b) || b == 60 || b == 62 || b == 33
        || scan_punct1(b) is Some
}

/// End position of the one token starting at `pos` (after skipping whitespace).
/// Returns `skip_ws(pos)` unchanged when there is no recognized token there.
pub open spec fn lex_token_end(input: Seq<u8>, pos: int) -> int {
    let p = skip_ws(input, pos);
    if 0 <= p < input.len() {
        let b = input[p];
        if is_digit(b) {
            scan_digits_end(input, p)
        } else if is_ident_start(b) {
            scan_ident_end(input, p)
        } else if b == 60 || b == 62 || b == 33 {
            lscan_op(input, p).1
        } else if scan_punct1(b) is Some {
            p + 1
        } else {
            p
        }
    } else {
        p
    }
}

/// The dispatcher never moves before the whitespace-skipped cursor and never past
/// the end.
pub proof fn lemma_lex_token_end_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        skip_ws(input, pos) <= lex_token_end(input, pos) <= input.len(),
{
    let p = skip_ws(input, pos);
    lemma_skip_ws_bounds(input, pos);
    if 0 <= p < input.len() {
        let b = input[p];
        if is_digit(b) {
            lemma_scan_digits_end_bounds(input, p);
        } else if is_ident_start(b) {
            lemma_scan_ident_end_bounds(input, p);
        }
    }
}

/// When a recognized token starts at the whitespace-skipped cursor, the dispatcher
/// strictly advances — the progress fact the token-list scanner needs to terminate.
pub proof fn lemma_lex_token_end_progress(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
        skip_ws(input, pos) < input.len(),
        is_token_start(input[skip_ws(input, pos)]),
    ensures
        skip_ws(input, pos) < lex_token_end(input, pos),
{
    lemma_skip_ws_bounds(input, pos);
    let p = skip_ws(input, pos);
    let b = input[p];
    if is_digit(b) {
        assert(lex_token_end(input, pos) == scan_digits_end(input, p));
        reveal_with_fuel(scan_digits_end, 1);
        assert(scan_digits_end(input, p) == scan_digits_end(input, p + 1));
        lemma_scan_digits_end_bounds(input, p + 1);
    } else if is_ident_start(b) {
        assert(lex_token_end(input, pos) == scan_ident_end(input, p));
        assert(is_ident_cont(b));
        reveal_with_fuel(scan_ident_end, 1);
        assert(scan_ident_end(input, p) == scan_ident_end(input, p + 1));
        lemma_scan_ident_end_bounds(input, p + 1);
    } else if b == 60 || b == 62 || b == 33 {
        // lscan_op advances by 1 or 2 (its second component is p+1 or p+2).
        assert(lex_token_end(input, pos) == lscan_op(input, p).1);
        assert(lscan_op(input, p).1 >= p + 1);
    } else {
        // munch-free punctuation: p + 1.
        assert(scan_punct1(b) is Some);
        assert(lex_token_end(input, pos) == p + 1);
    }
}

// -- L6: executable dispatcher + spec token-list scanner ----------------------
//
// `lex_token_end_exec` is the runnable dispatcher (composes the L0-L5 exec
// scanners), refining `lex_token_end`. `lex_all_ends` is the spec-level
// whole-input scanner: the strictly-increasing sequence of token end positions,
// fuel-bounded (like the parser's `sparse`, to sidestep proving termination
// through the L5 progress lemma inside a spec fn).

/// Executable "extent of the next token" — skip whitespace, dispatch on the first
/// byte, return the token's end position. Refines `lex_token_end` exactly.
pub fn lex_token_end_exec(input: &Vec<u8>, pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        r == lex_token_end(input@, pos as int),
{
    let p = skip_ws_exec(input, pos);
    proof { lemma_skip_ws_bounds(input@, pos as int); }
    if p < input.len() {
        let b = input[p];
        if 48u8 <= b && b <= 57u8 {
            scan_digits_exec(input, p)
        } else if (65u8 <= b && b <= 90u8) || (97u8 <= b && b <= 122u8) || b == 95u8 {
            scan_ident_exec(input, p)
        } else if b == 60u8 || b == 62u8 || b == 33u8 {
            let (_t, e) = scan_op_exec(input, p);
            e
        } else {
            let (t, e) = scan_punct1_exec(input, p);
            match t {
                Some(_) => e,
                None => p,
            }
        }
    } else {
        p
    }
}

/// Spec whole-input token-list scanner: the sequence of token end positions from
/// `pos`, stopping at end-of-input or an unrecognized (deferred-class) byte.
/// `fuel` bounds the recursion; a fuel of `input.len() + 1` always suffices.
pub open spec fn lex_all_ends(input: Seq<u8>, pos: int, fuel: nat) -> Seq<int>
    decreases fuel,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        let e = lex_token_end(input, pos);
        if e > pos {
            seq![e] + lex_all_ends(input, e, (fuel - 1) as nat)
        } else {
            Seq::empty()
        }
    }
}

/// Every token end position is strictly past the start and within the input:
/// `pos < ends[i] <= len`. The well-formedness the token-list refinement builds on.
pub proof fn lemma_lex_all_ends_bounded(input: Seq<u8>, pos: int, fuel: nat)
    requires
        0 <= pos <= input.len(),
    ensures
        forall|i: int| 0 <= i < lex_all_ends(input, pos, fuel).len()
            ==> pos < #[trigger] lex_all_ends(input, pos, fuel)[i] <= input.len(),
    decreases fuel,
{
    if fuel > 0 {
        let e = lex_token_end(input, pos);
        lemma_lex_token_end_bounds(input, pos);
        if e > pos {
            lemma_lex_all_ends_bounded(input, e, (fuel - 1) as nat);
            let rest = lex_all_ends(input, e, (fuel - 1) as nat);
            assert forall|i: int| 0 <= i < lex_all_ends(input, pos, fuel).len()
                implies pos < #[trigger] lex_all_ends(input, pos, fuel)[i] <= input.len() by {
                if i == 0 {
                    assert(lex_all_ends(input, pos, fuel)[0] == e);
                } else {
                    assert(lex_all_ends(input, pos, fuel)[i] == rest[i - 1]);
                    // rest entries are > e > pos and <= len.
                }
            }
        }
    }
}

// -- L7: token-list fuel stability --------------------------------------------
//
// Each token consumes at least one position, so `lex_all_ends` reaches its fixed
// result once `fuel >= input.len() - pos`; extra fuel changes nothing. This is
// what lets a fuel-free executable token-list loop (a later brick) refine the
// fuel-bounded spec — the same move the parser made from `sparse` to its exec.

pub proof fn lemma_lex_all_ends_fuel_stable(input: Seq<u8>, pos: int, fuel: nat)
    requires
        0 <= pos <= input.len(),
        fuel >= input.len() - pos,
    ensures
        lex_all_ends(input, pos, fuel) == lex_all_ends(input, pos, (fuel + 1) as nat),
    decreases input.len() - pos,
{
    let e = lex_token_end(input, pos);
    lemma_lex_token_end_bounds(input, pos);
    lemma_skip_ws_bounds(input, pos);
    if e > pos {
        // A token was consumed: e >= pos + 1, so the tail has strictly less to do
        // and still enough fuel. fuel > 0 here since fuel >= len - pos >= e - pos >= 1.
        assert(fuel >= input.len() - pos);
        assert(e <= input.len());
        assert(fuel - 1 >= input.len() - e);
        lemma_lex_all_ends_fuel_stable(input, e, (fuel - 1) as nat);
        assert(lex_all_ends(input, pos, fuel)
            == seq![e] + lex_all_ends(input, e, (fuel - 1) as nat));
        assert(lex_all_ends(input, pos, (fuel + 1) as nat)
            == seq![e] + lex_all_ends(input, e, fuel));
    } else {
        // No progress (end of input or a deferred-class byte): both are empty.
        // fuel could be 0 only if len - pos <= 0, i.e. pos == len, where e == pos.
        assert(lex_all_ends(input, pos, (fuel + 1) as nat) =~= Seq::<int>::empty());
        assert(lex_all_ends(input, pos, fuel) =~= Seq::<int>::empty());
    }
}

} // verus!
