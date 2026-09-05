//! Token-level lexer model.
//!
//! Provides a ghost/spec model of tokenization so the grammar layer
//! (`verified_stmt` etc.) can reason over a clean `Token` stream. Every theorem
//! here is stated at the token level.
//!
//! Limit: this model is NOT wired to the production `Lexer`. The only lexer code
//! that actually runs verified is `scan_symbol_bytes` (here) and
//! `scan_number_bytes` (in `lexer.rs`); the rest of the string -> token stage in
//! the production lexer is essentially unverified plain Rust.

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

//

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


pub open spec fn ends_int(v: Seq<usize>) -> Seq<int> {
    v.map_values(|x: usize| x as int)
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

/// Scan a number (integer core): if the byte at `pos` is a digit, consume the
/// maximal digit run and produce `Number` carrying those bytes.
pub open spec fn lscan_num(input: Seq<u8>, pos: int) -> (Option<TokenView>, int) {
    if 0 <= pos < input.len() && is_digit(input[pos]) {
        let e = scan_digits_end(input, pos);
        (Some(TokenView::Number(input.subrange(pos, e))), e)
    } else {
        (None, pos)
    }
}

/// Number token roundtrip: a non-empty digit run followed by a non-digit boundary
/// scans to `Number` carrying exactly those bytes, advancing past them. The
/// token-value analogue of `lemma_scan_digits_roundtrip`.
pub proof fn lemma_lscan_num(d: Seq<u8>, tail: Seq<u8>)
    requires
        d.len() >= 1,
        all_digits(d),
        tail.len() == 0 || !is_digit(tail[0]),
    ensures
        lscan_num(d + tail, 0) == (Some(TokenView::Number(d)), d.len() as int),
{
    let input = d + tail;
    assert(input[0] == d[0]);
    assert(is_digit(input[0]));
    lemma_scan_digits_roundtrip(d, tail);
    assert(scan_digits_end(input, 0) == d.len());
    assert(input.subrange(0, d.len() as int) =~= d);
}

// -- L11: decimal number extension (digits.digits) ----------------------------
//
// Extends L3/L10 past the integer core to `digits.digits`. This is the first
// multi-phase scan (integer run, then a `.`, then a fraction run) and its
// roundtrip needs two applications of the run characterization with concatenation
// index bookkeeping. Exponent (`e[+-]digits`) is the next phase, deferred.

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

/// Decimal roundtrip: an integer run `a`, a `.`, and a fraction run `b`, followed
/// by a non-digit boundary, scan to exactly `a.b` (length `|a| + 1 + |b|`). `.` in
/// the tail is harmless (only one `.` is consumed).
pub proof fn lemma_scan_num_dec_roundtrip(a: Seq<u8>, b: Seq<u8>, tail: Seq<u8>)
    requires
        a.len() >= 1,
        all_digits(a),
        b.len() >= 1,
        all_digits(b),
        tail.len() == 0 || !is_digit(tail[0]),
    ensures
        scan_num_dec_end(a + seq![46u8] + b + tail, 0) == a.len() + 1 + b.len(),
{
    let dot = seq![46u8];
    let input = a + dot + b + tail;
    // Phase 1: the integer run stops at the `.` (index a.len()).
    assert forall|i: int| 0 <= i < a.len() implies is_digit(#[trigger] input[i]) by {
        assert(input[i] == a[i]);
    }
    assert(input[a.len() as int] == 46) by {
        assert(input[a.len() as int] == dot[0]);
    }
    lemma_scan_digits_end_run(input, 0, a.len() as int);
    assert(scan_digits_end(input, 0) == a.len());
    // Phase 2: from just past the `.`, the fraction run stops at the boundary.
    let f0: int = a.len() as int + 1;
    let fend: int = f0 + b.len() as int;
    assert forall|i: int| f0 <= i < fend implies is_digit(#[trigger] input[i]) by {
        assert(input[i] == b[i - f0]);
    }
    if tail.len() == 0 {
        assert(input.len() == fend);
    } else {
        assert(input[fend] == tail[0]);
    }
    lemma_scan_digits_end_run(input, f0, fend);
    assert(scan_digits_end(input, f0) == fend);
}

// -- L12: full number token-value scanner (integer[.decimal][exponent]) --------
//
// Completes the number scanner to the production shape `digits[.digits][(e|E)
// [+|-]digits]`, matching `lexer.rs::scan_number_bytes`'s cursor progression, and
// packages it as a `Number` token-value scanner. Rust's `Display` for `f64` never
// emits scientific notation, so the *printer* only ever produces the integer or
// `digits.digits` forms; the exponent phase is therefore not needed for the
// roundtrip, only to lex arbitrary production input faithfully. Accordingly the
// two roundtrip lemmas below cover exactly the printed forms (integer, decimal),
// under one unified number boundary predicate `num_tail_ok`.

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

/// Bounds: the full number scan advances at least past the first digit and stays
/// in range (given the start is a digit).
pub proof fn lemma_scan_num_full_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos < input.len(),
        is_digit(input[pos]),
    ensures
        pos < scan_num_full_end(input, pos) <= input.len(),
{
    // First byte is a digit, so the integer run advances at least one past `pos`.
    assert(scan_digits_end(input, pos) == scan_digits_end(input, pos + 1));
    lemma_scan_digits_end_bounds(input, pos + 1);
    let d1 = scan_digits_end(input, pos);
    assert(pos < d1 <= input.len());
    // Decimal end `p` is either `d1` or a further digit run, both past `pos`.
    if 0 <= d1 < input.len() && input[d1] == 46 {
        lemma_scan_digits_end_bounds(input, d1 + 1);
    }
    let p = scan_num_dec_end(input, pos);
    assert(pos < p <= input.len());
    // Exponent end (if any) is a still-further digit run.
    if 0 <= p < input.len() && is_exp(input[p]) {
        let q0 = p + 1;
        let q = if 0 <= q0 < input.len() && is_num_sign(input[q0]) { q0 + 1 } else { q0 };
        lemma_scan_digits_end_bounds(input, q);
    }
}

/// Integer printed form re-scans exactly: a non-empty digit run followed by a
/// number boundary (no digit / `.` / exponent) scans to itself, no fraction or
/// exponent consumed.
pub proof fn lemma_lscan_num_full_int(d: Seq<u8>, tail: Seq<u8>)
    requires
        d.len() >= 1,
        all_digits(d),
        num_tail_ok(tail),
    ensures
        lscan_num_full(d + tail, 0) == (Some(TokenView::Number(d)), d.len() as int),
{
    let input = d + tail;
    assert(input[0] == d[0]);
    assert(is_digit(input[0]));
    // Integer run stops at d.len(); no `.` follows, so the decimal end is d.len().
    lemma_scan_digits_roundtrip(d, tail);
    assert(scan_digits_end(input, 0) == d.len());
    if tail.len() != 0 {
        assert(input[d.len() as int] == tail[0]);
    }
    assert(scan_num_dec_end(input, 0) == d.len());
    // No exponent follows either.
    assert(scan_num_full_end(input, 0) == d.len());
    assert(input.subrange(0, d.len() as int) =~= d);
}

/// Decimal printed form re-scans exactly: `a.b` followed by a number boundary
/// scans to itself, no exponent consumed.
pub proof fn lemma_lscan_num_full_dec(a: Seq<u8>, b: Seq<u8>, tail: Seq<u8>)
    requires
        a.len() >= 1,
        all_digits(a),
        b.len() >= 1,
        all_digits(b),
        num_tail_ok(tail),
    ensures
        lscan_num_full(a + seq![46u8] + b + tail, 0)
            == (Some(TokenView::Number(a + seq![46u8] + b)), (a.len() + 1 + b.len()) as int),
{
    let dot = seq![46u8];
    let input = a + dot + b + tail;
    let v = a + dot + b;
    assert(input[0] == a[0]);
    assert(is_digit(input[0]));
    lemma_scan_num_dec_roundtrip(a, b, tail);
    let p = (a.len() + 1 + b.len()) as int;
    assert(scan_num_dec_end(input, 0) == p);
    // `input[p]` is the boundary byte (or out of range), never an exponent.
    assert(v.len() == p);
    if tail.len() != 0 {
        assert(input[p] == tail[0]);
    }
    assert(scan_num_full_end(input, 0) == p);
    assert(input.subrange(0, p) =~= v);
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

// -- L15: single-token value dispatcher + roundtrip ----------------------------
//
// Composes L9/L12/L14 into one token-*value* scanner over the byte-determined
// classes (numbers, keywords, all symbols): skip whitespace, dispatch on the
// first byte, and produce the actual `TokenView`. lemma_lscan_token proves the
// single-token roundtrip for every such class, axiom-free. `Ident`/`String`
// (String payloads) are the remaining classes, deferred to the trust bridge.

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

// -- L16: whole-input token-LIST roundtrip -------------------------------------
//
// The lexer headline for the byte-determined classes: printing a token list with
// single-space separators and re-lexing recovers the list exactly. A space is a
// universal separator — it satisfies every token's boundary (num_tail_ok, the
// keyword non-continuation boundary, and op_tail_ok) — so no per-adjacency
// canonicalisation is needed for these classes. The scanner `lex_all_seq` strips
// leading whitespace (as a seq slice) *before* each single-token scan, so every
// scan runs at position 0 and reuses `lemma_lscan_token` directly; the only
// non-trivial locality fact is a one-byte `skip_ws` shift. Axiom-free.

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

//

/// `skip_ws` is suffix-local.
pub proof fn lemma_skip_ws_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        skip_ws(input, pos) == pos + skip_ws(input.subrange(pos, input.len() as int), 0),
    decreases input.len() - pos,
{
    let sub = input.subrange(pos, input.len() as int);
    if pos < input.len() {
        assert(sub[0] == input[pos]);
        if is_ws(input[pos]) {
            lemma_skip_ws_local(input, pos + 1);
            lemma_skip_ws_local(sub, 1);
            assert(input.subrange(pos + 1, input.len() as int) =~= sub.subrange(1, sub.len() as int));
        }
    }
}

/// `scan_digits_end` is suffix-local.
pub proof fn lemma_scan_digits_end_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        scan_digits_end(input, pos) == pos + scan_digits_end(input.subrange(pos, input.len() as int), 0),
    decreases input.len() - pos,
{
    let sub = input.subrange(pos, input.len() as int);
    if pos < input.len() {
        assert(sub[0] == input[pos]);
        if is_digit(input[pos]) {
            lemma_scan_digits_end_local(input, pos + 1);
            lemma_scan_digits_end_local(sub, 1);
            assert(input.subrange(pos + 1, input.len() as int) =~= sub.subrange(1, sub.len() as int));
        }
    }
}

/// `scan_ident_end` is suffix-local.
pub proof fn lemma_scan_ident_end_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        scan_ident_end(input, pos) == pos + scan_ident_end(input.subrange(pos, input.len() as int), 0),
    decreases input.len() - pos,
{
    let sub = input.subrange(pos, input.len() as int);
    if pos < input.len() {
        assert(sub[0] == input[pos]);
        if is_ident_cont(input[pos]) {
            lemma_scan_ident_end_local(input, pos + 1);
            lemma_scan_ident_end_local(sub, 1);
            assert(input.subrange(pos + 1, input.len() as int) =~= sub.subrange(1, sub.len() as int));
        }
    }
}


/// `scan_num_dec_end` is suffix-local.
pub proof fn lemma_scan_num_dec_end_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        scan_num_dec_end(input, pos) == pos + scan_num_dec_end(input.subrange(pos, input.len() as int), 0),
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    lemma_scan_digits_end_local(input, pos);
    lemma_scan_digits_end_bounds(sub, 0);
    let ds = scan_digits_end(sub, 0);
    let d1 = scan_digits_end(input, pos);
    assert(d1 == pos + ds);
    if d1 < n && input[d1] == 46 {
        assert(ds < sub.len());
        assert(sub[ds] == input[d1]);
        lemma_scan_digits_end_local(input, d1 + 1);
        lemma_scan_digits_end_local(sub, ds + 1);
        assert(input.subrange(d1 + 1, n) =~= sub.subrange(ds + 1, sub.len() as int));
    } else {
        if d1 < n {
            assert(ds < sub.len());
            assert(sub[ds] == input[d1]);
        } else {
            assert(ds >= sub.len());
        }
    }
}

/// Bounds for `scan_num_dec_end`.
pub proof fn lemma_scan_num_dec_end_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        pos <= scan_num_dec_end(input, pos) <= input.len(),
{
    lemma_scan_digits_end_bounds(input, pos);
    let d1 = scan_digits_end(input, pos);
    if 0 <= d1 < input.len() && input[d1] == 46 {
        lemma_scan_digits_end_bounds(input, d1 + 1);
    }
}

/// `scan_num_full_end` is suffix-local.
pub proof fn lemma_scan_num_full_end_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        scan_num_full_end(input, pos) == pos + scan_num_full_end(input.subrange(pos, input.len() as int), 0),
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    lemma_scan_num_dec_end_local(input, pos);
    let ps = scan_num_dec_end(sub, 0);
    let p = scan_num_dec_end(input, pos);
    assert(p == pos + ps);
    // bounds on ps
    lemma_scan_num_dec_end_bounds(input, pos);
    assert(0 <= ps <= sub.len());
    if p < n && is_exp(input[p]) {
        assert(ps < sub.len());
        assert(sub[ps] == input[p]);
        let q0 = p + 1;
        let q0s = ps + 1;
        let q = if q0 < n && is_num_sign(input[q0]) { q0 + 1 } else { q0 };
        let qs = if q0s < sub.len() && is_num_sign(sub[q0s]) { q0s + 1 } else { q0s };
        assert(q == pos + qs) by {
            if q0 < n {
                assert(q0s < sub.len());
                assert(sub[q0s] == input[q0]);
            } else {
                assert(q0s >= sub.len());
            }
        }
        lemma_scan_digits_end_local(input, q);
        lemma_scan_digits_end_local(sub, qs);
        assert(input.subrange(q, n) =~= sub.subrange(qs, sub.len() as int));
    } else {
        if p < n {
            assert(ps < sub.len());
            assert(sub[ps] == input[p]);
        } else {
            assert(ps >= sub.len());
        }
    }
}

/// `lscan_num_full` is suffix-local (same token value, shifted end).
pub proof fn lemma_lscan_num_full_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_num_full(input, pos).0 == lscan_num_full(input.subrange(pos, input.len() as int), 0).0,
        lscan_num_full(input, pos).1 == pos + lscan_num_full(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n && is_digit(input[pos]) {
        assert(sub[0] == input[pos]);
        lemma_scan_num_full_end_local(input, pos);
        let es = scan_num_full_end(sub, 0);
        let e = scan_num_full_end(input, pos);
        assert(e == pos + es);
        lemma_scan_num_full_bounds(input, pos);
        assert(input.subrange(pos, e) =~= sub.subrange(0, es));
    } else {
        if pos < n {
            assert(sub[0] == input[pos]);
        }
    }
}


/// `lscan_op` is suffix-local (non-recursive: reads `pos` and `pos+1`).
pub proof fn lemma_lscan_op_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_op(input, pos).0 == lscan_op(input.subrange(pos, input.len() as int), 0).0,
        lscan_op(input, pos).1 == pos + lscan_op(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n {
        assert(sub[0] == input[pos]);
        assert((pos + 1 < n) == (1 < sub.len()));
        if pos + 1 < n {
            assert(sub[1] == input[pos + 1]);
        }
    }
}

/// `lscan_sym` is suffix-local.
pub proof fn lemma_lscan_sym_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_sym(input, pos).0 == lscan_sym(input.subrange(pos, input.len() as int), 0).0,
        lscan_sym(input, pos).1 == pos + lscan_sym(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n {
        assert(sub[0] == input[pos]);
        let b = input[pos];
        if b == 60 || b == 62 || b == 33 {
            lemma_lscan_op_local(input, pos);
        }
    }
}

/// `lscan_keyword` is suffix-local (same keyword classification, shifted end).
pub proof fn lemma_lscan_keyword_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_keyword(input, pos).0 == lscan_keyword(input.subrange(pos, input.len() as int), 0).0,
        lscan_keyword(input, pos).1 == pos + lscan_keyword(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n && is_ident_start(input[pos]) {
        assert(sub[0] == input[pos]);
        lemma_scan_ident_end_local(input, pos);
        lemma_scan_ident_end_bounds(sub, 0);
        let es = scan_ident_end(sub, 0);
        let e = scan_ident_end(input, pos);
        assert(e == pos + es);
        assert(input.subrange(pos, e) =~= sub.subrange(0, es));
    }
}

/// `lscan_token` is suffix-local: scanning at `pos` yields the same token value
/// as scanning the suffix `input[pos..]` at `0`, with the end shifted by `pos`.
pub proof fn lemma_lscan_token_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_token(input, pos).0 == lscan_token(input.subrange(pos, input.len() as int), 0).0,
        lscan_token(input, pos).1 == pos + lscan_token(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    lemma_skip_ws_local(input, pos);
    lemma_skip_ws_bounds(sub, 0);
    let ps = skip_ws(sub, 0);
    let p = skip_ws(input, pos);
    assert(p == pos + ps);
    if p < n {
        assert(ps < sub.len());
        assert(sub[ps] == input[p]);
        let b = input[p];
        if is_digit(b) {
            lemma_lscan_num_full_local(input, p);
            lemma_lscan_num_full_local(sub, ps);
            assert(input.subrange(p, n) =~= sub.subrange(ps, sub.len() as int));
        } else if is_ident_start(b) {
            lemma_lscan_keyword_local(input, p);
            lemma_lscan_keyword_local(sub, ps);
            assert(input.subrange(p, n) =~= sub.subrange(ps, sub.len() as int));
        } else {
            lemma_lscan_sym_local(input, p);
            lemma_lscan_sym_local(sub, ps);
            assert(input.subrange(p, n) =~= sub.subrange(ps, sub.len() as int));
        }
    } else {
        assert(ps >= sub.len());
    }
}


/// `skip_ws` is idempotent: re-skipping from where it landed is a no-op.
pub proof fn lemma_skip_ws_idem(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        skip_ws(input, skip_ws(input, pos)) == skip_ws(input, pos),
{
    lemma_skip_ws_bounds(input, pos);
    lemma_skip_ws_fixpoint(input, pos);
    let s = skip_ws(input, pos);
    if s < input.len() {
        assert(!is_ws(input[s]));
        lemma_skip_ws_nonws(input, s);
    }
}

/// Scanning a token at `pos` is the same as scanning it at `skip_ws(input, pos)`
/// (the token scanner skips leading whitespace itself, and `skip_ws` is idempotent).
pub proof fn lemma_lscan_token_skip_ws(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_token(input, pos) == lscan_token(input, skip_ws(input, pos)),
{
    lemma_skip_ws_bounds(input, pos);
    lemma_skip_ws_idem(input, pos);
}

/// The end position of a single-token scan never exceeds the input length.
pub proof fn lemma_lscan_token_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        0 <= lscan_token(input, pos).1 <= input.len(),
{
    lemma_skip_ws_bounds(input, pos);
    let p = skip_ws(input, pos);
    if p < input.len() {
        let b = input[p];
        if is_digit(b) {
            lemma_scan_num_full_bounds(input, p);
        } else if is_ident_start(b) {
            lemma_scan_ident_end_bounds(input, p);
        }
    }
}

/// Position-based whole-input scanner, mirroring the exec loop exactly: scan a
/// token at `pos` (which skips leading whitespace), recurse at its end.
pub open spec fn lex_from(input: Seq<u8>, pos: int, fuel: nat) -> Seq<TokenView>
    decreases fuel,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        let p = skip_ws(input, pos);
        if 0 <= p < input.len() {
            let r = lscan_token(input, pos);
            match r.0 {
                Some(tv) => seq![tv] + lex_from(input, r.1, (fuel - 1) as nat),
                None => Seq::empty(),
            }
        } else {
            Seq::empty()
        }
    }
}

/// Bridge: the position-based `lex_from` equals the slice-based `lex_all_seq` on
/// the suffix. Lets the exec loop (positions) inherit `lex_all_seq`'s roundtrip.
pub proof fn lemma_lex_from_eq_seq(input: Seq<u8>, pos: int, fuel: nat)
    requires
        0 <= pos <= input.len(),
    ensures
        lex_from(input, pos, fuel) == lex_all_seq(input.subrange(pos, input.len() as int), fuel),
    decreases fuel,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if fuel != 0 {
        lemma_skip_ws_local(input, pos);
        lemma_skip_ws_bounds(sub, 0);
        let p = skip_ws(input, pos);
        let sp = skip_ws(sub, 0);
        assert(p == pos + sp);
        assert(0 <= sp <= sub.len());
        assert(pos <= p <= n);
        // stripped == input.subrange(p, n)
        assert(skip_ws_seq(sub) =~= input.subrange(p, n));
        if p < n {
            // token value agreement
            lemma_lscan_token_skip_ws(input, pos);
            lemma_lscan_token_local(input, p);
            // lscan_token(input,pos) == lscan_token(input,p); and lscan_token(input,p)
            // relates to lscan_token(input.subrange(p,n),0) == lscan_token(skip_ws_seq(sub),0)
            let r = lscan_token(input, pos);
            let rp = lscan_token(input, p);
            assert(r == rp);
            match r.0 {
                Some(tv) => {
                    // recurse
                    lemma_lscan_token_bounds(input, p);
                    lemma_lscan_token_bounds(input.subrange(p, n), 0);
                    assert(rp.1 == p + lscan_token(input.subrange(p, n), 0).1);
                    let es = lscan_token(input.subrange(p, n), 0).1;
                    assert(r.1 == p + es);
                    assert(0 <= es <= n - p);
                    assert(r.1 <= n);
                    // sub-side stripped remainder
                    assert(input.subrange(p, n).subrange(es, (n - p)) =~= input.subrange(r.1, n));
                    lemma_lex_from_eq_seq(input, r.1, (fuel - 1) as nat);
                    assert(input.subrange(r.1, n) =~= sub.subrange((r.1 - pos), sub.len() as int));
                }
                None => {}
            }
        }
    }
}


/// A recognised token advances strictly past its start (so the exec loop makes
/// progress and terminates).
pub proof fn lemma_lscan_token_progress(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
        skip_ws(input, pos) < input.len(),
        lscan_token(input, pos).0 is Some,
    ensures
        lscan_token(input, pos).1 > pos,
{
    lemma_skip_ws_bounds(input, pos);
    let p = skip_ws(input, pos);
    let b = input[p];
    if is_digit(b) {
        lemma_scan_num_full_bounds(input, p);
    } else if is_ident_start(b) {
        assert(is_ident_cont(input[p]));
        assert(scan_ident_end(input, p) == scan_ident_end(input, p + 1));
        lemma_scan_ident_end_bounds(input, p + 1);
    }
}

/// The printed list is at least as long as the token count (each token prints a
/// non-empty run plus a separator), so `input.len()+1` is always enough fuel.
pub proof fn lemma_lex_print_list_len_ge(ts: Seq<TokenView>)
    requires
        all_printable_tv(ts),
    ensures
        lex_print_list(ts).len() >= ts.len(),
    decreases ts.len(),
{
    if ts.len() != 0 {
        let rest = ts.drop_first();
        assert(all_printable_tv(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies printable_tv(#[trigger] rest[i]) by {
                assert(rest[i] == ts[i + 1]);
            }
        }
        assert(printable_tv(ts[0]));
        lemma_lex_print_tv_head(ts[0]);
        lemma_lex_print_list_len_ge(rest);
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

/// `u8`->`char`->`u8` round-trips for ASCII.
pub proof fn lemma_u8_char_u8(b: u8)
    requires
        b < 128,
    ensures
        (b as char) as u8 == b,
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

/// ASCII byte run re-decodes exactly: encoding its chars recovers it.
pub proof fn lemma_ascii_bytes_chars(bytes: Seq<u8>)
    requires
        all_ascii_bytes(bytes),
    ensures
        ascii_bytes(ascii_chars(bytes)) == bytes,
{
    assert forall|i: int| 0 <= i < bytes.len() implies ascii_bytes(ascii_chars(bytes))[i] == bytes[i] by {
        let b = bytes[i];
        assert(b < 128);
        lemma_u8_char_u8(b);
        assert(ascii_chars(bytes)[i] == (b as char));
    }
    assert(ascii_bytes(ascii_chars(bytes)) =~= bytes);
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


/// ASCII-lowercasing preserves ASCII-ness.
pub proof fn lemma_ascii_lower_seq_ascii(s: Seq<u8>)
    requires
        all_ascii_bytes(s),
    ensures
        all_ascii_bytes(ascii_lower_seq(s)),
{
    assert forall|i: int| 0 <= i < ascii_lower_seq(s).len() implies
        ascii_lower_seq(s)[i] < 128 by {
        assert(s[i] < 128);
        assert(ascii_lower_seq(s)[i] == ascii_lower(s[i]));
    }
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

/// View a real `Token` as its mirror (String payloads -> `Seq<char>`).
pub open spec fn tok_view(t: Token) -> MTok {
    match t {
        Token::Number(v) => MTok::MNum(v@),
        Token::Keyword(k) => MTok::MKw(k),
        Token::Ident(s) => MTok::MIdent(s@),
        Token::String(s) => MTok::MString(s@),
        _ => MTok::MSym(token_view(t)),
    }
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


// -- L23: whole-input unified token-LIST roundtrip -----------------------------
//
// L16 over the unified MTok mirror: print a token list (all five classes) with
// single-space separators, re-lex, recover it exactly. Same design — the space is
// a universal separator (self-delimiting strings included) and lex_mtok_seq strips
// leading whitespace as a seq slice before each scan, so every scan runs at 0.

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


// -- L24: locality for the string/ident scanners + unified dispatcher -----------

/// `scan_to_quote` is suffix-local.
pub proof fn lemma_scan_to_quote_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        scan_to_quote(input, pos) == pos + scan_to_quote(input.subrange(pos, input.len() as int), 0),
    decreases input.len() - pos,
{
    let sub = input.subrange(pos, input.len() as int);
    if pos < input.len() {
        assert(sub[0] == input[pos]);
        if input[pos] != 39 {
            lemma_scan_to_quote_local(input, pos + 1);
            lemma_scan_to_quote_local(sub, 1);
            assert(input.subrange(pos + 1, input.len() as int) =~= sub.subrange(1, sub.len() as int));
        }
    }
}

/// Bounds for `scan_to_quote`.
pub proof fn lemma_scan_to_quote_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        pos <= scan_to_quote(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && input[pos] != 39 {
        lemma_scan_to_quote_bounds(input, pos + 1);
    }
}

/// `lscan_string_m` is suffix-local (same char view, shifted end).
pub proof fn lemma_lscan_string_m_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_string_m(input, pos).0 == lscan_string_m(input.subrange(pos, input.len() as int), 0).0,
        lscan_string_m(input, pos).1 == pos + lscan_string_m(input.subrange(pos, input.len() as int), 0).1
            || lscan_string_m(input, pos).0 is None,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n && input[pos] == 39 {
        assert(sub[0] == input[pos]);
        lemma_scan_to_quote_local(input, pos + 1);
        lemma_scan_to_quote_local(sub, 1);
        lemma_scan_to_quote_bounds(sub, 1);
        let cs = scan_to_quote(sub, 1);
        let ci = scan_to_quote(input, pos + 1);
        assert(input.subrange(pos + 1, n) =~= sub.subrange(1, sub.len() as int));
        assert(ci == pos + cs);
        assert((ci < n) == (cs < sub.len()));
        if ci < n {
            assert(input.subrange(pos + 1, ci) =~= sub.subrange(1, cs));
        }
    }
}

/// `lscan_ident_m` is suffix-local.
pub proof fn lemma_lscan_ident_m_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_ident_m(input, pos).0 == lscan_ident_m(input.subrange(pos, input.len() as int), 0).0,
        lscan_ident_m(input, pos).1 == pos + lscan_ident_m(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if pos < n && is_ident_start(input[pos]) {
        assert(sub[0] == input[pos]);
        lemma_scan_ident_end_local(input, pos);
        lemma_scan_ident_end_bounds(sub, 0);
        let es = scan_ident_end(sub, 0);
        let e = scan_ident_end(input, pos);
        assert(e == pos + es);
        assert(input.subrange(pos, e) =~= sub.subrange(0, es));
    }
}

/// `lscan_mtok` is suffix-local: scanning at `pos` yields the same mirror token as
/// scanning the suffix at `0`, end shifted by `pos`.
pub proof fn lemma_lscan_mtok_local(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_mtok(input, pos).0 == lscan_mtok(input.subrange(pos, input.len() as int), 0).0,
        lscan_mtok(input, pos).1 == pos + lscan_mtok(input.subrange(pos, input.len() as int), 0).1,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    lemma_skip_ws_local(input, pos);
    lemma_skip_ws_bounds(sub, 0);
    let ps = skip_ws(sub, 0);
    let p = skip_ws(input, pos);
    assert(p == pos + ps);
    if p < n {
        assert(ps < sub.len());
        assert(sub[ps] == input[p]);
        let b = input[p];
        assert(input.subrange(p, n) =~= sub.subrange(ps, sub.len() as int));
        if b == 39 {
            lemma_lscan_string_m_local(input, p);
            lemma_lscan_string_m_local(sub, ps);
        } else if is_digit(b) {
            lemma_lscan_num_full_local(input, p);
            lemma_lscan_num_full_local(sub, ps);
        } else if is_ident_start(b) {
            lemma_lscan_keyword_local(input, p);
            lemma_lscan_keyword_local(sub, ps);
            lemma_lscan_ident_m_local(input, p);
            lemma_lscan_ident_m_local(sub, ps);
        } else {
            lemma_lscan_sym_local(input, p);
            lemma_lscan_sym_local(sub, ps);
        }
    } else {
        assert(ps >= sub.len());
    }
}


// -- L25: unified executable lexer (Vec<u8> -> Vec<Token>, all classes) ---------

/// Map a token list to its mirror list.
pub open spec fn tok_views(tokens: Seq<Token>) -> Seq<MTok>
    decreases tokens.len(),
{
    if tokens.len() == 0 {
        Seq::empty()
    } else {
        seq![tok_view(tokens[0])] + tok_views(tokens.drop_first())
    }
}

pub proof fn tok_views_concat(left: Seq<Token>, right: Seq<Token>)
    ensures tok_views(left + right) == tok_views(left) + tok_views(right),
    decreases left.len(),
{
    reveal_with_fuel(tok_views, 1);
    if left.len() > 0 {
        assert(left.drop_first() + right =~= (left + right).drop_first());
        tok_views_concat(left.drop_first(), right);
    } else {
        assert(left + right =~= right);
    }
}

/// The unified single-token end never exceeds the input length.
pub proof fn lemma_lscan_mtok_bounds(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        0 <= lscan_mtok(input, pos).1 <= input.len(),
{
    lemma_skip_ws_bounds(input, pos);
    let p = skip_ws(input, pos);
    if p < input.len() {
        let b = input[p];
        if b == 39 {
            lemma_scan_to_quote_bounds(input, p + 1);
        } else if is_digit(b) {
            lemma_scan_num_full_bounds(input, p);
        } else if is_ident_start(b) {
            lemma_scan_ident_end_bounds(input, p);
        }
    }
}

/// A recognised unified token advances strictly past its start.
pub proof fn lemma_lscan_mtok_progress(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
        skip_ws(input, pos) < input.len(),
        lscan_mtok(input, pos).0 is Some,
    ensures
        lscan_mtok(input, pos).1 > pos,
{
    lemma_skip_ws_bounds(input, pos);
    let p = skip_ws(input, pos);
    let b = input[p];
    if b == 39 {
        lemma_scan_to_quote_bounds(input, p + 1);
    } else if is_digit(b) {
        lemma_scan_num_full_bounds(input, p);
    } else if is_ident_start(b) {
        assert(is_ident_cont(input[p]));
        assert(scan_ident_end(input, p) == scan_ident_end(input, p + 1));
        lemma_scan_ident_end_bounds(input, p + 1);
    }
}

/// Position-based unified whole-input scanner (mirrors the exec loop).
pub open spec fn lex_mtok_from(input: Seq<u8>, pos: int, fuel: nat) -> Seq<MTok>
    decreases fuel,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        let p = skip_ws(input, pos);
        if 0 <= p < input.len() {
            let r = lscan_mtok(input, pos);
            match r.0 {
                Some(mt) => seq![mt] + lex_mtok_from(input, r.1, (fuel - 1) as nat),
                None => Seq::empty(),
            }
        } else {
            Seq::empty()
        }
    }
}

/// Scanning a unified token at `pos` equals scanning at `skip_ws(input, pos)`.
pub proof fn lemma_lscan_mtok_skip_ws(input: Seq<u8>, pos: int)
    requires
        0 <= pos <= input.len(),
    ensures
        lscan_mtok(input, pos) == lscan_mtok(input, skip_ws(input, pos)),
{
    lemma_skip_ws_bounds(input, pos);
    lemma_skip_ws_idem(input, pos);
}

/// Bridge: position-based `lex_mtok_from` equals slice-based `lex_mtok_seq`.
pub proof fn lemma_lex_mtok_from_eq_seq(input: Seq<u8>, pos: int, fuel: nat)
    requires
        0 <= pos <= input.len(),
    ensures
        lex_mtok_from(input, pos, fuel) == lex_mtok_seq(input.subrange(pos, input.len() as int), fuel),
    decreases fuel,
{
    let n = input.len() as int;
    let sub = input.subrange(pos, n);
    if fuel != 0 {
        lemma_skip_ws_local(input, pos);
        lemma_skip_ws_bounds(sub, 0);
        let p = skip_ws(input, pos);
        let sp = skip_ws(sub, 0);
        assert(p == pos + sp);
        assert(0 <= sp <= sub.len());
        assert(pos <= p <= n);
        assert(skip_ws_seq(sub) =~= input.subrange(p, n));
        if p < n {
            lemma_lscan_mtok_skip_ws(input, pos);
            lemma_lscan_mtok_local(input, p);
            let r = lscan_mtok(input, pos);
            let rp = lscan_mtok(input, p);
            assert(r == rp);
            match r.0 {
                Some(mt) => {
                    lemma_lscan_mtok_bounds(input, p);
                    lemma_lscan_mtok_bounds(input.subrange(p, n), 0);
                    assert(rp.1 == p + lscan_mtok(input.subrange(p, n), 0).1);
                    let es = lscan_mtok(input.subrange(p, n), 0).1;
                    assert(r.1 == p + es);
                    assert(0 <= es <= n - p);
                    assert(r.1 <= n);
                    assert(input.subrange(p, n).subrange(es, (n - p)) =~= input.subrange(r.1, n));
                    lemma_lex_mtok_from_eq_seq(input, r.1, (fuel - 1) as nat);
                    assert(input.subrange(r.1, n) =~= sub.subrange((r.1 - pos), sub.len() as int));
                }
                None => {}
            }
        }
    }
}

/// The printed list is at least as long as the token count, so `input.len()+1`
/// is always enough fuel.
pub proof fn lemma_mprint_list_len_ge(ms: Seq<MTok>)
    requires
        all_printable_mtok(ms),
    ensures
        mprint_list(ms).len() >= ms.len(),
    decreases ms.len(),
{
    if ms.len() != 0 {
        let rest = ms.drop_first();
        assert(all_printable_mtok(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies printable_mtok(#[trigger] rest[i]) by {
                assert(rest[i] == ms[i + 1]);
            }
        }
        assert(printable_mtok(ms[0]));
        lemma_mprint_head(ms[0]);
        lemma_mprint_list_len_ge(rest);
    }
}

/// First index at or after `pos` holding a double-quote byte `"` (34), or end.
pub open spec fn scan_to_dquote(input: Seq<u8>, pos: int) -> int
    decreases input.len() - pos,
{
    if 0 <= pos < input.len() && input[pos] != 34 {
        scan_to_dquote(input, pos + 1)
    } else {
        pos
    }
}

pub proof fn lemma_scan_to_dquote_run(input: Seq<u8>, pos: int, k: int)
    requires
        0 <= pos <= k <= input.len(),
        forall|i: int| pos <= i < k ==> input[i] != 34,
        k == input.len() || input[k] == 34,
    ensures
        scan_to_dquote(input, pos) == k,
    decreases k - pos,
{
    if pos < k {
        lemma_scan_to_dquote_run(input, pos + 1, k);
    }
}

/// Scan a quoted identifier, producing its char-sequence view (case preserved).
pub open spec fn lscan_qident_m(input: Seq<u8>, pos: int) -> (Option<Seq<char>>, int) {
    if 0 <= pos < input.len() && input[pos] == 34 {
        let close = scan_to_dquote(input, pos + 1);
        if close < input.len() {
            (Some(ascii_chars(input.subrange(pos + 1, close))), close + 1)
        } else {
            (None, pos)
        }
    } else {
        (None, pos)
    }
}

/// A no-dquote ASCII char run encodes to bytes with no dquote byte.
pub proof fn lemma_qident_bytes_nodquote(cs: Seq<char>)
    requires
        all_ascii_chars(cs),
        forall|i: int| 0 <= i < cs.len() ==> (#[trigger] cs[i]) as u32 != 34,
    ensures
        all_ascii_bytes(ascii_bytes(cs)),
        forall|i: int| 0 <= i < ascii_bytes(cs).len() ==> (#[trigger] ascii_bytes(cs)[i]) != 34,
{
    assert forall|i: int| 0 <= i < ascii_bytes(cs).len() implies
        ascii_bytes(cs)[i] < 128 && ascii_bytes(cs)[i] != 34 by {
        let c = cs[i];
        assert((c as u32) < 128);
        assert((c as u32) != 34);
        lemma_char_u8_val(c);
        assert(ascii_bytes(cs)[i] == (c as u8));
    }
}

/// Quoted-identifier roundtrip at the char-view level (axiom-free).
pub proof fn lemma_lscan_qident_m(cs: Seq<char>, tail: Seq<u8>)
    requires
        all_ascii_chars(cs),
        forall|i: int| 0 <= i < cs.len() ==> (#[trigger] cs[i]) as u32 != 34,
    ensures
        lscan_qident_m(seq![34u8] + ascii_bytes(cs) + seq![34u8] + tail, 0)
            == (Some(cs), (cs.len() + 2) as int),
{
    let q = seq![34u8];
    let d = ascii_bytes(cs);
    let input = q + d + q + tail;
    lemma_qident_bytes_nodquote(cs);
    assert(input[0] == 34);
    assert forall|i: int| 1 <= i < 1 + d.len() implies input[i] != 34 by {
        assert(input[i] == d[i - 1]);
    }
    let close = (1 + d.len()) as int;
    assert(input[close] == 34) by {
        assert(input[close] == q[0]);
    }
    lemma_scan_to_dquote_run(input, 1, close);
    assert(close < input.len());
    assert(input.subrange(1, close) =~= d);
    lemma_ascii_chars_bytes(cs);
    assert(ascii_chars(d) == cs);
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
