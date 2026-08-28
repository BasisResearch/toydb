//! Small, self-contained verified parser core.
//!
//! This module is intentionally separate from the production parser. It is
//! the Phase 0 proving ground: bytes are scanned with an explicit cursor,
//! parser input is exposed through a one-token stream contract, and the
//! integer literal round trip is proved without importing the production
//! AST.

#![allow(dead_code)] // Proof-only entry points are erased or unused in normal Rust builds.
#![allow(clippy::manual_range_contains, clippy::needless_borrow, clippy::ptr_arg)]

use vstd::prelude::*;

verus! {

/// Tokens used by the Phase 0 core. `Byte` is an opaque byte payload used by
/// the scanner for non-syntactic bytes; later phases will replace it with byte
/// runs for identifiers and strings.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Token {
    Integer(i64),
    Byte(u8),
    True,
    False,
    Null,
    Plus,
    Star,
    Neg,
    And,
    Or,
    Not,
    Like,
    Equal,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    NotEqual,
    Divide,
    Exponentiate,
    Remainder,
    Factorial,
    Is,
    Nan,
    OpenParen,
    CloseParen,
}

/// The scanner's total result. Invalid input is represented explicitly and
/// never silently turns into end-of-input.
pub enum StreamResult {
    Token(Option<Token>),
    Invalid,
}

/// One-byte scanner specification. Whitespace is skipped. Phase 0 accepts
/// one decimal digit as an integer token; multi-digit and signed literals are
/// deliberate Phase 1 work.
pub open spec fn next_token_spec(input: Seq<u8>, pos: int) -> (StreamResult, int)
    decreases input.len() - pos,
{
    if pos >= input.len() {
        (StreamResult::Token(None), pos)
    } else {
        let b = input[pos];
        if b == 9u8 || b == 10u8 || b == 13u8 || b == 32u8 {
            next_token_spec(input, pos + 1)
        } else if 48u8 <= b && b <= 57u8 {
            (StreamResult::Token(Some(Token::Integer((b - 48u8) as i64))), pos + 1)
        } else if b == 43u8 {
            (StreamResult::Token(Some(Token::Plus)), pos + 1)
        } else if b == 42u8 {
            (StreamResult::Token(Some(Token::Star)), pos + 1)
        } else if b == 45u8 {
            (StreamResult::Token(Some(Token::Neg)), pos + 1)
        } else if b == 40u8 {
            (StreamResult::Token(Some(Token::OpenParen)), pos + 1)
        } else if b == 41u8 {
            (StreamResult::Token(Some(Token::CloseParen)), pos + 1)
        } else if b == 116u8 {
            (StreamResult::Token(Some(Token::True)), pos + 1)
        } else if b == 102u8 {
            (StreamResult::Token(Some(Token::False)), pos + 1)
        } else if b == 110u8 {
            (StreamResult::Token(Some(Token::Null)), pos + 1)
        } else {
            (StreamResult::Invalid, pos)
        }
    }
}

/// Executable scanner, proved against `next_token_spec`.
pub fn next_token(input: &[u8], pos: usize) -> (r: (StreamResult, usize))
    requires 0 <= pos <= input@.len(),
    ensures
        r.0 == next_token_spec(input@, pos as int).0,
        r.1 as int == next_token_spec(input@, pos as int).1,
    decreases input.len() - pos,
{
    if pos >= input.len() {
        (StreamResult::Token(None), pos)
    } else {
        let b = input[pos];
        if b == 9u8 || b == 10u8 || b == 13u8 || b == 32u8 {
            next_token(input, pos + 1)
        } else if 48u8 <= b && b <= 57u8 {
            (StreamResult::Token(Some(Token::Integer((b - 48u8) as i64))), pos + 1)
        } else if b == 43u8 {
            (StreamResult::Token(Some(Token::Plus)), pos + 1)
        } else if b == 42u8 {
            (StreamResult::Token(Some(Token::Star)), pos + 1)
        } else if b == 45u8 {
            (StreamResult::Token(Some(Token::Neg)), pos + 1)
        } else if b == 40u8 {
            (StreamResult::Token(Some(Token::OpenParen)), pos + 1)
        } else if b == 41u8 {
            (StreamResult::Token(Some(Token::CloseParen)), pos + 1)
        } else if b == 116u8 {
            (StreamResult::Token(Some(Token::True)), pos + 1)
        } else if b == 102u8 {
            (StreamResult::Token(Some(Token::False)), pos + 1)
        } else if b == 110u8 {
            (StreamResult::Token(Some(Token::Null)), pos + 1)
        } else {
            (StreamResult::Invalid, pos)
        }
    }
}

/// Remaining tokens from a byte cursor. Invalid input truncates the
/// well-formed token view; the stream still reports `Invalid` to its caller.
pub open spec fn tokens_from(input: Seq<u8>, pos: int) -> Seq<Token>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Seq::empty()
    } else if input[pos] == 9u8 || input[pos] == 10u8 || input[pos] == 13u8 || input[pos] == 32u8 {
        tokens_from(input, pos + 1)
    } else {
        match next_token_spec(input, pos).0 {
            StreamResult::Token(Some(token)) => seq![token] + tokens_from(input, pos + 1),
            _ => Seq::empty(),
        }
    }
}

/// Connect the scanner result to the head/tail decomposition used by the
/// stream contract.
pub proof fn scanner_head(input: Seq<u8>, pos: int)
    requires 0 <= pos <= input.len(),
    ensures
        match next_token_spec(input, pos) {
            (StreamResult::Token(Some(token)), end) =>
                tokens_from(input, pos) =~= seq![token] + tokens_from(input, end),
            _ => true,
        },
    decreases input.len() - pos,
{
    if pos >= input.len() {
    } else {
        let b = input[pos];
        if b == 9u8 || b == 10u8 || b == 13u8 || b == 32u8 {
            scanner_head(input, pos + 1);
        } else if 48u8 <= b && b <= 57u8 {
        } else if b == 43u8 || b == 40u8 || b == 41u8 {
        }
    }
}

proof fn scanner_empty(input: Seq<u8>, pos: int)
    requires 0 <= pos <= input.len(),
    ensures
        match next_token_spec(input, pos) {
            (StreamResult::Token(None), _) | (StreamResult::Invalid, _) =>
                tokens_from(input, pos) =~= Seq::empty(),
            _ => true,
        },
    decreases input.len() - pos,
{
    if pos >= input.len() {
    } else {
        let b = input[pos];
        if b == 9u8 || b == 10u8 || b == 13u8 || b == 32u8 {
            scanner_empty(input, pos + 1);
        } else if 48u8 <= b && b <= 57u8 {
        } else if b == 43u8 || b == 40u8 || b == 41u8 {
        }
    }
}

proof fn scanner_end(input: Seq<u8>, pos: int)
    requires 0 <= pos <= input.len(),
    ensures next_token_spec(input, pos).1 <= input.len(),
    decreases input.len() - pos,
{
    if pos >= input.len() {
    } else {
        let b = input[pos];
        if b == 9u8 || b == 10u8 || b == 13u8 || b == 32u8 {
            scanner_end(input, pos + 1);
        }
    }
}

/// A streaming interface whose specification exposes only the remaining
/// token sequence.  Implementations may use a cursor or a one-token cache.
trait PeekStream {
    spec fn view(&self) -> Seq<Token>;
    spec fn valid(&self) -> bool;

    fn peek(&mut self) -> (r: StreamResult)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            };

    fn next(&mut self) -> (r: StreamResult)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view().drop_first(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            };
}

/// Byte-backed leaf stream.  Its view is the scanner's remaining token
/// sequence; parser proofs can therefore use this stream once the production
/// lexer is bridged to the Phase 0 byte model.
struct ByteTokenStream<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> ByteTokenStream<'a> {
    fn new(input: &'a [u8]) -> (r: Self)
        ensures r.view() == tokens_from(input@, 0),
    {
        ByteTokenStream { input, pos: 0 }
    }
}

impl PeekStream for ByteTokenStream<'_> {
    spec fn view(&self) -> Seq<Token> {
        tokens_from(self.input@, self.pos as int)
    }

    spec fn valid(&self) -> bool {
        self.pos as int <= self.input@.len()
    }

    fn peek(&mut self) -> (r: StreamResult)
        ensures
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            },
    {
        let ghost before = self.view();
        if self.pos > self.input.len() {
            return StreamResult::Invalid;
        }
        let (result, _) = next_token(self.input, self.pos);
        proof {
            scanner_head(self.input@, self.pos as int);
            assert(before =~= tokens_from(self.input@, self.pos as int));
            assert(result == next_token_spec(self.input@, self.pos as int).0);
            match result {
                StreamResult::Token(Some(token)) => {
                    assert(before.len() > 0);
                    assert(before[0] == token);
                }
                StreamResult::Token(None) | StreamResult::Invalid => {
                    scanner_empty(self.input@, self.pos as int);
                    assert(before.len() == 0);
                }
            }
        }
        result
    }

    fn next(&mut self) -> (r: StreamResult)
        ensures
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view().drop_first(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            },
    {
        let ghost before = self.view();
        if self.pos > self.input.len() {
            return StreamResult::Invalid;
        }
        let ghost start = self.pos;
        let (result, end) = next_token(self.input, self.pos);
        match result {
            StreamResult::Token(Some(token)) => {
                self.pos = end;
                proof {
                    scanner_head(self.input@, old(self).pos as int);
                    assert(start < self.input.len());
                    scanner_end(self.input@, start as int);
                    assert(end as int <= self.input@.len());
                    assert(before =~= tokens_from(self.input@, old(self).pos as int));
                    assert(result == next_token_spec(self.input@, old(self).pos as int).0);
                    assert(before.len() > 0);
                    assert(before[0] == token);
                }
                StreamResult::Token(Some(token))
            }
            _ => {
                proof {
                    scanner_head(self.input@, old(self).pos as int);
                    scanner_empty(self.input@, old(self).pos as int);
                    assert(before =~= tokens_from(self.input@, old(self).pos as int));
                    assert(result == next_token_spec(self.input@, old(self).pos as int).0);
                    assert(before.len() == 0);
                }
                result
            }
        }
    }
}

/// A token-slice stream used by the parser proof harness.  It has O(1) cursor
/// state and gives the parser the same contract as the byte stream.
struct TokenStream<'a> {
    input: &'a [Token],
    pos: usize,
}

impl<'a> TokenStream<'a> {
    fn new(input: &'a [Token]) -> (r: Self)
        ensures r.view() == input@,
    {
        TokenStream { input, pos: 0 }
    }
}

impl PeekStream for TokenStream<'_> {
    spec fn view(&self) -> Seq<Token> {
        if self.pos as int >= self.input@.len() {
            Seq::empty()
        } else {
            self.input@.subrange(self.pos as int, self.input@.len() as int)
        }
    }

    spec fn valid(&self) -> bool {
        true
    }

    fn peek(&mut self) -> (r: StreamResult)
        ensures
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            },
    {
        let ghost before = self.view();
        if self.pos < self.input.len() {
            let token = self.input[self.pos];
            proof {
                assert(before.len() == self.input@.len() - self.pos as int);
                assert(before[0] == token);
                assert(self.view() =~= before);
            }
            StreamResult::Token(Some(token))
        } else {
            proof {
                assert(before.len() == 0);
            }
            StreamResult::Token(None)
        }
    }

    fn next(&mut self) -> (r: StreamResult)
        ensures
            match r {
                StreamResult::Token(Some(token)) =>
                    old(self).view().len() > 0
                        && token == old(self).view()[0]
                        && final(self).view() == old(self).view().drop_first(),
                StreamResult::Token(None) =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
                StreamResult::Invalid =>
                    old(self).view().len() == 0 && final(self).view() == old(self).view(),
            },
    {
        let ghost before = self.view();
        if self.pos < self.input.len() {
            let token = self.input[self.pos];
            self.pos += 1;
            proof {
                assert(before.len() > 0);
                assert(before[0] == token);
                assert(before.drop_first() =~= self.view());
            }
            StreamResult::Token(Some(token))
        } else {
            proof {
                assert(before.len() == 0);
            }
            StreamResult::Token(None)
        }
    }
}

/// Minimal recursive expression AST for Phase 1.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Integer(i64),
    True,
    False,
    Null,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IsValue {
    Null,
    Nan,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    And,
    Divide,
    Equal,
    Exponentiate,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    Like,
    Multiply,
    NotEqual,
    Or,
    Remainder,
    Subtract,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Identity,
    Not,
    Factorial,
    Is(IsValue),
}

#[derive(PartialEq, Eq)]
pub enum Expression {
    Literal(Literal),
    Column(u8),
    Binary(BinaryOp, Box<Expression>, Box<Expression>),
    Unary(UnaryOp, Box<Expression>),
}

#[derive(PartialEq, Eq)]
pub enum ParseResult {
    Ok(Expression),
    Err,
}

/// Parse an atomic token through the stream contract.
spec fn parse_token_spec(token: Token) -> ParseResult {
    match token {
        Token::Integer(value) => ParseResult::Ok(Expression::Literal(Literal::Integer(value))),
        Token::True => ParseResult::Ok(Expression::Literal(Literal::True)),
        Token::False => ParseResult::Ok(Expression::Literal(Literal::False)),
        Token::Null => ParseResult::Ok(Expression::Literal(Literal::Null)),
        Token::Byte(value) => ParseResult::Ok(Expression::Column(value)),
        _ => ParseResult::Err,
    }
}

pub open spec fn parse_binary_token_spec(token: Token) -> Option<BinaryOp> {
    match token {
        Token::Plus => Some(BinaryOp::Add),
        Token::Star => Some(BinaryOp::Multiply),
        Token::And => Some(BinaryOp::And),
        Token::Or => Some(BinaryOp::Or),
        Token::Like => Some(BinaryOp::Like),
        Token::Equal => Some(BinaryOp::Equal),
        Token::GreaterThan => Some(BinaryOp::GreaterThan),
        Token::GreaterThanOrEqual => Some(BinaryOp::GreaterThanOrEqual),
        Token::LessThan => Some(BinaryOp::LessThan),
        Token::LessThanOrEqual => Some(BinaryOp::LessThanOrEqual),
        Token::NotEqual => Some(BinaryOp::NotEqual),
        Token::Divide => Some(BinaryOp::Divide),
        Token::Exponentiate => Some(BinaryOp::Exponentiate),
        Token::Remainder => Some(BinaryOp::Remainder),
        Token::Neg => Some(BinaryOp::Subtract),
        _ => None,
    }
}

pub open spec fn parse_unary_token_spec(token: Token) -> Option<UnaryOp> {
    match token {
        Token::Neg => Some(UnaryOp::Negate),
        Token::Plus => Some(UnaryOp::Identity),
        Token::Not => Some(UnaryOp::Not),
        _ => None,
    }
}

fn parse_token(token: Token) -> (r: ParseResult)
    ensures r == parse_token_spec(token),
{
    match token {
        Token::Integer(value) => ParseResult::Ok(Expression::Literal(Literal::Integer(value))),
        Token::True => ParseResult::Ok(Expression::Literal(Literal::True)),
        Token::False => ParseResult::Ok(Expression::Literal(Literal::False)),
        Token::Null => ParseResult::Ok(Expression::Literal(Literal::Null)),
        Token::Byte(value) => ParseResult::Ok(Expression::Column(value)),
        _ => ParseResult::Err,
    }
}

fn parse_binary_token(token: Token) -> (r: Option<BinaryOp>)
    ensures r == parse_binary_token_spec(token),
{
    match token {
        Token::Plus => Some(BinaryOp::Add),
        Token::Star => Some(BinaryOp::Multiply),
        Token::And => Some(BinaryOp::And),
        Token::Or => Some(BinaryOp::Or),
        Token::Like => Some(BinaryOp::Like),
        Token::Equal => Some(BinaryOp::Equal),
        Token::GreaterThan => Some(BinaryOp::GreaterThan),
        Token::GreaterThanOrEqual => Some(BinaryOp::GreaterThanOrEqual),
        Token::LessThan => Some(BinaryOp::LessThan),
        Token::LessThanOrEqual => Some(BinaryOp::LessThanOrEqual),
        Token::NotEqual => Some(BinaryOp::NotEqual),
        Token::Divide => Some(BinaryOp::Divide),
        Token::Exponentiate => Some(BinaryOp::Exponentiate),
        Token::Remainder => Some(BinaryOp::Remainder),
        Token::Neg => Some(BinaryOp::Subtract),
        _ => None,
    }
}

fn parse_group<S: PeekStream>(s: &mut S) -> (r: ParseResult)
    requires s.valid(),
    ensures
        final(s).valid(),
        final(s).view().len() <= old(s).view().len(),
    decreases s.view().len(),
{
    let ghost group_len = s.view().len();
    match s.peek() {
        StreamResult::Token(Some(Token::Neg)) => {
            s.next();
            match s.next() {
                StreamResult::Token(Some(first)) => match first {
                    Token::OpenParen => match parse_group(s) {
                        ParseResult::Ok(inner) => match s.next() {
                            StreamResult::Token(Some(Token::CloseParen)) =>
                                ParseResult::Ok(Expression::Unary(UnaryOp::Negate, Box::new(inner))),
                            _ => ParseResult::Err,
                        },
                        ParseResult::Err => ParseResult::Err,
                    },
                    first => match parse_token(first) {
                    ParseResult::Ok(inner) => match s.next() {
                        StreamResult::Token(Some(Token::CloseParen)) =>
                            ParseResult::Ok(Expression::Unary(UnaryOp::Negate, Box::new(inner))),
                        _ => ParseResult::Err,
                    },
                    ParseResult::Err => ParseResult::Err,
                    },
                },
                _ => ParseResult::Err,
            }
        }
        _ => {
            match s.next() {
                StreamResult::Token(Some(first)) => match first {
                    Token::OpenParen => match parse_group(s) {
                        ParseResult::Ok(left) => match s.next() {
                            StreamResult::Token(Some(op_token)) => match parse_binary_token(op_token) {
                                Some(op) => match s.next() {
                                    StreamResult::Token(Some(right_first)) => match right_first {
                                        Token::OpenParen => {
                                            proof { assert(s.view().len() < group_len); }
                                            match parse_group(s) {
                                            ParseResult::Ok(right) => match s.next() {
                                                StreamResult::Token(Some(Token::CloseParen)) => ParseResult::Ok(
                                                    Expression::Binary(op, Box::new(left), Box::new(right)),
                                                ),
                                                _ => ParseResult::Err,
                                            },
                                            ParseResult::Err => ParseResult::Err,
                                            }
                                        },
                                        right_token => match parse_token(right_token) {
                                            ParseResult::Ok(right) => match s.next() {
                                                StreamResult::Token(Some(Token::CloseParen)) => ParseResult::Ok(
                                                    Expression::Binary(op, Box::new(left), Box::new(right)),
                                                ),
                                                _ => ParseResult::Err,
                                            },
                                            ParseResult::Err => ParseResult::Err,
                                        },
                                    },
                                    _ => ParseResult::Err,
                                },
                                None => ParseResult::Err,
                            },
                            _ => ParseResult::Err,
                        },
                        ParseResult::Err => ParseResult::Err,
                    },
                    first => match parse_token(first) {
                    ParseResult::Ok(left) => match s.next() {
                        StreamResult::Token(Some(op_token)) => match parse_binary_token(op_token) {
                            Some(op) => match s.next() {
                                StreamResult::Token(Some(right_first)) => match right_first {
                                    Token::OpenParen => {
                                        proof { assert(s.view().len() < group_len); }
                                        match parse_group(s) {
                                        ParseResult::Ok(right) => match s.next() {
                                            StreamResult::Token(Some(Token::CloseParen)) => ParseResult::Ok(
                                                Expression::Binary(op, Box::new(left), Box::new(right)),
                                            ),
                                            _ => ParseResult::Err,
                                        },
                                        ParseResult::Err => ParseResult::Err,
                                        }
                                    },
                                    right_token => match parse_token(right_token) {
                                        ParseResult::Ok(right) => match s.next() {
                                            StreamResult::Token(Some(Token::CloseParen)) => ParseResult::Ok(
                                                Expression::Binary(op, Box::new(left), Box::new(right)),
                                            ),
                                            _ => ParseResult::Err,
                                        },
                                        ParseResult::Err => ParseResult::Err,
                                    },
                                },
                                _ => ParseResult::Err,
                            },
                            None => ParseResult::Err,
                        },
                        _ => ParseResult::Err,
                    },
                    ParseResult::Err => ParseResult::Err,
                    },
                },
                _ => ParseResult::Err,
            }
        }
    }
}

fn parse_expr<S: PeekStream>(s: &mut S) -> (r: ParseResult)
    requires s.valid(),
    ensures
        final(s).valid(),
        final(s).view().len() <= old(s).view().len(),
    decreases s.view().len(),
{
    match s.next() {
        StreamResult::Token(Some(Token::OpenParen)) => parse_group(s),
        StreamResult::Token(Some(token)) => parse_token(token),
        _ => ParseResult::Err,
    }
}

/// Canonical, fully parenthesized token-level printer.
pub open spec fn print_expr(e: Expression) -> Seq<Token>
    decreases e,
{
    match e {
        Expression::Literal(Literal::Integer(value)) => seq![Token::Integer(value)],
        Expression::Literal(Literal::True) => seq![Token::True],
        Expression::Literal(Literal::False) => seq![Token::False],
        Expression::Literal(Literal::Null) => seq![Token::Null],
        Expression::Column(value) => seq![Token::Byte(value)],
        Expression::Unary(op, inner) => match op {
            UnaryOp::Negate => seq![Token::OpenParen, Token::Neg]
                + print_expr(*inner) + seq![Token::CloseParen],
            UnaryOp::Identity => seq![Token::OpenParen, Token::Plus]
                + print_expr(*inner) + seq![Token::CloseParen],
            UnaryOp::Not => seq![Token::OpenParen, Token::Not]
                + print_expr(*inner) + seq![Token::CloseParen],
            UnaryOp::Factorial => seq![Token::OpenParen] + print_expr(*inner)
                + seq![Token::Factorial, Token::CloseParen],
            UnaryOp::Is(value) => {
                let token = match value {
                    IsValue::Null => Token::Null,
                    IsValue::Nan => Token::Nan,
                };
                seq![Token::OpenParen] + print_expr(*inner)
                    + seq![Token::Is, token, Token::CloseParen]
            }
        },
        Expression::Binary(op, left, right) => {
            let token = match op {
                BinaryOp::Add => Token::Plus,
                BinaryOp::And => Token::And,
                BinaryOp::Divide => Token::Divide,
                BinaryOp::Equal => Token::Equal,
                BinaryOp::Exponentiate => Token::Exponentiate,
                BinaryOp::GreaterThan => Token::GreaterThan,
                BinaryOp::GreaterThanOrEqual => Token::GreaterThanOrEqual,
                BinaryOp::LessThan => Token::LessThan,
                BinaryOp::LessThanOrEqual => Token::LessThanOrEqual,
                BinaryOp::Like => Token::Like,
                BinaryOp::Multiply => Token::Star,
                BinaryOp::NotEqual => Token::NotEqual,
                BinaryOp::Or => Token::Or,
                BinaryOp::Remainder => Token::Remainder,
                BinaryOp::Subtract => Token::Neg,
            };
            seq![Token::OpenParen] + print_expr(*left) + seq![token] + print_expr(*right)
                + seq![Token::CloseParen]
        }
    }
}

/// Maximum recursive nesting in a canonical expression.
pub open spec fn expr_depth(e: Expression) -> nat
    decreases e,
{
    match e {
        Expression::Literal(_) | Expression::Column(_) => 1,
        Expression::Unary(_, inner) => 1 + expr_depth(*inner),
        Expression::Binary(_, left, right) =>
            1 + if expr_depth(*left) >= expr_depth(*right) {
                expr_depth(*left)
            } else {
                expr_depth(*right)
            },
    }
}

/// Pure decoder for the canonical token grammar. It returns the unconsumed
/// suffix so recursive expressions need no token materialization.
pub open spec fn parse_prefix(input: Seq<Token>, fuel: nat) -> (ParseResult, Seq<Token>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (ParseResult::Err, input)
    } else {
        match input[0] {
            Token::Integer(value) =>
                (ParseResult::Ok(Expression::Literal(Literal::Integer(value))), input.drop_first()),
            Token::True =>
                (ParseResult::Ok(Expression::Literal(Literal::True)), input.drop_first()),
            Token::False =>
                (ParseResult::Ok(Expression::Literal(Literal::False)), input.drop_first()),
            Token::Null =>
                (ParseResult::Ok(Expression::Literal(Literal::Null)), input.drop_first()),
            Token::Byte(value) =>
                (ParseResult::Ok(Expression::Column(value)), input.drop_first()),
            Token::OpenParen => {
                if input.len() >= 2 {
                    match parse_unary_token_spec(input[1]) {
                        Some(op) => {
                            let inner_result = parse_prefix(
                                input.drop_first().drop_first(),
                                (fuel - 1) as nat,
                            );
                            match inner_result {
                                (ParseResult::Ok(inner), rest)
                                    if rest.len() > 0 && rest[0] == Token::CloseParen =>
                                        (ParseResult::Ok(Expression::Unary(op, Box::new(inner))), rest.drop_first()),
                                _ => (ParseResult::Err, input),
                            }
                        }
                        None => {
                            let left_result = parse_prefix(input.drop_first(), (fuel - 1) as nat);
                            match left_result {
                                (ParseResult::Ok(left), after_left) if after_left.len() > 0 => {
                                    if after_left[0] == Token::Factorial {
                                        if after_left.len() > 1 && after_left[1] == Token::CloseParen {
                                            (ParseResult::Ok(Expression::Unary(
                                                UnaryOp::Factorial, Box::new(left),
                                            )), after_left.drop_first().drop_first())
                                        } else {
                                            (ParseResult::Err, input)
                                        }
                                    } else if after_left[0] == Token::Is {
                                        if after_left.len() >= 3 && after_left[2] == Token::CloseParen {
                                            let value = match after_left[1] {
                                                Token::Null => Some(IsValue::Null),
                                                Token::Nan => Some(IsValue::Nan),
                                                _ => None,
                                            };
                                            match value {
                                                Some(value) => (ParseResult::Ok(Expression::Unary(
                                                    UnaryOp::Is(value), Box::new(left),
                                                )), after_left.drop_first().drop_first().drop_first()),
                                                None => (ParseResult::Err, input),
                                            }
                                        } else {
                                            (ParseResult::Err, input)
                                        }
                                    } else {
                                        match parse_binary_token_spec(after_left[0]) {
                                            Some(op) => {
                                                let right_result = parse_prefix(
                                                    after_left.drop_first(),
                                                    (fuel - 1) as nat,
                                                );
                                                match right_result {
                                                    (ParseResult::Ok(right), rest)
                                                        if rest.len() > 0 && rest[0] == Token::CloseParen =>
                                                            (ParseResult::Ok(Expression::Binary(
                                                                op, Box::new(left), Box::new(right),
                                                            )), rest.drop_first()),
                                                    _ => (ParseResult::Err, input),
                                                }
                                            }
                                            None => (ParseResult::Err, input),
                                        }
                                    }
                                }
                                _ => (ParseResult::Err, input),
                            }
                        }
                    }
                } else {
                    (ParseResult::Err, input)
                }
            }
            _ => (ParseResult::Err, input),
        }
    }
}

/// The decoder consumes exactly one printed expression and preserves any
/// following tokens. This is the structural roundtrip lemma.
proof fn lemma_parse_atom_prefix(token: Token, expression: Expression, tail: Seq<Token>, fuel: nat)
    requires
        fuel > 0,
        parse_token_spec(token) == ParseResult::Ok(expression),
    ensures parse_prefix(seq![token] + tail, fuel) == (ParseResult::Ok(expression), tail),
{
    reveal_with_fuel(parse_prefix, 1);
}

#[verifier::rlimit(1000)]
pub proof fn lemma_parse_print_prefix(e: &Expression, tail: Seq<Token>, fuel: nat)
    requires fuel >= expr_depth(*e),
    ensures parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail),
    decreases *e,
{
    reveal_with_fuel(parse_prefix, 1);
    reveal(print_expr);
    match e {
        Expression::Literal(Literal::Integer(value)) => {
            assert(fuel > 0);
            assert(fuel != 0);
            assert(print_expr(*e) == seq![Token::Integer(*value)]);
            assert((seq![Token::Integer(*value)] + tail).len() > 0);
            assert(print_expr(*e) + tail == seq![Token::Integer(*value)] + tail);
            assert((seq![Token::Integer(*value)] + tail).drop_first() =~= tail);
            lemma_parse_atom_prefix(
                Token::Integer(*value),
                Expression::Literal(Literal::Integer(*value)),
                tail,
                fuel,
            );
            assert(parse_prefix(print_expr(*e) + tail, fuel)
                == (ParseResult::Ok(*e), tail));
        }
        Expression::Literal(Literal::True) => {
            assert(fuel > 0);
            assert((seq![Token::True] + tail).drop_first() =~= tail);
            lemma_parse_atom_prefix(Token::True, Expression::Literal(Literal::True), tail, fuel);
            assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
        }
        Expression::Literal(Literal::False) => {
            assert(fuel > 0);
            assert((seq![Token::False] + tail).drop_first() =~= tail);
            lemma_parse_atom_prefix(Token::False, Expression::Literal(Literal::False), tail, fuel);
            assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
        }
        Expression::Literal(Literal::Null) => {
            assert(fuel > 0);
            assert((seq![Token::Null] + tail).drop_first() =~= tail);
            lemma_parse_atom_prefix(Token::Null, Expression::Literal(Literal::Null), tail, fuel);
            assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
        }
        Expression::Column(value) => {
            assert(fuel > 0);
            assert((seq![Token::Byte(*value)] + tail).drop_first() =~= tail);
            lemma_parse_atom_prefix(Token::Byte(*value), Expression::Column(*value), tail, fuel);
            assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
        }
        Expression::Unary(unary_op, inner) => {
            assert(expr_depth(**inner) < expr_depth(*e));
            match unary_op {
                UnaryOp::Negate | UnaryOp::Identity | UnaryOp::Not => {
                    let token = match unary_op {
                        UnaryOp::Negate => Token::Neg,
                        UnaryOp::Identity => Token::Plus,
                        _ => Token::Not,
                    };
                    let inner_tail = seq![Token::CloseParen] + tail;
                    lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                    assert((print_expr(*e) + tail).drop_first().drop_first()
                        =~= print_expr(**inner) + inner_tail);
                    assert(inner_tail.drop_first() =~= tail);
                    assert(parse_prefix(print_expr(**inner) + inner_tail, (fuel - 1) as nat)
                        == (ParseResult::Ok(**inner), inner_tail));
                    assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
                }
                UnaryOp::Factorial => {
                    let inner_tail = seq![Token::Factorial, Token::CloseParen] + tail;
                    lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                    assert((print_expr(*e) + tail).drop_first()
                        =~= print_expr(**inner) + inner_tail);
                    assert(inner_tail.drop_first().drop_first() =~= tail);
                    assert(parse_prefix(print_expr(**inner) + inner_tail, (fuel - 1) as nat)
                        == (ParseResult::Ok(**inner), inner_tail));
                    assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
                }
                UnaryOp::Is(value) => {
                    let value_token = match value {
                        IsValue::Null => Token::Null,
                        IsValue::Nan => Token::Nan,
                    };
                    let inner_tail = seq![Token::Is, value_token, Token::CloseParen] + tail;
                    lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                    assert((print_expr(*e) + tail).drop_first()
                        =~= print_expr(**inner) + inner_tail);
                    assert(inner_tail.drop_first().drop_first().drop_first() =~= tail);
                    assert(parse_prefix(print_expr(**inner) + inner_tail, (fuel - 1) as nat)
                        == (ParseResult::Ok(**inner), inner_tail));
                    assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
                }
            }
        }
        Expression::Binary(binary_op, left, right) => {
            assert(expr_depth(**left) < expr_depth(*e));
            assert(expr_depth(**right) < expr_depth(*e));
            let op = match binary_op {
                BinaryOp::Add => Token::Plus,
                BinaryOp::And => Token::And,
                BinaryOp::Divide => Token::Divide,
                BinaryOp::Equal => Token::Equal,
                BinaryOp::Exponentiate => Token::Exponentiate,
                BinaryOp::GreaterThan => Token::GreaterThan,
                BinaryOp::GreaterThanOrEqual => Token::GreaterThanOrEqual,
                BinaryOp::LessThan => Token::LessThan,
                BinaryOp::LessThanOrEqual => Token::LessThanOrEqual,
                BinaryOp::Like => Token::Like,
                BinaryOp::Multiply => Token::Star,
                BinaryOp::NotEqual => Token::NotEqual,
                BinaryOp::Or => Token::Or,
                BinaryOp::Remainder => Token::Remainder,
                BinaryOp::Subtract => Token::Neg,
            };
            let right_tail = seq![Token::CloseParen] + tail;
            let left_tail = seq![op] + print_expr(**right) + right_tail;
            lemma_parse_print_prefix(
                left,
                left_tail,
                (fuel - 1) as nat,
            );
            lemma_parse_print_prefix(
                right,
                right_tail,
                (fuel - 1) as nat,
            );
            assert((print_expr(*e) + tail).drop_first() =~= print_expr(**left) + left_tail);
            assert(left_tail.drop_first() =~= print_expr(**right) + right_tail);
            assert(right_tail.drop_first() =~= tail);
            assert(parse_prefix(print_expr(**left) + left_tail, (fuel - 1) as nat)
                == (ParseResult::Ok(**left), left_tail));
            assert(parse_prefix(print_expr(**right) + right_tail, (fuel - 1) as nat)
                == (ParseResult::Ok(**right), right_tail));
            assert(parse_prefix(print_expr(*e) + tail, fuel) == (ParseResult::Ok(*e), tail));
        }
    }
}

/// Canonical token roundtrip.
pub proof fn print_parse_roundtrip(e: Expression)
    ensures parse_prefix(print_expr(e), expr_depth(e)) == (ParseResult::Ok(e), Seq::empty()),
{
    lemma_parse_print_prefix(&e, Seq::empty(), expr_depth(e));
}

/// The canonical printer is injective.
pub proof fn print_expr_injective(left: Expression, right: Expression)
    ensures print_expr(left) == print_expr(right) ==> left == right,
{
    if print_expr(left) == print_expr(right) {
        let fuel = if expr_depth(left) >= expr_depth(right) {
            expr_depth(left)
        } else {
            expr_depth(right)
        };
        lemma_parse_print_prefix(&left, Seq::empty(), fuel);
        lemma_parse_print_prefix(&right, Seq::empty(), fuel);
        assert(ParseResult::Ok(left) == ParseResult::Ok(right));
    }
}

fn append_tokens(out: &mut Vec<Token>, tail: &Vec<Token>)
    ensures final(out)@ == old(out)@ + tail@,
{
    let mut i: usize = 0;
    while i < tail.len()
        invariant
            0 <= i <= tail.len(),
            out@ == old(out)@ + tail@.subrange(0, i as int),
        decreases tail.len() - i,
    {
        out.push(tail[i]);
        i += 1;
    }
}

fn print_expr_tokens(e: &Expression) -> (r: Vec<Token>)
    ensures r@ == print_expr(*e),
    decreases *e,
{
    let mut out = Vec::new();
    match e {
        Expression::Literal(Literal::Integer(value)) => out.push(Token::Integer(*value)),
        Expression::Literal(Literal::True) => out.push(Token::True),
        Expression::Literal(Literal::False) => out.push(Token::False),
        Expression::Literal(Literal::Null) => out.push(Token::Null),
        Expression::Column(value) => out.push(Token::Byte(*value)),
        Expression::Unary(op, inner) => {
            out.push(Token::OpenParen);
            let inner_tokens = print_expr_tokens(&inner);
            match op {
                UnaryOp::Negate => {
                    out.push(Token::Neg);
                    append_tokens(&mut out, &inner_tokens);
                    out.push(Token::CloseParen);
                }
                UnaryOp::Identity => {
                    out.push(Token::Plus);
                    append_tokens(&mut out, &inner_tokens);
                    out.push(Token::CloseParen);
                }
                UnaryOp::Not => {
                    out.push(Token::Not);
                    append_tokens(&mut out, &inner_tokens);
                    out.push(Token::CloseParen);
                }
                UnaryOp::Factorial => {
                    append_tokens(&mut out, &inner_tokens);
                    out.push(Token::Factorial);
                    out.push(Token::CloseParen);
                }
                UnaryOp::Is(value) => {
                    append_tokens(&mut out, &inner_tokens);
                    out.push(Token::Is);
                    out.push(match value {
                        IsValue::Null => Token::Null,
                        IsValue::Nan => Token::Nan,
                    });
                    out.push(Token::CloseParen);
                }
            }
        }
        Expression::Binary(op, left, right) => {
            out.push(Token::OpenParen);
            let left_tokens = print_expr_tokens(&left);
            append_tokens(&mut out, &left_tokens);
            out.push(match op {
                BinaryOp::Add => Token::Plus,
                BinaryOp::And => Token::And,
                BinaryOp::Divide => Token::Divide,
                BinaryOp::Equal => Token::Equal,
                BinaryOp::Exponentiate => Token::Exponentiate,
                BinaryOp::GreaterThan => Token::GreaterThan,
                BinaryOp::GreaterThanOrEqual => Token::GreaterThanOrEqual,
                BinaryOp::LessThan => Token::LessThan,
                BinaryOp::LessThanOrEqual => Token::LessThanOrEqual,
                BinaryOp::Like => Token::Like,
                BinaryOp::Multiply => Token::Star,
                BinaryOp::NotEqual => Token::NotEqual,
                BinaryOp::Or => Token::Or,
                BinaryOp::Remainder => Token::Remainder,
                BinaryOp::Subtract => Token::Neg,
            });
            let right_tokens = print_expr_tokens(&right);
            append_tokens(&mut out, &right_tokens);
            out.push(Token::CloseParen);
        }
    }
    out
}

} // verus!
