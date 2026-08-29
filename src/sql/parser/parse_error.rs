//! Structured parser errors produced by the Verus-verified parser.
//!
//! The verified expression/statement parsers (`verified_precedence`,
//! `verified_control`) cannot call `format!` inside a `verus!` block, so they
//! return a `ParseError` — a plain data enum carrying the offending token /
//! keyword / bytes — instead of a formatted `crate::error::Error`. The untrusted
//! [`ParseError::render`] (a normal Rust `impl`, outside `verus!`) turns it into
//! the exact `Error::InvalidInput` string the legacy recursive-descent parser
//! produced, so error messages stay byte-for-byte identical. This is the only
//! trusted surface of the error path; the verified parsers prove they always
//! populate a `ParseError` on every rejection.

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

use super::{Keyword, Token};
use crate::error::Error;

verus! {

/// A parser rejection, mirroring one `errinput!` site of the legacy parser.
/// Constructed inside the verified parsers; rendered to `Error` by `render`.
pub enum ParseError {
    /// `unexpected token {0}` — a token that cannot begin/continue the construct.
    UnexpectedToken(Token),
    /// `unexpected end of input` — a token was required past the end.
    UnexpectedEof,
    /// `expected identifier, got {0}`.
    ExpectedIdent(Token),
    /// `expected token {0}, found {1}` — a specific token was required.
    ExpectedToken(Token, Token),
    /// `invalid system time {0}` (rendered lossily) — non-`u64` AS OF value.
    InvalidSystemTime(Vec<u8>),
    /// `unexpected token {0}, wanted number` — AS OF value was not a number.
    WantedNumber(Token),
    /// `cannot nest EXPLAIN statements`.
    NestedExplain,
    /// `nullability already set for column {0}`.
    NullabilityAlreadySet(String),
    /// `unexpected keyword {0}` — a keyword that is not a valid column constraint.
    UnexpectedKeyword(Keyword),
    /// `column {0} set multiple times` — a duplicate UPDATE assignment.
    DuplicateColumn(String),
    /// `can't alias *` — a `*` select item cannot take an alias.
    CantAliasStar,
    /// `number too large to fit in target type` — integer literal overflow.
    NumberTooLarge,
    /// `invalid float literal {0}` (rendered lossily).
    InvalidFloatLiteral(Vec<u8>),
    /// `expected expression atom, found {0}`.
    ExpectedAtom(Token),
}

} // verus!

impl ParseError {
    /// Renders the structured error into the production `Error::InvalidInput`
    /// string, matching the legacy parser's `errinput!` output exactly. Untrusted
    /// (outside `verus!`): the string content is not part of any proof, only that
    /// the verified parsers always produce a `ParseError` on rejection.
    pub fn render(self) -> Error {
        let msg = match self {
            ParseError::UnexpectedToken(token) => format!("unexpected token {token}"),
            ParseError::UnexpectedEof => "unexpected end of input".to_string(),
            ParseError::ExpectedIdent(token) => format!("expected identifier, got {token}"),
            ParseError::ExpectedToken(expect, found) => {
                format!("expected token {expect}, found {found}")
            }
            ParseError::InvalidSystemTime(bytes) => {
                format!("invalid system time {}", String::from_utf8_lossy(&bytes))
            }
            ParseError::WantedNumber(token) => format!("unexpected token {token}, wanted number"),
            ParseError::NestedExplain => "cannot nest EXPLAIN statements".to_string(),
            ParseError::NullabilityAlreadySet(name) => {
                format!("nullability already set for column {name}")
            }
            ParseError::UnexpectedKeyword(keyword) => format!("unexpected keyword {keyword}"),
            ParseError::DuplicateColumn(column) => format!("column {column} set multiple times"),
            ParseError::CantAliasStar => "can't alias *".to_string(),
            ParseError::NumberTooLarge => "number too large to fit in target type".to_string(),
            ParseError::InvalidFloatLiteral(bytes) => {
                format!("invalid float literal {}", String::from_utf8_lossy(&bytes))
            }
            ParseError::ExpectedAtom(token) => format!("expected expression atom, found {token}"),
        };
        Error::InvalidInput(msg)
    }
}
