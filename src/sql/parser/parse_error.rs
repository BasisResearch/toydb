
#[allow(unused_imports)]
use vstd::prelude::*;

use super::{Keyword, Token};
use crate::error::Error;

verus! {

pub enum ParseError {
    UnexpectedToken(Token),
    UnexpectedEof,
    ExpectedIdent(Token),
    ExpectedToken(Token, Token),
    InvalidSystemTime(Vec<u8>),
    WantedNumber(Token),
    NestedExplain,
    NullabilityAlreadySet(String),
    UnexpectedKeyword(Keyword),
    DuplicateColumn(String),
    CantAliasStar,
    NumberTooLarge,
    InvalidFloatLiteral(Vec<u8>),
    ExpectedAtom(Token),
}

}

impl ParseError {
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
