//! Operator tag vocabulary shared by the expression printer and parser.
//!
//! `BinaryTag` and `UnaryTag` name the operators the grammar layer reasons
//! about, and `binary_from_token` / `prefix_operator` map a `TokenView` onto
//! them. `verified_roundtrip`, `verified_precedence`, `verified_minparen` and
//! `verified_minparen_stmt` all state their contracts in terms of these tags.
//!
//! This module used to also carry a spec-level print/parse round trip for the
//! function-free fragment of the grammar (`print_expr`, `parse_prefix`,
//! `print_parse_roundtrip`, `print_expr_injective`). That fragment could never
//! cover `Expression::Function` — a spec parser cannot build a `Vec` — and it
//! was superseded by the mirror-based development in `verified_roundtrip` and
//! `verified_minparen`, which covers the whole grammar over the parser that
//! actually runs. It was removed; `verified_minparen::min_roundtrip` and
//! `min_print_injective` are the properties it used to state.

#![allow(dead_code)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_production::TokenView;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, ast, float_trust, verified_production};

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BinaryTag {
    And,
    Or,
    Equal,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    NotEqual,
    Add,
    Divide,
    Exponentiate,
    Multiply,
    Remainder,
    Subtract,
    Like,
}

pub open spec fn binary_from_token(token: TokenView) -> Option<BinaryTag> {
    match token {
        TokenView::Keyword(Keyword::And) => Some(BinaryTag::And),
        TokenView::Keyword(Keyword::Or) => Some(BinaryTag::Or),
        TokenView::Equal => Some(BinaryTag::Equal),
        TokenView::GreaterThan => Some(BinaryTag::GreaterThan),
        TokenView::GreaterThanOrEqual => Some(BinaryTag::GreaterThanOrEqual),
        TokenView::LessThan => Some(BinaryTag::LessThan),
        TokenView::LessThanOrEqual => Some(BinaryTag::LessThanOrEqual),
        TokenView::NotEqual => Some(BinaryTag::NotEqual),
        // `<>` is a second spelling of not-equal (legacy toyDB accepts it). Two
        // token spellings collapse to one tag; the printer only ever emits `!=`.
        TokenView::LessOrGreaterThan => Some(BinaryTag::NotEqual),
        TokenView::Plus => Some(BinaryTag::Add),
        TokenView::Slash => Some(BinaryTag::Divide),
        TokenView::Caret => Some(BinaryTag::Exponentiate),
        TokenView::Asterisk => Some(BinaryTag::Multiply),
        TokenView::Percent => Some(BinaryTag::Remainder),
        TokenView::Minus => Some(BinaryTag::Subtract),
        TokenView::Keyword(Keyword::Like) => Some(BinaryTag::Like),
        _ => None,
    }
}

pub open spec fn prefix_operator(token: TokenView) -> Option<UnaryTag> {
    match token {
        TokenView::Plus => Some(UnaryTag::Identity),
        TokenView::Minus => Some(UnaryTag::Negate),
        TokenView::Keyword(Keyword::Not) => Some(UnaryTag::Not),
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UnaryTag {
    Identity,
    Negate,
    Not,
}

}
