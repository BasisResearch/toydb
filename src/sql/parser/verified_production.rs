//! Verus specifications over the production SQL AST.
//!
//! Unlike the staged parser core, this module imports the actual production
//! datatypes. It defines the exact domain accepted by the canonical printer.

#![allow(dead_code)]

#[allow(unused_imports)]
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::{Keyword, Token, ast, float_trust};

verus! {

/// Ghost view of a production token. Numeric bytes are exposed as a sequence;
/// string and identifier payloads remain opaque values.
pub enum TokenView {
    Number(Seq<u8>),
    String(String),
    Ident(String),
    Keyword(Keyword),
    Period,
    Equal,
    NotEqual,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    LessOrGreaterThan,
    Plus,
    Minus,
    Asterisk,
    Slash,
    Caret,
    Percent,
    Exclamation,
    Question,
    Comma,
    Semicolon,
    OpenParen,
    CloseParen,
}

pub open spec fn token_view(token: Token) -> TokenView {
    match token {
        Token::Number(bytes) => TokenView::Number(bytes@),
        Token::String(value) => TokenView::String(value),
        Token::Ident(value) => TokenView::Ident(value),
        Token::Keyword(value) => TokenView::Keyword(value),
        Token::Period => TokenView::Period,
        Token::Equal => TokenView::Equal,
        Token::NotEqual => TokenView::NotEqual,
        Token::GreaterThan => TokenView::GreaterThan,
        Token::GreaterThanOrEqual => TokenView::GreaterThanOrEqual,
        Token::LessThan => TokenView::LessThan,
        Token::LessThanOrEqual => TokenView::LessThanOrEqual,
        Token::LessOrGreaterThan => TokenView::LessOrGreaterThan,
        Token::Plus => TokenView::Plus,
        Token::Minus => TokenView::Minus,
        Token::Asterisk => TokenView::Asterisk,
        Token::Slash => TokenView::Slash,
        Token::Caret => TokenView::Caret,
        Token::Percent => TokenView::Percent,
        Token::Exclamation => TokenView::Exclamation,
        Token::Question => TokenView::Question,
        Token::Comma => TokenView::Comma,
        Token::Semicolon => TokenView::Semicolon,
        Token::OpenParen => TokenView::OpenParen,
        Token::CloseParen => TokenView::CloseParen,
    }
}

pub open spec fn token_views(tokens: Seq<Token>) -> Seq<TokenView>
    decreases tokens.len(),
{
    if tokens.len() == 0 {
        Seq::empty()
    } else {
        seq![token_view(tokens[0])] + token_views(tokens.drop_first())
    }
}

pub proof fn token_views_concat(left: Seq<Token>, right: Seq<Token>)
    ensures token_views(left + right) == token_views(left) + token_views(right),
    decreases left.len(),
{
    reveal_with_fuel(token_views, 1);
    if left.len() > 0 {
        token_views_concat(left.drop_first(), right);
        assert((left + right).drop_first() =~= left.drop_first() + right);
    }
}

/// Whether the production literal printer can encode this value directly.
pub open spec fn printable_literal(literal: ast::Literal) -> bool {
    match literal {
        ast::Literal::Null | ast::Literal::Boolean(_) | ast::Literal::String(_) => true,
        ast::Literal::Integer(value) => value >= 0,
        ast::Literal::Float(value) =>
            value.is_finite_spec() && !value.is_sign_negative_spec(),
    }
}

pub open spec fn literal_views(literal: ast::Literal) -> Option<Seq<TokenView>> {
    match literal {
        ast::Literal::Null => Some(seq![TokenView::Keyword(Keyword::Null)]),
        ast::Literal::Boolean(true) => Some(seq![TokenView::Keyword(Keyword::True)]),
        ast::Literal::Boolean(false) => Some(seq![TokenView::Keyword(Keyword::False)]),
        ast::Literal::Integer(value) if value >= 0 => Some(seq![
            TokenView::Number(super::verified_integer::decimal_digits(value as u64)),
        ]),
        ast::Literal::Integer(_) => None,
        ast::Literal::Float(value)
            if value.is_finite_spec() && !value.is_sign_negative_spec() => Some(seq![
                TokenView::Number(float_trust::spec_format(value)),
            ]),
        ast::Literal::Float(_) => None,
        ast::Literal::String(value) => Some(seq![TokenView::String(value)]),
    }
}

pub open spec fn parse_literal_views(tokens: Seq<TokenView>) -> Option<ast::Literal> {
    if tokens.len() != 1 {
        None
    } else {
        match tokens[0] {
            TokenView::Keyword(Keyword::Null) => Some(ast::Literal::Null),
            TokenView::Keyword(Keyword::True) => Some(ast::Literal::Boolean(true)),
            TokenView::Keyword(Keyword::False) => Some(ast::Literal::Boolean(false)),
            TokenView::Number(bytes) => if super::verified_integer::all_digits(bytes) {
                match super::verified_integer::parse_i64_spec(bytes) {
                    Some(value) => Some(ast::Literal::Integer(value)),
                    None => None,
                }
            } else {
                match float_trust::spec_parse(bytes) {
                    Some(value) => Some(ast::Literal::Float(value)),
                    None => None,
                }
            },
            TokenView::String(value) => Some(ast::Literal::String(value)),
            _ => None,
        }
    }
}

pub proof fn literal_roundtrip(literal: ast::Literal)
    requires literal_views(literal).is_some(),
    ensures parse_literal_views(literal_views(literal).unwrap()) == Some(literal),
{
    reveal(literal_views);
    reveal(parse_literal_views);
    match literal {
        ast::Literal::Integer(value) => {
            assert(value >= 0);
            super::verified_integer::print_parse_roundtrip(value);
            super::verified_integer::decimal_digits_are_digits(value as u64);
        },
        ast::Literal::Float(value) => {
            assert(value.is_finite_spec());
            float_trust::axiom_f64_finite_roundtrip(value);
        },
        ast::Literal::Null
        | ast::Literal::Boolean(_)
        | ast::Literal::String(_) => {},
    }
}

} // verus!
