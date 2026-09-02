//! Axiom-free production-AST expression roundtrip core.
//!
//! This module deliberately excludes `Expression::Function`, but not for the
//! reason first assumed. Recursion through a `Vec<Expression>` *does* admit a
//! termination measure (a spec height whose list component decreases on the
//! argument sequence; see `verified_function_list`). The real obstacle is that
//! these roundtrip functions are `spec fn`s, and Verus has no spec-level `Vec`
//! constructor, nor is `Vec` equality determined by its view. A spec parser
//! therefore cannot build or compare a `Function(name, Vec)` node. Parsing
//! functions requires an *executable* parser that builds `Vec`s at runtime,
//! verified against a `Seq`-based mirror; `verified_function_list` is that
//! template. All other production expression forms have direct boxed-child
//! recursion and are verified here against concrete `TokenView` sequences.

#![allow(dead_code)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_production::TokenView;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, ast, float_trust, verified_production};

verus! {

pub open spec fn function_free(e: ast::Expression) -> bool
    decreases e,
{
    match e {
        ast::Expression::Function(_, _) => false,
        ast::Expression::Operator(op) => match op {
            ast::Operator::And(left, right)
            | ast::Operator::Or(left, right)
            | ast::Operator::Equal(left, right)
            | ast::Operator::GreaterThan(left, right)
            | ast::Operator::GreaterThanOrEqual(left, right)
            | ast::Operator::LessThan(left, right)
            | ast::Operator::LessThanOrEqual(left, right)
            | ast::Operator::NotEqual(left, right)
            | ast::Operator::Add(left, right)
            | ast::Operator::Divide(left, right)
            | ast::Operator::Exponentiate(left, right)
            | ast::Operator::Multiply(left, right)
            | ast::Operator::Remainder(left, right)
            | ast::Operator::Subtract(left, right)
            | ast::Operator::Like(left, right) =>
                function_free(*left) && function_free(*right),
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => function_free(*inner),
            ast::Operator::Is(left, _) => function_free(*left),
        },
        _ => true,
    }
}

pub open spec fn printable(e: ast::Expression) -> bool
    decreases e,
{
    function_free(e) && verified_production::printable_expression(e)
}

pub proof fn printable_is_core(expression: ast::Expression)
    ensures printable(expression)
        == verified_production::core_printable_expression(expression),
    decreases expression,
{
    reveal(printable);
    reveal(function_free);
    reveal(verified_production::printable_expression);
    reveal(verified_production::core_printable_expression);
    match expression {
        ast::Expression::Operator(operator) => match operator {
            ast::Operator::And(left, right)
            | ast::Operator::Or(left, right)
            | ast::Operator::Equal(left, right)
            | ast::Operator::GreaterThan(left, right)
            | ast::Operator::GreaterThanOrEqual(left, right)
            | ast::Operator::LessThan(left, right)
            | ast::Operator::LessThanOrEqual(left, right)
            | ast::Operator::NotEqual(left, right)
            | ast::Operator::Add(left, right)
            | ast::Operator::Divide(left, right)
            | ast::Operator::Exponentiate(left, right)
            | ast::Operator::Multiply(left, right)
            | ast::Operator::Remainder(left, right)
            | ast::Operator::Subtract(left, right)
            | ast::Operator::Like(left, right) => {
                printable_is_core(*left);
                printable_is_core(*right);
            },
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner)
            | ast::Operator::Is(inner, _) => printable_is_core(*inner),
        },
        _ => {},
    }
}

pub open spec fn depth(e: ast::Expression) -> nat
    decreases e,
{
    match e {
        ast::Expression::All
        | ast::Expression::Column(_, _)
        | ast::Expression::Literal(_) => 1,
        ast::Expression::Function(_, _) => 0,
        ast::Expression::Operator(op) => match op {
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => 1 + depth(*inner),
            ast::Operator::Is(left, _) => 1 + depth(*left),
            ast::Operator::And(left, right)
            | ast::Operator::Or(left, right)
            | ast::Operator::Equal(left, right)
            | ast::Operator::GreaterThan(left, right)
            | ast::Operator::GreaterThanOrEqual(left, right)
            | ast::Operator::LessThan(left, right)
            | ast::Operator::LessThanOrEqual(left, right)
            | ast::Operator::NotEqual(left, right)
            | ast::Operator::Add(left, right)
            | ast::Operator::Divide(left, right)
            | ast::Operator::Exponentiate(left, right)
            | ast::Operator::Multiply(left, right)
            | ast::Operator::Remainder(left, right)
            | ast::Operator::Subtract(left, right)
            | ast::Operator::Like(left, right) => {
                let left_depth = depth(*left);
                let right_depth = depth(*right);
                1 + if left_depth >= right_depth { left_depth } else { right_depth }
            }
        },
    }
}

pub open spec fn prefix_boundary(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || tail[0] != TokenView::Period
}

pub open spec fn binary_token(op: &ast::Operator) -> Option<TokenView> {
    match op {
        ast::Operator::And(_, _) => Some(TokenView::Keyword(Keyword::And)),
        ast::Operator::Or(_, _) => Some(TokenView::Keyword(Keyword::Or)),
        ast::Operator::Equal(_, _) => Some(TokenView::Equal),
        ast::Operator::GreaterThan(_, _) => Some(TokenView::GreaterThan),
        ast::Operator::GreaterThanOrEqual(_, _) => Some(TokenView::GreaterThanOrEqual),
        ast::Operator::LessThan(_, _) => Some(TokenView::LessThan),
        ast::Operator::LessThanOrEqual(_, _) => Some(TokenView::LessThanOrEqual),
        ast::Operator::NotEqual(_, _) => Some(TokenView::NotEqual),
        ast::Operator::Add(_, _) => Some(TokenView::Plus),
        ast::Operator::Divide(_, _) => Some(TokenView::Slash),
        ast::Operator::Exponentiate(_, _) => Some(TokenView::Caret),
        ast::Operator::Multiply(_, _) => Some(TokenView::Asterisk),
        ast::Operator::Remainder(_, _) => Some(TokenView::Percent),
        ast::Operator::Subtract(_, _) => Some(TokenView::Minus),
        ast::Operator::Like(_, _) => Some(TokenView::Keyword(Keyword::Like)),
        _ => None,
    }
}

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

pub open spec fn unary_token(op: &ast::Operator) -> Option<TokenView> {
    match op {
        ast::Operator::Not(_) => Some(TokenView::Keyword(Keyword::Not)),
        ast::Operator::Identity(_) => Some(TokenView::Plus),
        ast::Operator::Negate(_) => Some(TokenView::Minus),
        _ => None,
    }
}

pub open spec fn print_expr(e: ast::Expression) -> Option<Seq<TokenView>>
    decreases e,
{
    match e {
        ast::Expression::All | ast::Expression::Column(_, _) =>
            verified_production::atom_views(e),
        ast::Expression::Literal(literal) =>
            verified_production::literal_views(literal),
        ast::Expression::Function(_, _) => None,
        ast::Expression::Operator(op) => match op {
            ast::Operator::Not(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => match (unary_token(&op), print_expr(*inner)) {
                (Some(token), Some(inner_tokens)) => Some(
                    seq![TokenView::OpenParen, token] + inner_tokens
                        + seq![TokenView::CloseParen],
                ),
                _ => None,
            },
            ast::Operator::Factorial(inner) => match print_expr(*inner) {
                Some(inner_tokens) => Some(
                    seq![TokenView::OpenParen] + inner_tokens
                        + seq![TokenView::Exclamation, TokenView::CloseParen],
                ),
                None => None,
            },
            ast::Operator::Is(left, literal) => match (print_expr(*left), literal) {
                (Some(left_tokens), ast::Literal::Null) => Some(
                    seq![TokenView::OpenParen] + left_tokens + seq![
                        TokenView::Keyword(Keyword::Is),
                        TokenView::Keyword(Keyword::Null),
                        TokenView::CloseParen,
                    ],
                ),
                (Some(left_tokens), ast::Literal::Float(value))
                    if value.to_bits_spec() == float_trust::CANONICAL_NAN_BITS => Some(
                    seq![TokenView::OpenParen] + left_tokens + seq![
                        TokenView::Keyword(Keyword::Is),
                        TokenView::Keyword(Keyword::NaN),
                        TokenView::CloseParen,
                    ],
                ),
                _ => None,
            },
            ast::Operator::And(left, right)
            | ast::Operator::Or(left, right)
            | ast::Operator::Equal(left, right)
            | ast::Operator::GreaterThan(left, right)
            | ast::Operator::GreaterThanOrEqual(left, right)
            | ast::Operator::LessThan(left, right)
            | ast::Operator::LessThanOrEqual(left, right)
            | ast::Operator::NotEqual(left, right)
            | ast::Operator::Add(left, right)
            | ast::Operator::Divide(left, right)
            | ast::Operator::Exponentiate(left, right)
            | ast::Operator::Multiply(left, right)
            | ast::Operator::Remainder(left, right)
            | ast::Operator::Subtract(left, right)
            | ast::Operator::Like(left, right) => match (binary_token(&op), print_expr(*left), print_expr(*right)) {
                (Some(token), Some(left_tokens), Some(right_tokens)) => Some(
                    seq![TokenView::OpenParen] + left_tokens + seq![token]
                        + right_tokens + seq![TokenView::CloseParen],
                ),
                _ => None,
            },
        },
    }
}

pub open spec fn parse_atom_prefix(input: Seq<TokenView>)
    -> Option<(ast::Expression, Seq<TokenView>)> {
    if input.len() == 0 {
        None
    } else {
        match input[0] {
            TokenView::Asterisk => Some((ast::Expression::All, input.drop_first())),
            TokenView::Ident(name) => {
                if input.len() >= 3 && input[1] == TokenView::Period {
                    match input[2] {
                        TokenView::Ident(column) => Some((
                            ast::Expression::Column(Some(name), column),
                            input.drop_first().drop_first().drop_first(),
                        )),
                        _ => None,
                    }
                } else {
                    Some((ast::Expression::Column(None, name), input.drop_first()))
                }
            }
            TokenView::Number(bytes) => match verified_production::parse_literal_views(
                seq![TokenView::Number(bytes)],
            ) {
                Some(literal) => Some((ast::Expression::Literal(literal), input.drop_first())),
                None => None,
            },
            TokenView::Keyword(Keyword::Null)
            | TokenView::Keyword(Keyword::True)
            | TokenView::Keyword(Keyword::False)
            | TokenView::String(_) => match verified_production::parse_literal_views(
                seq![input[0]],
            ) {
                Some(literal) => Some((ast::Expression::Literal(literal), input.drop_first())),
                None => None,
            },
            _ => None,
        }
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

pub open spec fn unary_operator(tag: UnaryTag, inner: ast::Expression) -> ast::Operator {
    match tag {
        UnaryTag::Identity => ast::Operator::Identity(Box::new(inner)),
        UnaryTag::Negate => ast::Operator::Negate(Box::new(inner)),
        UnaryTag::Not => ast::Operator::Not(Box::new(inner)),
    }
}

pub open spec fn binary_operator(tag: BinaryTag, left: ast::Expression, right: ast::Expression)
    -> ast::Operator {
    match tag {
        BinaryTag::And => ast::Operator::And(Box::new(left), Box::new(right)),
        BinaryTag::Or => ast::Operator::Or(Box::new(left), Box::new(right)),
        BinaryTag::Equal => ast::Operator::Equal(Box::new(left), Box::new(right)),
        BinaryTag::GreaterThan => ast::Operator::GreaterThan(Box::new(left), Box::new(right)),
        BinaryTag::GreaterThanOrEqual =>
            ast::Operator::GreaterThanOrEqual(Box::new(left), Box::new(right)),
        BinaryTag::LessThan => ast::Operator::LessThan(Box::new(left), Box::new(right)),
        BinaryTag::LessThanOrEqual =>
            ast::Operator::LessThanOrEqual(Box::new(left), Box::new(right)),
        BinaryTag::NotEqual => ast::Operator::NotEqual(Box::new(left), Box::new(right)),
        BinaryTag::Add => ast::Operator::Add(Box::new(left), Box::new(right)),
        BinaryTag::Divide => ast::Operator::Divide(Box::new(left), Box::new(right)),
        BinaryTag::Exponentiate =>
            ast::Operator::Exponentiate(Box::new(left), Box::new(right)),
        BinaryTag::Multiply => ast::Operator::Multiply(Box::new(left), Box::new(right)),
        BinaryTag::Remainder => ast::Operator::Remainder(Box::new(left), Box::new(right)),
        BinaryTag::Subtract => ast::Operator::Subtract(Box::new(left), Box::new(right)),
        BinaryTag::Like => ast::Operator::Like(Box::new(left), Box::new(right)),
    }
}

pub open spec fn parse_prefix(input: Seq<TokenView>, fuel: nat)
    -> (Option<ast::Expression>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::OpenParen => {
                if input.len() < 2 {
                    (None, input)
                } else {
                    match prefix_operator(input[1]) {
                        Some(tag) => {
                            let inner = parse_prefix(
                                input.drop_first().drop_first(),
                                (fuel - 1) as nat,
                            );
                            match inner {
                                (Some(expression), rest)
                                    if rest.len() > 0 && rest[0] == TokenView::CloseParen => (
                                    Some(ast::Expression::Operator(
                                        unary_operator(tag, expression),
                                    )),
                                    rest.drop_first(),
                                ),
                                _ => (None, input),
                            }
                        }
                        None => {
                            let left = parse_prefix(input.drop_first(), (fuel - 1) as nat);
                            match left {
                                (Some(left), after_left) if after_left.len() > 0 => {
                                    if after_left[0] == TokenView::Exclamation {
                                        if after_left.len() > 1
                                            && after_left[1] == TokenView::CloseParen
                                        {
                                            (
                                                Some(ast::Expression::Operator(
                                                    ast::Operator::Factorial(Box::new(left)),
                                                )),
                                                after_left.drop_first().drop_first(),
                                            )
                                        } else {
                                            (None, input)
                                        }
                                    } else if after_left[0]
                                        == TokenView::Keyword(Keyword::Is)
                                    {
                                        if after_left.len() >= 3
                                            && after_left[2] == TokenView::CloseParen
                                        {
                                            let literal = match after_left[1] {
                                                TokenView::Keyword(Keyword::Null) => {
                                                    Some(ast::Literal::Null)
                                                }
                                                TokenView::Keyword(Keyword::NaN) => Some(
                                                    ast::Literal::Float(
                                                        float_trust::spec_canonical_nan(),
                                                    ),
                                                ),
                                                _ => None,
                                            };
                                            match literal {
                                                Some(literal) => (
                                                    Some(ast::Expression::Operator(
                                                        ast::Operator::Is(Box::new(left), literal),
                                                    )),
                                                    after_left
                                                        .drop_first()
                                                        .drop_first()
                                                        .drop_first(),
                                                ),
                                                None => (None, input),
                                            }
                                        } else {
                                            (None, input)
                                        }
                                    } else {
                                        match binary_from_token(after_left[0]) {
                                            Some(tag) => {
                                                let right = parse_prefix(
                                                    after_left.drop_first(),
                                                    (fuel - 1) as nat,
                                                );
                                                match right {
                                                    (Some(right), rest)
                                                        if rest.len() > 0
                                                            && rest[0] == TokenView::CloseParen => (
                                                            Some(ast::Expression::Operator(
                                                                binary_operator(tag, left, right),
                                                            )),
                                                            rest.drop_first(),
                                                        ),
                                                    _ => (None, input),
                                                }
                                            }
                                            None => (None, input),
                                        }
                                    }
                                }
                                _ => (None, input),
                            }
                        }
                    }
                }
            }
            _ => match parse_atom_prefix(input) {
                Some((expression, rest)) => (Some(expression), rest),
                None => (None, input),
            },
        }
    }
}

proof fn lemma_parse_atom_prefix(
    expression: ast::Expression,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        fuel > 0,
        verified_production::atom_views(expression).is_some(),
        prefix_boundary(tail),
    ensures parse_prefix(
        verified_production::atom_views(expression).unwrap() + tail,
        fuel,
    ) == (Some(expression), tail),
{
    reveal_with_fuel(parse_prefix, 1);
    reveal(parse_atom_prefix);
    reveal(verified_production::atom_views);
    assert(fuel != 0);
    match expression {
        ast::Expression::All => {
            let tokens = seq![TokenView::Asterisk] + tail;
            assert(tokens.len() > 0);
            assert(tokens[0] == TokenView::Asterisk);
            assert(tokens.drop_first() =~= tail);
            assert(parse_atom_prefix(tokens) == Some((ast::Expression::All, tail)));
            assert(parse_prefix(tokens, fuel) == (Some(ast::Expression::All), tail));
        },
        ast::Expression::Column(None, column) => {
            let tokens = seq![TokenView::Ident(column)] + tail;
            assert(tokens.len() > 0);
            assert(tokens[0] == TokenView::Ident(column));
            assert(tokens.drop_first() =~= tail);
            assert(parse_atom_prefix(tokens)
                == Some((ast::Expression::Column(None, column), tail)));
            assert(parse_prefix(tokens, fuel)
                == (Some(ast::Expression::Column(None, column)), tail));
        },
        ast::Expression::Column(Some(table), column) => {
            let tokens = seq![
                TokenView::Ident(table),
                TokenView::Period,
                TokenView::Ident(column),
            ] + tail;
            assert(tokens.len() >= 3);
            assert(tokens[0] == TokenView::Ident(table));
            assert(tokens[1] == TokenView::Period);
            assert(tokens[2] == TokenView::Ident(column));
            assert(tokens.drop_first().drop_first().drop_first() =~= tail);
            assert(parse_atom_prefix(tokens)
                == Some((ast::Expression::Column(Some(table), column), tail)));
            assert(parse_prefix(tokens, fuel)
                == (Some(ast::Expression::Column(Some(table), column)), tail));
        },
        _ => assert(false),
    }
}

proof fn lemma_parse_literal_prefix(
    literal: ast::Literal,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        fuel > 0,
        verified_production::literal_views(literal).is_some(),
    ensures parse_prefix(
        verified_production::literal_views(literal).unwrap() + tail,
        fuel,
    ) == (Some(ast::Expression::Literal(literal)), tail),
{
    verified_production::literal_roundtrip(literal);
    reveal_with_fuel(parse_prefix, 1);
    reveal(parse_atom_prefix);
    reveal(verified_production::literal_views);
    match literal {
        ast::Literal::Null
        | ast::Literal::Boolean(_)
        | ast::Literal::Integer(_)
        | ast::Literal::Float(_)
        | ast::Literal::String(_) => {
            let tokens = verified_production::literal_views(literal).unwrap() + tail;
            assert(tokens.drop_first() =~= tail);
        },
    }
}

#[verifier::rlimit(1000)]
pub proof fn lemma_parse_print_prefix(
    expression: &ast::Expression,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        printable(*expression),
        fuel >= depth(*expression),
        prefix_boundary(tail),
    ensures
        print_expr(*expression).is_some(),
        parse_prefix(print_expr(*expression).unwrap() + tail, fuel)
            == (Some(*expression), tail),
    decreases *expression,
{
    reveal(printable);
    reveal(function_free);
    reveal(depth);
    reveal(print_expr);
    reveal_with_fuel(parse_prefix, 1);

    match expression {
        ast::Expression::All | ast::Expression::Column(_, _) => {
            lemma_parse_atom_prefix(*expression, tail, fuel);
        },
        ast::Expression::Literal(literal) => {
            lemma_parse_literal_prefix(*literal, tail, fuel);
        },
        ast::Expression::Function(_, _) => assert(false),
        ast::Expression::Operator(operator) => match operator {
            ast::Operator::Not(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => {
                let token = unary_token(operator).unwrap();
                let inner_tail = seq![TokenView::CloseParen] + tail;
                lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                assert((print_expr(*expression).unwrap() + tail)
                    .drop_first().drop_first()
                    =~= print_expr(**inner).unwrap() + inner_tail);
                assert(inner_tail.drop_first() =~= tail);
                match operator {
                    ast::Operator::Not(_) => {
                        assert(prefix_operator(token) == Some(UnaryTag::Not));
                        assert(unary_operator(UnaryTag::Not, **inner) == *operator);
                    },
                    ast::Operator::Identity(_) => {
                        assert(prefix_operator(token) == Some(UnaryTag::Identity));
                        assert(unary_operator(UnaryTag::Identity, **inner) == *operator);
                    },
                    ast::Operator::Negate(_) => {
                        assert(prefix_operator(token) == Some(UnaryTag::Negate));
                        assert(unary_operator(UnaryTag::Negate, **inner) == *operator);
                    },
                    _ => assert(false),
                }
            },
            ast::Operator::Factorial(inner) => {
                let inner_tail = seq![TokenView::Exclamation, TokenView::CloseParen] + tail;
                lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                assert((print_expr(*expression).unwrap() + tail).drop_first()
                    =~= print_expr(**inner).unwrap() + inner_tail);
                assert(inner_tail.drop_first().drop_first() =~= tail);
            },
            ast::Operator::Is(inner, literal) => {
                let value_token = match literal {
                    ast::Literal::Null => TokenView::Keyword(Keyword::Null),
                    ast::Literal::Float(_) => TokenView::Keyword(Keyword::NaN),
                    _ => { assert(false); TokenView::Keyword(Keyword::Null) },
                };
                let inner_tail = seq![
                    TokenView::Keyword(Keyword::Is),
                    value_token,
                    TokenView::CloseParen,
                ] + tail;
                lemma_parse_print_prefix(inner, inner_tail, (fuel - 1) as nat);
                assert((print_expr(*expression).unwrap() + tail).drop_first()
                    =~= print_expr(**inner).unwrap() + inner_tail);
                assert(inner_tail.drop_first().drop_first().drop_first() =~= tail);
                match literal {
                    ast::Literal::Null => {},
                    ast::Literal::Float(value) => {
                        float_trust::axiom_canonical_nan(*value);
                    },
                    _ => assert(false),
                }
            },
            ast::Operator::And(left, right)
            | ast::Operator::Or(left, right)
            | ast::Operator::Equal(left, right)
            | ast::Operator::GreaterThan(left, right)
            | ast::Operator::GreaterThanOrEqual(left, right)
            | ast::Operator::LessThan(left, right)
            | ast::Operator::LessThanOrEqual(left, right)
            | ast::Operator::NotEqual(left, right)
            | ast::Operator::Add(left, right)
            | ast::Operator::Divide(left, right)
            | ast::Operator::Exponentiate(left, right)
            | ast::Operator::Multiply(left, right)
            | ast::Operator::Remainder(left, right)
            | ast::Operator::Subtract(left, right)
            | ast::Operator::Like(left, right) => {
                let token = binary_token(operator).unwrap();
                let right_tail = seq![TokenView::CloseParen] + tail;
                let left_tail = seq![token] + print_expr(**right).unwrap() + right_tail;
                lemma_parse_print_prefix(left, left_tail, (fuel - 1) as nat);
                lemma_parse_print_prefix(right, right_tail, (fuel - 1) as nat);
                assert((print_expr(*expression).unwrap() + tail).drop_first()
                    =~= print_expr(**left).unwrap() + left_tail);
                assert(left_tail.drop_first() =~= print_expr(**right).unwrap() + right_tail);
                assert(right_tail.drop_first() =~= tail);
                let tag = binary_from_token(token).unwrap();
                match operator {
                    ast::Operator::And(_, _) => assert(tag == BinaryTag::And),
                    ast::Operator::Or(_, _) => assert(tag == BinaryTag::Or),
                    ast::Operator::Equal(_, _) => assert(tag == BinaryTag::Equal),
                    ast::Operator::GreaterThan(_, _) => assert(tag == BinaryTag::GreaterThan),
                    ast::Operator::GreaterThanOrEqual(_, _) =>
                        assert(tag == BinaryTag::GreaterThanOrEqual),
                    ast::Operator::LessThan(_, _) => assert(tag == BinaryTag::LessThan),
                    ast::Operator::LessThanOrEqual(_, _) =>
                        assert(tag == BinaryTag::LessThanOrEqual),
                    ast::Operator::NotEqual(_, _) => assert(tag == BinaryTag::NotEqual),
                    ast::Operator::Add(_, _) => assert(tag == BinaryTag::Add),
                    ast::Operator::Divide(_, _) => assert(tag == BinaryTag::Divide),
                    ast::Operator::Exponentiate(_, _) => assert(tag == BinaryTag::Exponentiate),
                    ast::Operator::Multiply(_, _) => assert(tag == BinaryTag::Multiply),
                    ast::Operator::Remainder(_, _) => assert(tag == BinaryTag::Remainder),
                    ast::Operator::Subtract(_, _) => assert(tag == BinaryTag::Subtract),
                    ast::Operator::Like(_, _) => assert(tag == BinaryTag::Like),
                    _ => assert(false),
                }
                assert(binary_operator(tag, **left, **right) == *operator);
            },
        },
    }
}

/// Canonical token roundtrip for every function-free production expression.
pub proof fn print_parse_roundtrip(expression: ast::Expression)
    requires printable(expression),
    ensures parse_prefix(print_expr(expression).unwrap(), depth(expression))
        == (Some(expression), Seq::empty()),
{
    lemma_parse_print_prefix(&expression, Seq::empty(), depth(expression));
}

/// The canonical printer is injective on its function-free production domain.
pub proof fn print_expr_injective(left: ast::Expression, right: ast::Expression)
    requires printable(left), printable(right),
    ensures print_expr(left) == print_expr(right) ==> left == right,
{
    if print_expr(left) == print_expr(right) {
        let fuel = if depth(left) >= depth(right) { depth(left) } else { depth(right) };
        lemma_parse_print_prefix(&left, Seq::empty(), fuel);
        lemma_parse_print_prefix(&right, Seq::empty(), fuel);
        assert(Some(left) == Some(right));
    }
}

}
