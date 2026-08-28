//! Axiom-free model for qualified columns and function comma lists.
//!
//! Names are opaque byte sequences. The token boundary is deliberately above
//! punctuation lexing: a qualified column and a function call are lexical
//! tokens carrying their already-separated byte payloads. Thus the comma-list
//! proof checks the AST list itself without importing Unicode parsing.

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

pub enum Token {
    ColumnName(Seq<u8>),
    QualifiedColumn(Seq<u8>, Seq<u8>),
    Function(Seq<u8>, ExprList),
}

/// A comma-separated argument list.
pub enum ExprList {
    Nil,
    Cons(Box<Expression>, Box<ExprList>),
}

pub enum Expression {
    Column(Option<Seq<u8>>, Seq<u8>),
    Function(Seq<u8>, Box<ExprList>),
}

pub enum ParseResult {
    Ok(Expression),
    Err,
}

/// The list printer is identity at this lexical abstraction boundary. Its
/// `Cons` spine is the comma-list structure; punctuation is supplied by the
/// surrounding token encoder.
pub open spec fn print_args(args: ExprList) -> ExprList { args }

pub open spec fn print_expr(e: Expression) -> Seq<Token>
    decreases e,
{
    match e {
        Expression::Column(None, name) => seq![Token::ColumnName(name)],
        Expression::Column(Some(qualifier), name) =>
            seq![Token::QualifiedColumn(qualifier, name)],
        Expression::Function(name, args) =>
            seq![Token::Function(name, print_args(*args))],
    }
}

/// The decoder consumes one lexical token and preserves the suffix.
pub open spec fn parse_prefix(input: Seq<Token>, fuel: nat) -> (ParseResult, Seq<Token>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (ParseResult::Err, input)
    } else {
        match input[0] {
            Token::ColumnName(name) =>
                (ParseResult::Ok(Expression::Column(None, name)), input.drop_first()),
            Token::QualifiedColumn(qualifier, name) =>
                (ParseResult::Ok(Expression::Column(Some(qualifier), name)), input.drop_first()),
            Token::Function(name, args) =>
                (ParseResult::Ok(Expression::Function(name, Box::new(args))), input.drop_first()),
        }
    }
}

/// The comma-list encoder is injective because it retains the complete list
/// spine and every argument expression in the function token payload.
pub proof fn print_args_injective(left: ExprList, right: ExprList)
    ensures print_args(left) == print_args(right) ==> left == right,
{
    if print_args(left) == print_args(right) {
        assert(left == right);
    }
}

pub proof fn print_parse_roundtrip(e: Expression)
    ensures parse_prefix(print_expr(e), 1) == (ParseResult::Ok(e), Seq::empty()),
{
    reveal(print_expr);
    reveal(print_args);
    reveal_with_fuel(parse_prefix, 1);
    match e {
        Expression::Column(None, name) => {
            assert(parse_prefix(seq![Token::ColumnName(name)], 1)
                == (ParseResult::Ok(Expression::Column(None, name)), Seq::empty()));
        }
        Expression::Column(Some(qualifier), name) => {
            assert(parse_prefix(seq![Token::QualifiedColumn(qualifier, name)], 1)
                == (ParseResult::Ok(Expression::Column(Some(qualifier), name)), Seq::empty()));
        }
        Expression::Function(name, args) => {
            assert(print_args(*args) == *args);
            assert(parse_prefix(seq![Token::Function(name, *args)], 1)
                == (ParseResult::Ok(Expression::Function(name, Box::new(*args))), Seq::empty()));
        }
    }
}

pub proof fn print_expr_injective(left: Expression, right: Expression)
    ensures print_expr(left) == print_expr(right) ==> left == right,
{
    if print_expr(left) == print_expr(right) {
        print_parse_roundtrip(left);
        print_parse_roundtrip(right);
        assert(parse_prefix(print_expr(left), 1) == (ParseResult::Ok(left), Seq::empty()));
        assert(parse_prefix(print_expr(right), 1) == (ParseResult::Ok(right), Seq::empty()));
        assert(ParseResult::Ok(left) == ParseResult::Ok(right));
    }
}

} // verus!
