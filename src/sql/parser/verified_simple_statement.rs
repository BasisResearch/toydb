//! Roundtrip proof for list-free statements over the production AST.

#![allow(dead_code)]

use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::{Keyword, ast, verified_production};

verus! {

pub open spec fn print_statement(statement: ast::Statement) -> Option<Seq<TokenView>>
    decreases statement,
{
    match statement {
        ast::Statement::Begin { .. } => verified_production::begin_views(statement),
        ast::Statement::Commit => Some(seq![TokenView::Keyword(Keyword::Commit)]),
        ast::Statement::Rollback => Some(seq![TokenView::Keyword(Keyword::Rollback)]),
        ast::Statement::DropTable { name, if_exists: false } => Some(seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Ident(name),
        ]),
        ast::Statement::DropTable { name, if_exists: true } => Some(seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Keyword(Keyword::If),
            TokenView::Keyword(Keyword::Exists),
            TokenView::Ident(name),
        ]),
        ast::Statement::Delete { .. } => verified_production::delete_views(statement),
        ast::Statement::Explain(inner) if !matches!(*inner, ast::Statement::Explain(_)) => {
            match print_statement(*inner) {
                Some(tokens) => Some(seq![TokenView::Keyword(Keyword::Explain)] + tokens),
                None => None,
            }
        },
        _ => None,
    }
}

pub open spec fn statement_fuel(statement: ast::Statement) -> nat
    decreases statement,
{
    match statement {
        ast::Statement::Delete { .. } => 1 + verified_production::delete_fuel(statement),
        ast::Statement::Explain(inner) => 1 + statement_fuel(*inner),
        _ => 1,
    }
}

pub open spec fn parse_statement(tokens: Seq<TokenView>, fuel: nat)
    -> Option<ast::Statement>
    decreases fuel,
{
    if fuel == 0 || tokens.len() == 0 {
        None
    } else {
        match tokens[0] {
            TokenView::Keyword(Keyword::Begin) =>
                verified_production::parse_begin_views(tokens),
            TokenView::Keyword(Keyword::Commit) if tokens.len() == 1 =>
                Some(ast::Statement::Commit),
            TokenView::Keyword(Keyword::Rollback) if tokens.len() == 1 =>
                Some(ast::Statement::Rollback),
            TokenView::Keyword(Keyword::Drop) => {
                if tokens.len() == 3
                    && tokens[1] == TokenView::Keyword(Keyword::Table)
                {
                    match tokens[2] {
                        TokenView::Ident(name) => Some(
                            ast::Statement::DropTable { name, if_exists: false },
                        ),
                        _ => None,
                    }
                } else if tokens.len() == 5
                    && tokens[1] == TokenView::Keyword(Keyword::Table)
                    && tokens[2] == TokenView::Keyword(Keyword::If)
                    && tokens[3] == TokenView::Keyword(Keyword::Exists)
                {
                    match tokens[4] {
                        TokenView::Ident(name) => Some(
                            ast::Statement::DropTable { name, if_exists: true },
                        ),
                        _ => None,
                    }
                } else {
                    None
                }
            },
            TokenView::Keyword(Keyword::Delete) =>
                verified_production::parse_delete_views(tokens, fuel),
            TokenView::Keyword(Keyword::Explain) => {
                match parse_statement(tokens.drop_first(), (fuel - 1) as nat) {
                    Some(inner) => Some(ast::Statement::Explain(Box::new(inner))),
                    None => None,
                }
            },
            _ => None,
        }
    }
}

proof fn parse_with_fuel(statement: ast::Statement, fuel: nat)
    requires
        print_statement(statement).is_some(),
        fuel >= statement_fuel(statement),
    ensures parse_statement(print_statement(statement).unwrap(), fuel) == Some(statement),
    decreases statement,
{
    reveal(print_statement);
    reveal(statement_fuel);
    reveal_with_fuel(parse_statement, 1);
    match statement {
        ast::Statement::Begin { .. } => {
            verified_production::begin_roundtrip(statement);
        },
        ast::Statement::Commit | ast::Statement::Rollback => {},
        ast::Statement::DropTable { .. } => {},
        ast::Statement::Delete { .. } => {
            verified_production::delete_parse_with_fuel(statement, fuel);
        },
        ast::Statement::Explain(inner) => {
            parse_with_fuel(*inner, (fuel - 1) as nat);
            let inner_tokens = print_statement(*inner).unwrap();
            let tokens = seq![TokenView::Keyword(Keyword::Explain)] + inner_tokens;
            assert(tokens.drop_first() =~= inner_tokens);
        },
        _ => assert(false),
    }
}

pub proof fn print_parse_roundtrip(statement: ast::Statement)
    requires print_statement(statement).is_some(),
    ensures parse_statement(print_statement(statement).unwrap(), statement_fuel(statement))
        == Some(statement),
{
    parse_with_fuel(statement, statement_fuel(statement));
}

pub proof fn print_statement_injective(left: ast::Statement, right: ast::Statement)
    requires
        print_statement(left).is_some(),
        print_statement(right).is_some(),
        print_statement(left) == print_statement(right),
    ensures left == right,
{
    let fuel = if statement_fuel(left) >= statement_fuel(right) {
        statement_fuel(left)
    } else {
        statement_fuel(right)
    };
    parse_with_fuel(left, fuel);
    parse_with_fuel(right, fuel);
}

}
