//! Canonical token printer for parser-producible expressions.
//!
//! The printer deliberately emits a fully parenthesized form.  This keeps the
//! token-level roundtrip structural and avoids depending on the parser's
//! precedence table.

use vstd::prelude::*;

use super::{Keyword, Token, ast, float_trust, verified_integer};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{verified_expression, verified_production, verified_simple_statement};

verus! {

fn print_atom_expression(expression: &ast::Expression) -> (r: Option<Vec<Token>>)
    ensures match verified_production::atom_views(*expression) {
        Some(views) => r.is_some()
            && verified_production::token_views(r.unwrap()@) == views,
        None => r.is_none(),
    },
{
    let result = match expression {
        ast::Expression::All => Some(vec![Token::Asterisk]),
        ast::Expression::Column(table, column) => {
            let mut tokens = Vec::new();
            if let Some(table) = table {
                tokens.push(Token::Ident(table.clone()));
                tokens.push(Token::Period);
            }
            tokens.push(Token::Ident(column.clone()));
            Some(tokens)
        }
        _ => None,
    };
    proof {
        reveal(verified_production::atom_views);
        reveal(verified_production::token_view);
        reveal_with_fuel(verified_production::token_views, 4);
    }
    result
}

} // verus!

/// Prints an expression in the canonical token format.
///
/// Returns `None` for AST shapes this printer cannot emit as tokens that
/// re-parse to the same expression.  Note that some of these shapes *are*
/// reachable from the parser — `None` marks "no canonical token form", not
/// "unparseable".  Specifically:
///
/// * A negative integer or float literal: the leading sign is a separate parser
///   operator, never part of a `Number` token, so the bare literal has no
///   canonical form here.
/// * A non-finite float (`INFINITY`, `NAN`): these parse from keywords of the
///   same name into `Literal::Float`, but `is_printable_f64` rejects them, as
///   they have no canonical decimal `Number` token.
/// * An `IS` comparison against a literal other than `NULL` or the canonical
///   `NaN`.
pub fn print_expr(expression: &ast::Expression) -> Option<Vec<Token>> {
    match expression {
        ast::Expression::All | ast::Expression::Column(_, _) => print_atom_expression(expression),
        ast::Expression::Literal(literal) => print_literal(literal),
        ast::Expression::Function(name, arguments) => {
            let mut tokens = vec![Token::Ident(name.clone()), Token::OpenParen];
            let mut index = 0;
            while index < arguments.len() {
                if index != 0 {
                    tokens.push(Token::Comma);
                }
                let mut argument_tokens = print_expr(&arguments[index])?;
                tokens.append(&mut argument_tokens);
                index += 1;
            }
            tokens.push(Token::CloseParen);
            Some(tokens)
        }
        ast::Expression::Operator(operator) => {
            print_core_expr(expression).or_else(|| print_operator(operator))
        }
    }
}

verus! {

fn print_literal(literal: &ast::Literal) -> (r: Option<Vec<Token>>)
    ensures
        r.is_some() <==> verified_production::printable_literal(*literal),
        match verified_production::literal_views(*literal) {
            Some(views) => r.is_some()
                && verified_production::token_views(r.unwrap()@) == views,
            None => r.is_none(),
        },
{
    proof {
        reveal(verified_production::literal_views);
        reveal(verified_production::token_view);
        reveal_with_fuel(verified_production::token_views, 2);
    }
    Some(match literal {
        ast::Literal::Null => vec![Token::Keyword(Keyword::Null)],
        ast::Literal::Boolean(value) => {
            vec![Token::Keyword(if *value { Keyword::True } else { Keyword::False })]
        }
        // A leading sign is a parser operator, not part of a Number token.
        ast::Literal::Integer(value) if *value >= 0 => {
            let bytes = verified_integer::print_i64(*value);
            vec![Token::Number(bytes)]
        }
        ast::Literal::Integer(_) => return None,
        // The trusted canonical formatter retains the decimal point for
        // integral floating-point values.
        ast::Literal::Float(value) if float_trust::is_printable_f64(*value) => {
            let bytes = float_trust::format_f64(*value);
            vec![Token::Number(bytes)]
        }
        ast::Literal::Float(_) => return None,
        ast::Literal::String(value) => vec![Token::String(value.clone())],
    })
}

} // verus!

verus! {

fn print_control_statement(statement: &ast::Statement) -> (r: Option<Vec<Token>>)
    ensures match verified_production::control_tokens(*statement) {
        Some(tokens) => r.is_some() && r.unwrap()@ == tokens,
        None => r.is_none(),
    },
{
    match statement {
        ast::Statement::Commit => Some(vec![Token::Keyword(Keyword::Commit)]),
        ast::Statement::Rollback => Some(vec![Token::Keyword(Keyword::Rollback)]),
        _ => None,
    }
}

fn print_drop_table(statement: &ast::Statement) -> (r: Option<Vec<Token>>)
    ensures match verified_production::drop_table_tokens(*statement) {
        Some(tokens) => r.is_some() && r.unwrap()@ == tokens,
        None => r.is_none(),
    },
{
    match statement {
        ast::Statement::DropTable { name, if_exists } => {
            let mut tokens = vec![
                Token::Keyword(Keyword::Drop),
                Token::Keyword(Keyword::Table),
            ];
            if *if_exists {
                tokens.push(Token::Keyword(Keyword::If));
                tokens.push(Token::Keyword(Keyword::Exists));
            }
            tokens.push(Token::Ident(name.clone()));
            Some(tokens)
        }
        _ => None,
    }
}

fn print_begin(statement: &ast::Statement) -> (r: Option<Vec<Token>>)
    ensures match verified_production::begin_views(*statement) {
        Some(views) => r.is_some()
            && verified_production::token_views(r.unwrap()@) == views,
        None => r.is_none(),
    },
{
    match statement {
        ast::Statement::Begin { read_only, as_of } => {
            let mut tokens = vec![Token::Keyword(Keyword::Begin)];
            if *read_only {
                tokens.push(Token::Keyword(Keyword::Read));
                tokens.push(Token::Keyword(Keyword::Only));
            }
            if let Some(version) = as_of {
                tokens.push(Token::Keyword(Keyword::As));
                tokens.push(Token::Keyword(Keyword::Of));
                tokens.push(Token::Keyword(Keyword::System));
                tokens.push(Token::Keyword(Keyword::Time));
                tokens.push(Token::Number(verified_integer::print_u64(*version)));
            }
            proof {
                reveal(verified_production::begin_views);
                reveal(verified_production::token_view);
                reveal_with_fuel(verified_production::token_views, 10);
            }
            Some(tokens)
        }
        _ => None,
    }
}

} // verus!

verus! {

fn core_binary(lhs_input: Vec<Token>, token: Token, rhs_input: Vec<Token>) -> (r: Vec<Token>)
    ensures verified_production::token_views(r@) ==
        seq![verified_production::TokenView::OpenParen]
            + verified_production::token_views(lhs_input@)
            + seq![verified_production::token_view(token)]
            + verified_production::token_views(rhs_input@)
            + seq![verified_production::TokenView::CloseParen],
{
    let ghost lhs_view = lhs_input@;
    let ghost rhs_view = rhs_input@;
    let mut lhs = lhs_input;
    let mut rhs = rhs_input;
    let mut tokens = vec![Token::OpenParen];
    tokens.append(&mut lhs);
    tokens.push(token);
    tokens.append(&mut rhs);
    tokens.push(Token::CloseParen);
    proof {
        assert(tokens@ =~= seq![Token::OpenParen] + lhs_view + seq![token]
            + rhs_view + seq![Token::CloseParen]);
        verified_production::token_views_concat(seq![Token::OpenParen], lhs_view);
        verified_production::token_views_concat(
            seq![Token::OpenParen] + lhs_view,
            seq![token],
        );
        verified_production::token_views_concat(
            seq![Token::OpenParen] + lhs_view + seq![token],
            rhs_view,
        );
        verified_production::token_views_concat(
            seq![Token::OpenParen] + lhs_view + seq![token] + rhs_view,
            seq![Token::CloseParen],
        );
        reveal_with_fuel(verified_production::token_views, 2);
        reveal(verified_production::token_view);
        assert(verified_production::token_views(tokens@) ==
            seq![verified_production::TokenView::OpenParen]
                + verified_production::token_views(lhs_view)
                + seq![verified_production::token_view(token)]
                + verified_production::token_views(rhs_view)
                + seq![verified_production::TokenView::CloseParen]);
    }
    tokens
}

fn core_unary(token: Token, expression_input: Vec<Token>) -> (r: Vec<Token>)
    ensures verified_production::token_views(r@) == seq![
        verified_production::TokenView::OpenParen,
        verified_production::token_view(token),
    ] + verified_production::token_views(expression_input@)
        + seq![verified_production::TokenView::CloseParen],
{
    let ghost expression_view = expression_input@;
    let mut expression = expression_input;
    let mut tokens = vec![Token::OpenParen, token];
    tokens.append(&mut expression);
    tokens.push(Token::CloseParen);
    proof {
        assert(tokens@ =~= seq![Token::OpenParen, token] + expression_view
            + seq![Token::CloseParen]);
        verified_production::token_views_concat(seq![Token::OpenParen, token], expression_view);
        verified_production::token_views_concat(
            seq![Token::OpenParen, token] + expression_view,
            seq![Token::CloseParen],
        );
        reveal_with_fuel(verified_production::token_views, 3);
        reveal(verified_production::token_view);
        assert(verified_production::token_views(tokens@) == seq![
            verified_production::TokenView::OpenParen,
            verified_production::token_view(token),
        ] + verified_production::token_views(expression_view)
            + seq![verified_production::TokenView::CloseParen]);
    }
    tokens
}

fn core_postfix(expression_input: Vec<Token>, token: Token) -> (r: Vec<Token>)
    ensures verified_production::token_views(r@) ==
        seq![verified_production::TokenView::OpenParen]
            + verified_production::token_views(expression_input@)
            + seq![
                verified_production::token_view(token),
                verified_production::TokenView::CloseParen,
            ],
{
    let ghost expression_view = expression_input@;
    let mut expression = expression_input;
    let mut tokens = vec![Token::OpenParen];
    tokens.append(&mut expression);
    tokens.push(token);
    tokens.push(Token::CloseParen);
    proof {
        assert(tokens@ =~= seq![Token::OpenParen] + expression_view
            + seq![token, Token::CloseParen]);
        verified_production::token_views_concat(seq![Token::OpenParen], expression_view);
        verified_production::token_views_concat(
            seq![Token::OpenParen] + expression_view,
            seq![token, Token::CloseParen],
        );
        reveal_with_fuel(verified_production::token_views, 3);
        reveal(verified_production::token_view);
        assert(verified_production::token_views(tokens@) ==
            seq![verified_production::TokenView::OpenParen]
                + verified_production::token_views(expression_view)
                + seq![
                    verified_production::token_view(token),
                    verified_production::TokenView::CloseParen,
                ]);
    }
    tokens
}

fn core_is(expression_input: Vec<Token>, value: Token) -> (r: Vec<Token>)
    ensures verified_production::token_views(r@) ==
        seq![verified_production::TokenView::OpenParen]
            + verified_production::token_views(expression_input@)
            + seq![
                verified_production::TokenView::Keyword(Keyword::Is),
                verified_production::token_view(value),
                verified_production::TokenView::CloseParen,
            ],
{
    let ghost expression_view = expression_input@;
    let mut expression = expression_input;
    let mut tokens = vec![Token::OpenParen];
    tokens.append(&mut expression);
    tokens.push(Token::Keyword(Keyword::Is));
    tokens.push(value);
    tokens.push(Token::CloseParen);
    proof {
        assert(tokens@ =~= seq![Token::OpenParen] + expression_view + seq![
            Token::Keyword(Keyword::Is), value, Token::CloseParen,
        ]);
        verified_production::token_views_concat(seq![Token::OpenParen], expression_view);
        verified_production::token_views_concat(
            seq![Token::OpenParen] + expression_view,
            seq![Token::Keyword(Keyword::Is), value, Token::CloseParen],
        );
        reveal_with_fuel(verified_production::token_views, 4);
        reveal(verified_production::token_view);
        assert(verified_production::token_views(tokens@) ==
            seq![verified_production::TokenView::OpenParen]
                + verified_production::token_views(expression_view)
                + seq![
                    verified_production::TokenView::Keyword(Keyword::Is),
                    verified_production::token_view(value),
                    verified_production::TokenView::CloseParen,
                ]);
    }
    tokens
}

/// Verified executable printer for expression trees without function nodes.
#[verifier::rlimit(2000)]
fn print_core_expr(expression: &ast::Expression) -> (r: Option<Vec<Token>>)
    ensures
        r.is_some() <==> verified_production::core_printable_expression(*expression),
        match verified_expression::print_expr(*expression) {
            Some(views) => r.is_some()
                && verified_production::token_views(r.unwrap()@) == views,
            None => r.is_none(),
        },
    decreases expression,
{
    use ast::Operator::*;

    match expression {
        ast::Expression::All | ast::Expression::Column(_, _) => print_atom_expression(expression),
        ast::Expression::Literal(literal) => print_literal(literal),
        ast::Expression::Function(_, _) => None,
        ast::Expression::Operator(operator) => Some(match operator {
            And(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::Keyword(Keyword::And),
                print_core_expr(rhs)?,
            ),
            Not(inner) => core_unary(Token::Keyword(Keyword::Not), print_core_expr(inner)?),
            Or(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::Keyword(Keyword::Or),
                print_core_expr(rhs)?,
            ),
            Equal(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Equal, print_core_expr(rhs)?),
            GreaterThan(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::GreaterThan,
                print_core_expr(rhs)?,
            ),
            GreaterThanOrEqual(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::GreaterThanOrEqual,
                print_core_expr(rhs)?,
            ),
            Is(lhs, ast::Literal::Null) =>
                core_is(print_core_expr(lhs)?, Token::Keyword(Keyword::Null)),
            Is(lhs, ast::Literal::Float(value)) if float_trust::is_canonical_nan(*value) =>
                core_is(print_core_expr(lhs)?, Token::Keyword(Keyword::NaN)),
            Is(_, _) => return None,
            LessThan(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::LessThan, print_core_expr(rhs)?),
            LessThanOrEqual(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::LessThanOrEqual,
                print_core_expr(rhs)?,
            ),
            NotEqual(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::NotEqual, print_core_expr(rhs)?),
            Add(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Plus, print_core_expr(rhs)?),
            Divide(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Slash, print_core_expr(rhs)?),
            Exponentiate(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Caret, print_core_expr(rhs)?),
            Factorial(inner) => core_postfix(print_core_expr(inner)?, Token::Exclamation),
            Identity(inner) => core_unary(Token::Plus, print_core_expr(inner)?),
            Multiply(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Asterisk, print_core_expr(rhs)?),
            Negate(inner) => core_unary(Token::Minus, print_core_expr(inner)?),
            Remainder(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Percent, print_core_expr(rhs)?),
            Subtract(lhs, rhs) =>
                core_binary(print_core_expr(lhs)?, Token::Minus, print_core_expr(rhs)?),
            Like(lhs, rhs) => core_binary(
                print_core_expr(lhs)?,
                Token::Keyword(Keyword::Like),
                print_core_expr(rhs)?,
            ),
        }),
    }
}

fn contains_all_core(expression: &ast::Expression) -> (r: bool)
    ensures verified_expression::function_free(*expression) ==>
        r == verified_production::contains_all(*expression),
    decreases expression,
{
    use ast::Operator::*;

    let result = match expression {
        ast::Expression::All => true,
        ast::Expression::Column(_, _) | ast::Expression::Literal(_) => false,
        ast::Expression::Function(_, _) => true,
        ast::Expression::Operator(operator) => match operator {
            And(lhs, rhs)
            | Or(lhs, rhs)
            | Equal(lhs, rhs)
            | GreaterThan(lhs, rhs)
            | GreaterThanOrEqual(lhs, rhs)
            | LessThan(lhs, rhs)
            | LessThanOrEqual(lhs, rhs)
            | NotEqual(lhs, rhs)
            | Add(lhs, rhs)
            | Divide(lhs, rhs)
            | Exponentiate(lhs, rhs)
            | Multiply(lhs, rhs)
            | Remainder(lhs, rhs)
            | Subtract(lhs, rhs)
            | Like(lhs, rhs) => contains_all_core(lhs) || contains_all_core(rhs),
            Not(inner) | Factorial(inner) | Identity(inner) | Negate(inner) =>
                contains_all_core(inner),
            Is(inner, _) => contains_all_core(inner),
        },
    };
    proof {
        reveal(verified_expression::function_free);
        reveal(verified_production::contains_all);
    }
    result
}

fn print_delete(statement: &ast::Statement) -> (r: Option<Vec<Token>>)
    ensures match verified_production::delete_views(*statement) {
        Some(views) => r.is_some()
            && verified_production::token_views(r.unwrap()@) == views,
        None => r.is_none(),
    },
{
    match statement {
        ast::Statement::Delete { table, where_clause } => {
            let mut tokens = vec![
                Token::Keyword(Keyword::Delete),
                Token::Keyword(Keyword::From),
                Token::Ident(table.clone()),
            ];
            match where_clause {
                None => {
                    proof {
                        reveal(verified_production::delete_views);
                        reveal(verified_production::token_view);
                        reveal_with_fuel(verified_production::token_views, 4);
                    }
                    Some(tokens)
                },
                Some(expression) => {
                    proof {
                        verified_expression::printable_is_core(*expression);
                        reveal(verified_production::delete_views);
                        reveal(verified_expression::printable);
                        reveal(verified_expression::function_free);
                        reveal(verified_production::core_printable_expression);
                    }
                    if contains_all_core(expression) {
                        return None;
                    }
                    let mut expression_tokens = print_core_expr(expression)?;
                    let ghost expression_token_view = expression_tokens@;
                    tokens.push(Token::Keyword(Keyword::Where));
                    tokens.append(&mut expression_tokens);
                    proof {
                        assert(tokens@ =~= seq![
                            Token::Keyword(Keyword::Delete),
                            Token::Keyword(Keyword::From),
                            Token::Ident(*table),
                            Token::Keyword(Keyword::Where),
                        ] + expression_token_view);
                        verified_production::token_views_concat(
                            seq![
                                Token::Keyword(Keyword::Delete),
                                Token::Keyword(Keyword::From),
                                Token::Ident(*table),
                                Token::Keyword(Keyword::Where),
                            ],
                            expression_token_view,
                        );
                        reveal(verified_production::token_view);
                        reveal_with_fuel(verified_production::token_views, 5);
                    }
                    Some(tokens)
                },
            }
        },
        _ => None,
    }
}

#[allow(clippy::question_mark)]
fn print_simple_statement(statement: &ast::Statement) -> (r: Option<Vec<Token>>)
    ensures match verified_simple_statement::print_statement(*statement) {
        Some(views) => r.is_some()
            && verified_production::token_views(r.unwrap()@) == views,
        None => r.is_none(),
    },
    decreases statement,
{
    proof { reveal_with_fuel(verified_simple_statement::print_statement, 1); }
    match statement {
        ast::Statement::Begin { .. } => {
            let result = print_begin(statement);
            proof {
                assert(verified_simple_statement::print_statement(*statement)
                    == verified_production::begin_views(*statement));
            }
            result
        },
        ast::Statement::Commit | ast::Statement::Rollback => {
            let result = print_control_statement(statement);
            proof {
                reveal(verified_simple_statement::print_statement);
                reveal(verified_production::control_tokens);
                reveal(verified_production::token_view);
                reveal_with_fuel(verified_production::token_views, 2);
            }
            result
        },
        ast::Statement::DropTable { .. } => {
            let result = print_drop_table(statement);
            proof {
                reveal(verified_simple_statement::print_statement);
                reveal(verified_production::drop_table_tokens);
                reveal(verified_production::token_view);
                reveal_with_fuel(verified_production::token_views, 6);
            }
            result
        },
        ast::Statement::Delete { .. } => {
            let result = print_delete(statement);
            proof {
                assert(verified_simple_statement::print_statement(*statement)
                    == verified_production::delete_views(*statement));
            }
            result
        },
        ast::Statement::Explain(inner) => {
            if matches!(**inner, ast::Statement::Explain(_)) {
                proof {
                    assert(verified_simple_statement::print_statement(*statement).is_none());
                }
                return None;
            }
            let mut inner_tokens = match print_simple_statement(inner) {
                Some(tokens) => tokens,
                None => {
                    proof {
                        assert(verified_simple_statement::print_statement(**inner).is_none());
                        assert(verified_simple_statement::print_statement(*statement).is_none());
                    }
                    return None;
                },
            };
            let ghost inner_view = inner_tokens@;
            let mut tokens = vec![Token::Keyword(Keyword::Explain)];
            tokens.append(&mut inner_tokens);
            proof {
                reveal_with_fuel(verified_simple_statement::print_statement, 1);
                verified_production::token_views_concat(
                    seq![Token::Keyword(Keyword::Explain)],
                    inner_view,
                );
                reveal(verified_production::token_view);
                reveal_with_fuel(verified_production::token_views, 2);
                assert(tokens@ =~= seq![Token::Keyword(Keyword::Explain)] + inner_view);
            }
            Some(tokens)
        },
        _ => {
            proof {
                assert(verified_simple_statement::print_statement(*statement).is_none());
            }
            None
        },
    }
}

} // verus!

fn print_operator(operator: &ast::Operator) -> Option<Vec<Token>> {
    use ast::Operator::*;

    fn binary(mut lhs: Vec<Token>, token: Token, mut rhs: Vec<Token>) -> Vec<Token> {
        let mut tokens = vec![Token::OpenParen];
        tokens.append(&mut lhs);
        tokens.push(token);
        tokens.append(&mut rhs);
        tokens.push(Token::CloseParen);
        tokens
    }

    fn unary(token: Token, mut expression: Vec<Token>) -> Vec<Token> {
        let mut tokens = vec![Token::OpenParen, token];
        tokens.append(&mut expression);
        tokens.push(Token::CloseParen);
        tokens
    }

    fn postfix(mut expression: Vec<Token>, token: Token) -> Vec<Token> {
        let mut tokens = vec![Token::OpenParen];
        tokens.append(&mut expression);
        tokens.push(token);
        tokens.push(Token::CloseParen);
        tokens
    }

    fn is(mut lhs: Vec<Token>, value: Token) -> Vec<Token> {
        let mut tokens = vec![Token::OpenParen];
        tokens.append(&mut lhs);
        tokens.push(Keyword::Is.into());
        tokens.push(value);
        tokens.push(Token::CloseParen);
        tokens
    }

    Some(match operator {
        And(lhs, rhs) => binary(print_expr(lhs)?, Keyword::And.into(), print_expr(rhs)?),
        Not(expression) => unary(Keyword::Not.into(), print_expr(expression)?),
        Or(lhs, rhs) => binary(print_expr(lhs)?, Keyword::Or.into(), print_expr(rhs)?),
        Equal(lhs, rhs) => binary(print_expr(lhs)?, Token::Equal, print_expr(rhs)?),
        GreaterThan(lhs, rhs) => binary(print_expr(lhs)?, Token::GreaterThan, print_expr(rhs)?),
        GreaterThanOrEqual(lhs, rhs) => {
            binary(print_expr(lhs)?, Token::GreaterThanOrEqual, print_expr(rhs)?)
        }
        Is(lhs, ast::Literal::Null) => is(print_expr(lhs)?, Keyword::Null.into()),
        Is(lhs, ast::Literal::Float(value)) if float_trust::is_canonical_nan(*value) => {
            is(print_expr(lhs)?, Keyword::NaN.into())
        }
        Is(_, _) => return None,
        LessThan(lhs, rhs) => binary(print_expr(lhs)?, Token::LessThan, print_expr(rhs)?),
        LessThanOrEqual(lhs, rhs) => {
            binary(print_expr(lhs)?, Token::LessThanOrEqual, print_expr(rhs)?)
        }
        NotEqual(lhs, rhs) => binary(print_expr(lhs)?, Token::NotEqual, print_expr(rhs)?),
        Add(lhs, rhs) => binary(print_expr(lhs)?, Token::Plus, print_expr(rhs)?),
        Divide(lhs, rhs) => binary(print_expr(lhs)?, Token::Slash, print_expr(rhs)?),
        Exponentiate(lhs, rhs) => binary(print_expr(lhs)?, Token::Caret, print_expr(rhs)?),
        Factorial(expression) => postfix(print_expr(expression)?, Token::Exclamation),
        Identity(expression) => unary(Token::Plus, print_expr(expression)?),
        Multiply(lhs, rhs) => binary(print_expr(lhs)?, Token::Asterisk, print_expr(rhs)?),
        Negate(expression) => unary(Token::Minus, print_expr(expression)?),
        Remainder(lhs, rhs) => binary(print_expr(lhs)?, Token::Percent, print_expr(rhs)?),
        Subtract(lhs, rhs) => binary(print_expr(lhs)?, Token::Minus, print_expr(rhs)?),
        Like(lhs, rhs) => binary(print_expr(lhs)?, Keyword::Like.into(), print_expr(rhs)?),
    })
}

/// Prints a statement in canonical token form.
///
/// Returns `None` for statement shapes with no canonical token form.  Some of
/// these the parser genuinely cannot produce — empty required lists,
/// right-nested joins, nested `EXPLAIN`.  Others the parser *can* produce but
/// this printer still rejects, because they have no canonical form that
/// re-parses identically: notably an `All` (`*`) expression anywhere but a
/// direct select item, e.g. `count(*)`, which parses to
/// `Function("count", [All])`.
pub fn print_statement(statement: &ast::Statement) -> Option<Vec<Token>> {
    if let Some(tokens) = print_simple_statement(statement) {
        return Some(tokens);
    }
    match statement {
        ast::Statement::Begin { .. } => print_begin(statement),
        ast::Statement::Commit | ast::Statement::Rollback => print_control_statement(statement),
        ast::Statement::Explain(statement) => {
            if matches!(statement.as_ref(), ast::Statement::Explain(_)) {
                return None;
            }
            let mut tokens = vec![Keyword::Explain.into()];
            tokens.extend(print_statement(statement)?);
            Some(tokens)
        }
        ast::Statement::CreateTable { name, columns } => {
            if columns.is_empty() {
                return None;
            }
            let mut tokens = vec![
                Keyword::Create.into(),
                Keyword::Table.into(),
                Token::Ident(name.clone()),
                Token::OpenParen,
            ];
            for (index, column) in columns.iter().enumerate() {
                if index != 0 {
                    tokens.push(Token::Comma);
                }
                tokens.extend(print_column(column)?);
            }
            tokens.push(Token::CloseParen);
            Some(tokens)
        }
        ast::Statement::DropTable { .. } => print_drop_table(statement),
        ast::Statement::Delete { table, where_clause } => print_delete(statement).or_else(|| {
            let mut tokens =
                vec![Keyword::Delete.into(), Keyword::From.into(), Token::Ident(table.clone())];
            if let Some(expression) = where_clause {
                tokens.push(Keyword::Where.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            Some(tokens)
        }),
        ast::Statement::Insert { table, columns, values } => {
            if values.is_empty() || columns.as_ref().is_some_and(Vec::is_empty) {
                return None;
            }
            let mut tokens =
                vec![Keyword::Insert.into(), Keyword::Into.into(), Token::Ident(table.clone())];
            if let Some(columns) = columns {
                tokens.push(Token::OpenParen);
                for (index, column) in columns.iter().enumerate() {
                    if index != 0 {
                        tokens.push(Token::Comma);
                    }
                    tokens.push(Token::Ident(column.clone()));
                }
                tokens.push(Token::CloseParen);
            }
            tokens.push(Keyword::Values.into());
            for (row_index, row) in values.iter().enumerate() {
                if row.is_empty() {
                    return None;
                }
                if row_index != 0 {
                    tokens.push(Token::Comma);
                }
                tokens.push(Token::OpenParen);
                for (index, expression) in row.iter().enumerate() {
                    if index != 0 {
                        tokens.push(Token::Comma);
                    }
                    tokens.extend(print_statement_expression(expression)?);
                }
                tokens.push(Token::CloseParen);
            }
            Some(tokens)
        }
        ast::Statement::Update { table, set, where_clause } => {
            if set.is_empty() {
                return None;
            }
            let mut tokens =
                vec![Keyword::Update.into(), Token::Ident(table.clone()), Keyword::Set.into()];
            for (index, (column, expression)) in set.iter().enumerate() {
                if index != 0 {
                    tokens.push(Token::Comma);
                }
                tokens.push(Token::Ident(column.clone()));
                tokens.push(Token::Equal);
                match expression {
                    Some(expression) => tokens.extend(print_statement_expression(expression)?),
                    None => tokens.push(Keyword::Default.into()),
                }
            }
            if let Some(expression) = where_clause {
                tokens.push(Keyword::Where.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            Some(tokens)
        }
        ast::Statement::Select {
            select,
            from,
            where_clause,
            group_by,
            having,
            order_by,
            limit,
            offset,
        } => {
            if select.is_empty() {
                return None;
            }
            let mut tokens = vec![Keyword::Select.into()];
            for (index, (expression, alias)) in select.iter().enumerate() {
                if index != 0 {
                    tokens.push(Token::Comma);
                }
                if matches!(expression, ast::Expression::All) {
                    if alias.is_some() {
                        return None;
                    }
                    tokens.push(Token::Asterisk);
                } else {
                    tokens.extend(print_statement_expression(expression)?);
                    if let Some(alias) = alias {
                        tokens.extend([Keyword::As.into(), Token::Ident(alias.clone())]);
                    }
                }
            }
            if !from.is_empty() {
                tokens.push(Keyword::From.into());
                for (index, item) in from.iter().enumerate() {
                    if index != 0 {
                        tokens.push(Token::Comma);
                    }
                    tokens.extend(print_from(item)?);
                }
            }
            if let Some(expression) = where_clause {
                tokens.push(Keyword::Where.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            if !group_by.is_empty() {
                tokens.extend([Keyword::Group.into(), Keyword::By.into()]);
                for (index, expression) in group_by.iter().enumerate() {
                    if index != 0 {
                        tokens.push(Token::Comma);
                    }
                    tokens.extend(print_statement_expression(expression)?);
                }
            }
            if let Some(expression) = having {
                tokens.push(Keyword::Having.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            if !order_by.is_empty() {
                tokens.extend([Keyword::Order.into(), Keyword::By.into()]);
                for (index, (expression, direction)) in order_by.iter().enumerate() {
                    if index != 0 {
                        tokens.push(Token::Comma);
                    }
                    tokens.extend(print_statement_expression(expression)?);
                    tokens.push(
                        match direction {
                            ast::Direction::Ascending => Keyword::Asc,
                            ast::Direction::Descending => Keyword::Desc,
                        }
                        .into(),
                    );
                }
            }
            if let Some(expression) = limit {
                tokens.push(Keyword::Limit.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            if let Some(expression) = offset {
                tokens.push(Keyword::Offset.into());
                tokens.extend(print_statement_expression(expression)?);
            }
            Some(tokens)
        }
    }
}

fn print_statement_expression(expression: &ast::Expression) -> Option<Vec<Token>> {
    if contains_all(expression) { None } else { print_expr(expression) }
}

fn contains_all(expression: &ast::Expression) -> bool {
    match expression {
        ast::Expression::All => true,
        ast::Expression::Column(_, _) | ast::Expression::Literal(_) => false,
        ast::Expression::Function(_, arguments) => arguments.iter().any(contains_all),
        ast::Expression::Operator(operator) => match operator {
            ast::Operator::And(lhs, rhs)
            | ast::Operator::Or(lhs, rhs)
            | ast::Operator::Equal(lhs, rhs)
            | ast::Operator::GreaterThan(lhs, rhs)
            | ast::Operator::GreaterThanOrEqual(lhs, rhs)
            | ast::Operator::LessThan(lhs, rhs)
            | ast::Operator::LessThanOrEqual(lhs, rhs)
            | ast::Operator::NotEqual(lhs, rhs)
            | ast::Operator::Add(lhs, rhs)
            | ast::Operator::Divide(lhs, rhs)
            | ast::Operator::Exponentiate(lhs, rhs)
            | ast::Operator::Multiply(lhs, rhs)
            | ast::Operator::Remainder(lhs, rhs)
            | ast::Operator::Subtract(lhs, rhs)
            | ast::Operator::Like(lhs, rhs) => contains_all(lhs) || contains_all(rhs),
            ast::Operator::Not(expression)
            | ast::Operator::Factorial(expression)
            | ast::Operator::Identity(expression)
            | ast::Operator::Negate(expression) => contains_all(expression),
            ast::Operator::Is(expression, _) => contains_all(expression),
        },
    }
}

fn print_column(column: &ast::Column) -> Option<Vec<Token>> {
    let mut tokens = vec![Token::Ident(column.name.clone()), print_datatype(column.datatype)];
    if column.primary_key {
        tokens.extend([Keyword::Primary.into(), Keyword::Key.into()]);
    }
    match column.nullable {
        Some(true) => tokens.push(Keyword::Null.into()),
        Some(false) => tokens.extend([Keyword::Not.into(), Keyword::Null.into()]),
        None => {}
    }
    if let Some(expression) = &column.default {
        tokens.push(Keyword::Default.into());
        tokens.extend(print_statement_expression(expression)?);
    }
    if column.unique {
        tokens.push(Keyword::Unique.into());
    }
    if column.index {
        tokens.push(Keyword::Index.into());
    }
    if let Some(table) = &column.references {
        tokens.extend([Keyword::References.into(), Token::Ident(table.clone())]);
    }
    Some(tokens)
}

fn print_datatype(datatype: crate::sql::types::DataType) -> Token {
    match datatype {
        crate::sql::types::DataType::Boolean => Keyword::Boolean.into(),
        crate::sql::types::DataType::Integer => Keyword::Integer.into(),
        crate::sql::types::DataType::Float => Keyword::Float.into(),
        crate::sql::types::DataType::String => Keyword::String.into(),
    }
}

fn print_from(from: &ast::From) -> Option<Vec<Token>> {
    match from {
        ast::From::Table { name, alias } => {
            let mut tokens = vec![Token::Ident(name.clone())];
            if let Some(alias) = alias {
                tokens.extend([Keyword::As.into(), Token::Ident(alias.clone())]);
            }
            Some(tokens)
        }
        ast::From::Join { left, right, join_type, predicate } => {
            if !matches!(right.as_ref(), ast::From::Table { .. }) {
                return None;
            }
            if matches!(join_type, ast::JoinType::Cross) != predicate.is_none() {
                return None;
            }
            let mut tokens = print_from(left)?;
            tokens.extend(match join_type {
                ast::JoinType::Cross => vec![Keyword::Cross.into(), Keyword::Join.into()],
                ast::JoinType::Inner => vec![Keyword::Inner.into(), Keyword::Join.into()],
                ast::JoinType::Left => vec![Keyword::Left.into(), Keyword::Join.into()],
                ast::JoinType::Right => vec![Keyword::Right.into(), Keyword::Join.into()],
            });
            tokens.extend(print_from(right)?);
            if let Some(predicate) = predicate {
                tokens.push(Keyword::On.into());
                tokens.extend(print_statement_expression(predicate)?);
            }
            Some(tokens)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::print_expr;
    use crate::sql::parser::Parser;
    use crate::sql::parser::ast::{Expression, Literal, Operator};
    use proptest::prelude::*;

    fn boxed(expression: Expression) -> Box<Expression> {
        Box::new(expression)
    }

    fn column(name: &str) -> Expression {
        Expression::Column(None, name.into())
    }

    fn roundtrip(expression: Expression) {
        let tokens = print_expr(&expression).expect("expression should be parser-producible");
        let parsed = Parser::parse_expr_tokens(&tokens).expect("canonical tokens should parse");
        assert_eq!(parsed, expression);
    }

    fn strings() -> impl Strategy<Value = String> {
        proptest::collection::vec(any::<char>(), 0..16)
            .prop_map(|chars| chars.into_iter().collect())
    }

    fn expression_strategy(include_all: bool) -> BoxedStrategy<Expression> {
        let finite_float = (0u64..=0x7fefffffffffffff).prop_map(f64::from_bits);
        let atom = prop_oneof![
            (proptest::option::of(strings()), strings())
                .prop_map(|(table, column)| { Expression::Column(table, column) }),
            Just(Expression::Literal(Literal::Null)),
            any::<bool>().prop_map(|value| Expression::Literal(Literal::Boolean(value))),
            (0i64..=i64::MAX).prop_map(|value| Expression::Literal(Literal::Integer(value))),
            finite_float.prop_map(|value| Expression::Literal(Literal::Float(value))),
            strings().prop_map(|value| Expression::Literal(Literal::String(value))),
        ]
        .boxed();
        let leaf =
            if include_all { prop_oneof![Just(Expression::All), atom].boxed() } else { atom };

        leaf.prop_recursive(5, 128, 8, |inner| {
            let binary = (0u8..15, inner.clone(), inner.clone()).prop_map(|(kind, lhs, rhs)| {
                let (lhs, rhs) = (Box::new(lhs), Box::new(rhs));
                Expression::Operator(match kind {
                    0 => Operator::And(lhs, rhs),
                    1 => Operator::Or(lhs, rhs),
                    2 => Operator::Equal(lhs, rhs),
                    3 => Operator::GreaterThan(lhs, rhs),
                    4 => Operator::GreaterThanOrEqual(lhs, rhs),
                    5 => Operator::LessThan(lhs, rhs),
                    6 => Operator::LessThanOrEqual(lhs, rhs),
                    7 => Operator::NotEqual(lhs, rhs),
                    8 => Operator::Add(lhs, rhs),
                    9 => Operator::Divide(lhs, rhs),
                    10 => Operator::Exponentiate(lhs, rhs),
                    11 => Operator::Multiply(lhs, rhs),
                    12 => Operator::Remainder(lhs, rhs),
                    13 => Operator::Subtract(lhs, rhs),
                    14 => Operator::Like(lhs, rhs),
                    _ => unreachable!("strategy constrains the operator index"),
                })
            });
            let unary = (0u8..4, inner.clone()).prop_map(|(kind, expression)| {
                let expression = Box::new(expression);
                Expression::Operator(match kind {
                    0 => Operator::Not(expression),
                    1 => Operator::Factorial(expression),
                    2 => Operator::Identity(expression),
                    3 => Operator::Negate(expression),
                    _ => unreachable!("strategy constrains the operator index"),
                })
            });
            let is = (inner.clone(), any::<bool>()).prop_map(|(expression, nan)| {
                Expression::Operator(Operator::Is(
                    Box::new(expression),
                    if nan { Literal::Float(f64::NAN) } else { Literal::Null },
                ))
            });
            let function = (strings(), proptest::collection::vec(inner, 0..5))
                .prop_map(|(name, arguments)| Expression::Function(name, arguments));

            prop_oneof![binary, unary, is, function]
        })
        .boxed()
    }

    fn expressions() -> BoxedStrategy<Expression> {
        expression_strategy(true)
    }

    fn statement_expressions() -> BoxedStrategy<Expression> {
        expression_strategy(false)
    }

    fn from_items() -> BoxedStrategy<crate::sql::parser::ast::From> {
        use crate::sql::parser::ast::{From, JoinType};

        let tables = (strings(), proptest::option::of(strings()))
            .prop_map(|(name, alias)| From::Table { name, alias })
            .boxed();
        let right_tables = tables.clone();
        tables
            .prop_recursive(3, 32, 2, move |left| {
                let cross =
                    (left.clone(), right_tables.clone()).prop_map(|(left, right)| From::Join {
                        left: Box::new(left),
                        right: Box::new(right),
                        join_type: JoinType::Cross,
                        predicate: None,
                    });
                let joined =
                    (
                        left,
                        right_tables.clone(),
                        prop_oneof![
                            Just(JoinType::Inner),
                            Just(JoinType::Left),
                            Just(JoinType::Right),
                        ],
                        statement_expressions(),
                    )
                        .prop_map(|(left, right, join_type, predicate)| {
                            From::Join {
                                left: Box::new(left),
                                right: Box::new(right),
                                join_type,
                                predicate: Some(predicate),
                            }
                        });
                prop_oneof![cross, joined]
            })
            .boxed()
    }

    fn statements() -> BoxedStrategy<crate::sql::parser::ast::Statement> {
        use crate::sql::parser::ast::{Column, Direction, Statement};
        use crate::sql::types::DataType;

        let datatype = prop_oneof![
            Just(DataType::Boolean),
            Just(DataType::Integer),
            Just(DataType::Float),
            Just(DataType::String),
        ];
        let columns = (
            strings(),
            datatype,
            any::<bool>(),
            proptest::option::of(any::<bool>()),
            proptest::option::of(statement_expressions()),
            any::<bool>(),
            any::<bool>(),
            proptest::option::of(strings()),
        )
            .prop_map(
                |(name, datatype, primary_key, nullable, default, unique, index, references)| {
                    Column {
                        name,
                        datatype,
                        primary_key,
                        nullable,
                        default,
                        unique,
                        index,
                        references,
                    }
                },
            );
        let begin = (any::<bool>(), proptest::option::of(any::<u64>()))
            .prop_map(|(read_only, as_of)| Statement::Begin { read_only, as_of });
        let create = (strings(), proptest::collection::vec(columns, 1..5))
            .prop_map(|(name, columns)| Statement::CreateTable { name, columns });
        let drop = (strings(), any::<bool>())
            .prop_map(|(name, if_exists)| Statement::DropTable { name, if_exists });
        let delete = (strings(), proptest::option::of(statement_expressions()))
            .prop_map(|(table, where_clause)| Statement::Delete { table, where_clause });
        let insert_columns =
            prop_oneof![Just(None), proptest::collection::vec(strings(), 1..5).prop_map(Some),];
        let insert = (
            strings(),
            insert_columns,
            proptest::collection::vec(
                proptest::collection::vec(statement_expressions(), 1..5),
                1..5,
            ),
        )
            .prop_map(|(table, columns, values)| Statement::Insert {
                table,
                columns,
                values,
            });
        let update = (
            strings(),
            proptest::collection::btree_map(
                strings(),
                proptest::option::of(statement_expressions()),
                1..5,
            ),
            proptest::option::of(statement_expressions()),
        )
            .prop_map(|(table, set, where_clause)| Statement::Update {
                table,
                set,
                where_clause,
            });
        let select_item = prop_oneof![
            Just((Expression::All, None)),
            (statement_expressions(), proptest::option::of(strings())),
        ];
        let direction = prop_oneof![Just(Direction::Ascending), Just(Direction::Descending)];
        let select = (
            proptest::collection::vec(select_item, 1..5),
            proptest::collection::vec(from_items(), 0..4),
            proptest::option::of(statement_expressions()),
            proptest::collection::vec(statement_expressions(), 0..4),
            proptest::option::of(statement_expressions()),
            proptest::collection::vec((statement_expressions(), direction), 0..4),
            proptest::option::of(statement_expressions()),
            proptest::option::of(statement_expressions()),
        )
            .prop_map(
                |(select, from, where_clause, group_by, having, order_by, limit, offset)| {
                    Statement::Select {
                        select,
                        from,
                        where_clause,
                        group_by,
                        having,
                        order_by,
                        limit,
                        offset,
                    }
                },
            );
        let base = prop_oneof![
            begin,
            Just(Statement::Commit),
            Just(Statement::Rollback),
            create,
            drop,
            delete,
            insert,
            update,
            select,
        ]
        .boxed();
        prop_oneof![
            base.clone(),
            base.prop_map(|statement| Statement::Explain(Box::new(statement)))
        ]
        .boxed()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn parser_inverts_the_canonical_printer(expression in expressions()) {
            let tokens = print_expr(&expression)
                .expect("the strategy only generates parser-producible expressions");
            prop_assert_eq!(Parser::parse_expr_tokens(&tokens), Ok(expression));
        }

        #[test]
        fn parser_inverts_the_canonical_statement_printer(statement in statements()) {
            let tokens = super::print_statement(&statement)
                .expect("the strategy only generates parser-producible statements");
            prop_assert_eq!(Parser::parse_statement_tokens(&tokens), Ok(statement));
        }

        #[test]
        fn canonical_expression_printer_is_injective(
            left in expressions(),
            right in expressions(),
        ) {
            let left_tokens = print_expr(&left).expect("strategy generates printable expressions");
            let right_tokens = print_expr(&right).expect("strategy generates printable expressions");
            if left_tokens == right_tokens {
                prop_assert_eq!(left, right);
            }
        }

        #[test]
        fn canonical_statement_printer_is_injective(
            left in statements(),
            right in statements(),
        ) {
            let left_tokens = super::print_statement(&left)
                .expect("strategy generates printable statements");
            let right_tokens = super::print_statement(&right)
                .expect("strategy generates printable statements");
            if left_tokens == right_tokens {
                prop_assert_eq!(left, right);
            }
        }
    }

    #[test]
    fn prints_atoms_columns_functions_and_lists() {
        roundtrip(Expression::All);
        roundtrip(column("value"));
        roundtrip(Expression::Column(Some("orders".into()), "value".into()));
        roundtrip(Expression::Literal(Literal::Null));
        roundtrip(Expression::Literal(Literal::Boolean(true)));
        roundtrip(Expression::Literal(Literal::Boolean(false)));
        roundtrip(Expression::Literal(Literal::Integer(42)));
        roundtrip(Expression::Literal(Literal::Integer(i64::MAX)));
        roundtrip(Expression::Literal(Literal::Float(1.25)));
        roundtrip(Expression::Literal(Literal::Float(1.0)));
        roundtrip(Expression::Literal(Literal::String("a'b".into())));
        roundtrip(Expression::Function("coalesce".into(), vec![]));
        roundtrip(Expression::Function(
            "coalesce".into(),
            vec![column("value"), Expression::Literal(Literal::Integer(1))],
        ));
    }

    #[test]
    fn prints_every_operator_variant() {
        let a = column("a");
        let b = column("b");
        let binary = [
            Operator::And(boxed(a.clone()), boxed(b.clone())),
            Operator::Or(boxed(a.clone()), boxed(b.clone())),
            Operator::Equal(boxed(a.clone()), boxed(b.clone())),
            Operator::GreaterThan(boxed(a.clone()), boxed(b.clone())),
            Operator::GreaterThanOrEqual(boxed(a.clone()), boxed(b.clone())),
            Operator::LessThan(boxed(a.clone()), boxed(b.clone())),
            Operator::LessThanOrEqual(boxed(a.clone()), boxed(b.clone())),
            Operator::NotEqual(boxed(a.clone()), boxed(b.clone())),
            Operator::Add(boxed(a.clone()), boxed(b.clone())),
            Operator::Divide(boxed(a.clone()), boxed(b.clone())),
            Operator::Exponentiate(boxed(a.clone()), boxed(b.clone())),
            Operator::Multiply(boxed(a.clone()), boxed(b.clone())),
            Operator::Remainder(boxed(a.clone()), boxed(b.clone())),
            Operator::Subtract(boxed(a.clone()), boxed(b.clone())),
            Operator::Like(boxed(a.clone()), boxed(b.clone())),
        ];
        for operator in binary {
            roundtrip(Expression::Operator(operator));
        }

        for operator in [
            Operator::Not(boxed(a.clone())),
            Operator::Factorial(boxed(a.clone())),
            Operator::Identity(boxed(a.clone())),
            Operator::Negate(boxed(a.clone())),
            Operator::Is(boxed(a.clone()), Literal::Null),
            Operator::Is(boxed(a.clone()), Literal::Float(f64::NAN)),
        ] {
            roundtrip(Expression::Operator(operator));
        }
    }

    #[test]
    fn rejects_signed_and_nonfinite_literal_shapes() {
        for literal in [
            Literal::Integer(-1),
            Literal::Float(-1.0),
            Literal::Float(-0.0),
            Literal::Float(f64::NAN),
            Literal::Float(f64::INFINITY),
            Literal::Float(f64::NEG_INFINITY),
        ] {
            assert!(print_expr(&Expression::Literal(literal)).is_none());
        }

        let noncanonical_nan = f64::from_bits(f64::NAN.to_bits() ^ 1);
        let is_nan = Expression::Operator(Operator::Is(
            boxed(column("value")),
            Literal::Float(noncanonical_nan),
        ));
        assert!(print_expr(&is_nan).is_none());
    }

    fn roundtrip_statement(statement: crate::sql::parser::ast::Statement) {
        let tokens = super::print_statement(&statement).expect("statement should be printable");
        let parsed =
            Parser::parse_statement_tokens(&tokens).expect("canonical tokens should parse");
        assert_eq!(parsed, statement);
    }

    fn table(name: &str) -> crate::sql::parser::ast::From {
        crate::sql::parser::ast::From::Table { name: name.into(), alias: None }
    }

    fn predicate(name: &str) -> Expression {
        Expression::Operator(Operator::Equal(
            boxed(column(name)),
            boxed(Expression::Literal(Literal::Integer(1))),
        ))
    }

    #[test]
    fn prints_every_statement_and_nested_ast_form() {
        use crate::sql::parser::ast::{Column, Direction, From, JoinType, Statement};
        use crate::sql::types::DataType;
        use std::collections::BTreeMap;

        roundtrip_statement(Statement::Begin { read_only: false, as_of: None });
        roundtrip_statement(Statement::Begin { read_only: true, as_of: Some(7) });
        roundtrip_statement(Statement::Begin { read_only: true, as_of: Some(u64::MAX) });
        roundtrip_statement(Statement::Commit);
        roundtrip_statement(Statement::Rollback);
        roundtrip_statement(Statement::Explain(Box::new(Statement::Commit)));

        let columns = vec![
            Column {
                name: "b".into(),
                datatype: DataType::Boolean,
                primary_key: true,
                nullable: Some(false),
                default: Some(Expression::Literal(Literal::Boolean(true))),
                unique: true,
                index: true,
                references: Some("parent".into()),
            },
            Column {
                name: "i".into(),
                datatype: DataType::Integer,
                primary_key: false,
                nullable: None,
                default: None,
                unique: false,
                index: false,
                references: None,
            },
            Column {
                name: "f".into(),
                datatype: DataType::Float,
                primary_key: false,
                nullable: Some(true),
                default: None,
                unique: false,
                index: false,
                references: None,
            },
            Column {
                name: "s".into(),
                datatype: DataType::String,
                primary_key: false,
                nullable: None,
                default: None,
                unique: false,
                index: false,
                references: None,
            },
        ];
        roundtrip_statement(Statement::CreateTable { name: "items".into(), columns });
        roundtrip_statement(Statement::DropTable { name: "items".into(), if_exists: false });
        roundtrip_statement(Statement::DropTable { name: "items".into(), if_exists: true });
        roundtrip_statement(Statement::Delete {
            table: "items".into(),
            where_clause: Some(predicate("id")),
        });

        roundtrip_statement(Statement::Insert {
            table: "items".into(),
            columns: None,
            values: vec![vec![Expression::Literal(Literal::Integer(1))]],
        });
        roundtrip_statement(Statement::Insert {
            table: "items".into(),
            columns: Some(vec!["id".into(), "name".into()]),
            values: vec![vec![
                Expression::Literal(Literal::Integer(1)),
                Expression::Literal(Literal::String("one".into())),
            ]],
        });

        let mut set = BTreeMap::new();
        set.insert("a".into(), Some(Expression::Literal(Literal::Integer(2))));
        set.insert("b".into(), None);
        roundtrip_statement(Statement::Update {
            table: "items".into(),
            set,
            where_clause: Some(predicate("id")),
        });

        let inner = From::Join {
            left: Box::new(table("a")),
            right: Box::new(From::Table { name: "b".into(), alias: Some("bee".into()) }),
            join_type: JoinType::Inner,
            predicate: Some(predicate("a_id")),
        };
        let left = From::Join {
            left: Box::new(inner),
            right: Box::new(table("c")),
            join_type: JoinType::Left,
            predicate: Some(predicate("b_id")),
        };
        let right = From::Join {
            left: Box::new(left),
            right: Box::new(table("d")),
            join_type: JoinType::Right,
            predicate: Some(predicate("c_id")),
        };
        let cross = From::Join {
            left: Box::new(table("e")),
            right: Box::new(table("f")),
            join_type: JoinType::Cross,
            predicate: None,
        };
        roundtrip_statement(Statement::Select {
            select: vec![(Expression::All, None), (column("name"), Some("label".into()))],
            from: vec![right, cross],
            where_clause: Some(predicate("id")),
            group_by: vec![column("name")],
            having: Some(predicate("count")),
            order_by: vec![
                (column("name"), Direction::Ascending),
                (column("id"), Direction::Descending),
            ],
            limit: Some(Expression::Literal(Literal::Integer(10))),
            offset: Some(Expression::Literal(Literal::Integer(2))),
        });
    }

    #[test]
    fn rejects_non_parser_producible_statement_shapes() {
        use crate::sql::parser::ast::{Direction, From, JoinType, Statement};
        use std::collections::BTreeMap;

        assert!(
            super::print_statement(&Statement::CreateTable { name: "t".into(), columns: vec![] })
                .is_none()
        );
        assert!(
            super::print_statement(&Statement::Explain(Box::new(Statement::Explain(Box::new(
                Statement::Commit
            )))))
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Insert {
                table: "t".into(),
                columns: Some(vec![]),
                values: vec![vec![Expression::Literal(Literal::Integer(1))]],
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Insert {
                table: "t".into(),
                columns: None,
                values: vec![vec![]],
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Update {
                table: "t".into(),
                set: BTreeMap::new(),
                where_clause: None,
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Select {
                select: vec![],
                from: vec![],
                where_clause: None,
                group_by: vec![],
                having: None,
                order_by: vec![],
                limit: None,
                offset: None,
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Select {
                select: vec![(Expression::All, Some("x".into()))],
                from: vec![],
                where_clause: None,
                group_by: vec![],
                having: None,
                order_by: vec![],
                limit: None,
                offset: None,
            })
            .is_none()
        );
        for arguments in [
            vec![Expression::All, column("x")],
            vec![column("x"), Expression::All, column("y")],
            vec![column("x"), Expression::All],
        ] {
            assert!(
                super::print_statement(&Statement::Select {
                    select: vec![(Expression::Function("f".into(), arguments), None)],
                    from: vec![],
                    where_clause: None,
                    group_by: vec![],
                    having: None,
                    order_by: vec![],
                    limit: None,
                    offset: None,
                })
                .is_none()
            );
        }
        assert!(
            super::print_statement(&Statement::Select {
                select: vec![(
                    Expression::Operator(Operator::Add(boxed(Expression::All), boxed(column("x")))),
                    None
                )],
                from: vec![],
                where_clause: None,
                group_by: vec![],
                having: None,
                order_by: vec![],
                limit: None,
                offset: None,
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Select {
                select: vec![(column("x"), None)],
                from: vec![From::Join {
                    left: Box::new(From::Table { name: "a".into(), alias: None }),
                    right: Box::new(From::Join {
                        left: Box::new(From::Table { name: "b".into(), alias: None }),
                        right: Box::new(From::Table { name: "c".into(), alias: None }),
                        join_type: JoinType::Inner,
                        predicate: Some(predicate("id")),
                    }),
                    join_type: JoinType::Cross,
                    predicate: None,
                }],
                where_clause: None,
                group_by: vec![],
                having: None,
                order_by: vec![(column("x"), Direction::Ascending)],
                limit: None,
                offset: None,
            })
            .is_none()
        );
        assert!(
            super::print_statement(&Statement::Select {
                select: vec![(column("x"), None)],
                from: vec![From::Join {
                    left: Box::new(From::Table { name: "a".into(), alias: None }),
                    right: Box::new(From::Table { name: "b".into(), alias: None }),
                    join_type: JoinType::Cross,
                    predicate: Some(predicate("id")),
                }],
                where_clause: None,
                group_by: vec![],
                having: None,
                order_by: vec![],
                limit: None,
                offset: None,
            })
            .is_none()
        );
    }
}
