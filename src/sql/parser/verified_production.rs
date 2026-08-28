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

pub proof fn literal_injective(left: ast::Literal, right: ast::Literal)
    requires
        literal_views(left).is_some(),
        literal_views(right).is_some(),
        literal_views(left) == literal_views(right),
    ensures left == right,
{
    literal_roundtrip(left);
    literal_roundtrip(right);
}

pub open spec fn atom_views(expression: ast::Expression) -> Option<Seq<TokenView>> {
    match expression {
        ast::Expression::All => Some(seq![TokenView::Asterisk]),
        ast::Expression::Column(None, column) => Some(seq![TokenView::Ident(column)]),
        ast::Expression::Column(Some(table), column) => Some(seq![
            TokenView::Ident(table),
            TokenView::Period,
            TokenView::Ident(column),
        ]),
        _ => None,
    }
}

pub open spec fn parse_atom_views(tokens: Seq<TokenView>) -> Option<ast::Expression> {
    if tokens == seq![TokenView::Asterisk] {
        Some(ast::Expression::All)
    } else if tokens.len() == 1 {
        match tokens[0] {
            TokenView::Ident(column) => Some(ast::Expression::Column(None, column)),
            _ => None,
        }
    } else if tokens.len() == 3 && tokens[1] == TokenView::Period {
        match (tokens[0], tokens[2]) {
            (TokenView::Ident(table), TokenView::Ident(column)) =>
                Some(ast::Expression::Column(Some(table), column)),
            _ => None,
        }
    } else {
        None
    }
}

pub proof fn atom_roundtrip(expression: ast::Expression)
    requires atom_views(expression).is_some(),
    ensures parse_atom_views(atom_views(expression).unwrap()) == Some(expression),
{
    reveal(atom_views);
    reveal(parse_atom_views);
    match expression {
        ast::Expression::All
        | ast::Expression::Column(_, _) => {},
        _ => assert(false),
    }
}

pub proof fn atom_injective(left: ast::Expression, right: ast::Expression)
    requires
        atom_views(left).is_some(),
        atom_views(right).is_some(),
        atom_views(left) == atom_views(right),
    ensures left == right,
{
    atom_roundtrip(left);
    atom_roundtrip(right);
}

/// Exact canonical encoding for the list-free transaction-control variants.
pub open spec fn control_tokens(statement: ast::Statement) -> Option<Seq<Token>> {
    match statement {
        ast::Statement::Commit => Some(seq![Token::Keyword(Keyword::Commit)]),
        ast::Statement::Rollback => Some(seq![Token::Keyword(Keyword::Rollback)]),
        _ => None,
    }
}

/// Exact decoder for the canonical transaction-control encodings.
pub open spec fn parse_control(tokens: Seq<Token>) -> Option<ast::Statement> {
    if tokens == seq![Token::Keyword(Keyword::Commit)] {
        Some(ast::Statement::Commit)
    } else if tokens == seq![Token::Keyword(Keyword::Rollback)] {
        Some(ast::Statement::Rollback)
    } else {
        None
    }
}

pub proof fn control_roundtrip(statement: ast::Statement)
    requires control_tokens(statement).is_some(),
    ensures parse_control(control_tokens(statement).unwrap()) == Some(statement),
{
    reveal(control_tokens);
    reveal(parse_control);
    match statement {
        ast::Statement::Commit => {
            assert(control_tokens(statement)
                == Some(seq![Token::Keyword(Keyword::Commit)]));
            assert(parse_control(seq![Token::Keyword(Keyword::Commit)])
                == Some(ast::Statement::Commit));
        },
        ast::Statement::Rollback => {
            assert(Keyword::Rollback != Keyword::Commit);
            assert(Token::Keyword(Keyword::Rollback) != Token::Keyword(Keyword::Commit));
            let rollback = seq![Token::Keyword(Keyword::Rollback)];
            let commit = seq![Token::Keyword(Keyword::Commit)];
            if rollback == commit {
                assert(rollback[0] == commit[0]);
                assert(false);
            }
            assert(control_tokens(statement)
                == Some(seq![Token::Keyword(Keyword::Rollback)]));
            assert(parse_control(seq![Token::Keyword(Keyword::Rollback)])
                == Some(ast::Statement::Rollback));
        },
        _ => assert(false),
    }
}

pub proof fn control_injective(left: ast::Statement, right: ast::Statement)
    requires
        control_tokens(left).is_some(),
        control_tokens(right).is_some(),
        control_tokens(left) == control_tokens(right),
    ensures left == right,
{
    control_roundtrip(left);
    control_roundtrip(right);
}

/// Exact canonical encoding for `DROP TABLE`.
pub open spec fn drop_table_tokens(statement: ast::Statement) -> Option<Seq<Token>> {
    match statement {
        ast::Statement::DropTable { name, if_exists: false } => Some(seq![
            Token::Keyword(Keyword::Drop),
            Token::Keyword(Keyword::Table),
            Token::Ident(name),
        ]),
        ast::Statement::DropTable { name, if_exists: true } => Some(seq![
            Token::Keyword(Keyword::Drop),
            Token::Keyword(Keyword::Table),
            Token::Keyword(Keyword::If),
            Token::Keyword(Keyword::Exists),
            Token::Ident(name),
        ]),
        _ => None,
    }
}

pub open spec fn parse_drop_table(tokens: Seq<Token>) -> Option<ast::Statement> {
    if tokens.len() == 3
        && tokens[0] == Token::Keyword(Keyword::Drop)
        && tokens[1] == Token::Keyword(Keyword::Table)
    {
        match tokens[2] {
            Token::Ident(name) =>
                Some(ast::Statement::DropTable { name, if_exists: false }),
            _ => None,
        }
    } else if tokens.len() == 5
        && tokens[0] == Token::Keyword(Keyword::Drop)
        && tokens[1] == Token::Keyword(Keyword::Table)
        && tokens[2] == Token::Keyword(Keyword::If)
        && tokens[3] == Token::Keyword(Keyword::Exists)
    {
        match tokens[4] {
            Token::Ident(name) =>
                Some(ast::Statement::DropTable { name, if_exists: true }),
            _ => None,
        }
    } else {
        None
    }
}

pub proof fn drop_table_roundtrip(statement: ast::Statement)
    requires drop_table_tokens(statement).is_some(),
    ensures parse_drop_table(drop_table_tokens(statement).unwrap()) == Some(statement),
{
    reveal(drop_table_tokens);
    reveal(parse_drop_table);
    match statement {
        ast::Statement::DropTable { if_exists: false, .. } => {},
        ast::Statement::DropTable { if_exists: true, .. } => {},
        _ => assert(false),
    }
}

pub proof fn drop_table_injective(left: ast::Statement, right: ast::Statement)
    requires
        drop_table_tokens(left).is_some(),
        drop_table_tokens(right).is_some(),
        drop_table_tokens(left) == drop_table_tokens(right),
    ensures left == right,
{
    drop_table_roundtrip(left);
    drop_table_roundtrip(right);
}

/// Exact token-view encoding for `BEGIN`.
pub open spec fn begin_views(statement: ast::Statement) -> Option<Seq<TokenView>> {
    match statement {
        ast::Statement::Begin { read_only, as_of } => {
            let prefix = if read_only {
                seq![
                    TokenView::Keyword(Keyword::Begin),
                    TokenView::Keyword(Keyword::Read),
                    TokenView::Keyword(Keyword::Only),
                ]
            } else {
                seq![TokenView::Keyword(Keyword::Begin)]
            };
            Some(prefix + match as_of {
                Some(version) => seq![
                    TokenView::Keyword(Keyword::As),
                    TokenView::Keyword(Keyword::Of),
                    TokenView::Keyword(Keyword::System),
                    TokenView::Keyword(Keyword::Time),
                    TokenView::Number(super::verified_integer::decimal_digits(version)),
                ],
                None => Seq::empty(),
            })
        },
        _ => None,
    }
}

pub open spec fn parse_begin_views(tokens: Seq<TokenView>) -> Option<ast::Statement> {
    if tokens == seq![TokenView::Keyword(Keyword::Begin)] {
        Some(ast::Statement::Begin { read_only: false, as_of: None })
    } else if tokens == seq![
        TokenView::Keyword(Keyword::Begin),
        TokenView::Keyword(Keyword::Read),
        TokenView::Keyword(Keyword::Only),
    ] {
        Some(ast::Statement::Begin { read_only: true, as_of: None })
    } else if tokens.len() == 6
        && tokens[0] == TokenView::Keyword(Keyword::Begin)
        && tokens[1] == TokenView::Keyword(Keyword::As)
        && tokens[2] == TokenView::Keyword(Keyword::Of)
        && tokens[3] == TokenView::Keyword(Keyword::System)
        && tokens[4] == TokenView::Keyword(Keyword::Time)
    {
        match tokens[5] {
            TokenView::Number(bytes) => match super::verified_integer::parse_digits_spec(bytes) {
                Some(version) =>
                    Some(ast::Statement::Begin { read_only: false, as_of: Some(version) }),
                None => None,
            },
            _ => None,
        }
    } else if tokens.len() == 8
        && tokens[0] == TokenView::Keyword(Keyword::Begin)
        && tokens[1] == TokenView::Keyword(Keyword::Read)
        && tokens[2] == TokenView::Keyword(Keyword::Only)
        && tokens[3] == TokenView::Keyword(Keyword::As)
        && tokens[4] == TokenView::Keyword(Keyword::Of)
        && tokens[5] == TokenView::Keyword(Keyword::System)
        && tokens[6] == TokenView::Keyword(Keyword::Time)
    {
        match tokens[7] {
            TokenView::Number(bytes) => match super::verified_integer::parse_digits_spec(bytes) {
                Some(version) =>
                    Some(ast::Statement::Begin { read_only: true, as_of: Some(version) }),
                None => None,
            },
            _ => None,
        }
    } else {
        None
    }
}

pub proof fn begin_roundtrip(statement: ast::Statement)
    requires begin_views(statement).is_some(),
    ensures parse_begin_views(begin_views(statement).unwrap()) == Some(statement),
{
    reveal(begin_views);
    reveal(parse_begin_views);
    match statement {
        ast::Statement::Begin { read_only, as_of } => {
            match (read_only, as_of) {
                (false, None) => {},
                (true, None) => {},
                (false, Some(version)) => {
                    super::verified_integer::print_parse_u64_roundtrip(version);
                },
                (true, Some(version)) => {
                    super::verified_integer::print_parse_u64_roundtrip(version);
                },
            }
        },
        _ => assert(false),
    }
}

pub proof fn begin_injective(left: ast::Statement, right: ast::Statement)
    requires
        begin_views(left).is_some(),
        begin_views(right).is_some(),
        begin_views(left) == begin_views(right),
    ensures left == right,
{
    begin_roundtrip(left);
    begin_roundtrip(right);
}

/// Exact canonical encoding for a list-free `DELETE` statement whose optional
/// predicate is in the verified function-free expression domain.
pub open spec fn delete_views(statement: ast::Statement) -> Option<Seq<TokenView>> {
    match statement {
        ast::Statement::Delete { table, where_clause: None } => Some(seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
        ]),
        ast::Statement::Delete { table, where_clause: Some(expression) }
            if super::verified_expression::printable(expression)
                && !contains_all(expression) => Some(seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
            TokenView::Keyword(Keyword::Where),
        ] + super::verified_expression::print_expr(expression).unwrap()),
        _ => None,
    }
}

pub open spec fn delete_fuel(statement: ast::Statement) -> nat {
    match statement {
        ast::Statement::Delete { where_clause: Some(expression), .. } =>
            super::verified_expression::depth(expression),
        _ => 1,
    }
}

pub open spec fn parse_delete_views(tokens: Seq<TokenView>, fuel: nat)
    -> Option<ast::Statement> {
    if tokens.len() < 3
        || tokens[0] != TokenView::Keyword(Keyword::Delete)
        || tokens[1] != TokenView::Keyword(Keyword::From)
    {
        None
    } else {
        match tokens[2] {
            TokenView::Ident(table) => {
                if tokens.len() == 3 {
                    Some(ast::Statement::Delete { table, where_clause: None })
                } else if tokens.len() > 4
                    && tokens[3] == TokenView::Keyword(Keyword::Where)
                {
                    match super::verified_expression::parse_prefix(
                        tokens.drop_first().drop_first().drop_first().drop_first(),
                        fuel,
                    ) {
                        (Some(expression), rest) if rest.len() == 0 => Some(
                            ast::Statement::Delete {
                                table,
                                where_clause: Some(expression),
                            },
                        ),
                        _ => None,
                    }
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

pub proof fn delete_parse_with_fuel(statement: ast::Statement, fuel: nat)
    requires
        delete_views(statement).is_some(),
        fuel >= delete_fuel(statement),
    ensures parse_delete_views(delete_views(statement).unwrap(), fuel) == Some(statement),
{
    reveal(delete_views);
    reveal(delete_fuel);
    reveal(parse_delete_views);
    match statement {
        ast::Statement::Delete { table, where_clause: None } => {
            let tokens = seq![
                TokenView::Keyword(Keyword::Delete),
                TokenView::Keyword(Keyword::From),
                TokenView::Ident(table),
            ];
            assert(tokens.len() == 3);
            assert(tokens[0] == TokenView::Keyword(Keyword::Delete));
            assert(tokens[1] == TokenView::Keyword(Keyword::From));
            assert(tokens[2] == TokenView::Ident(table));
            assert(parse_delete_views(tokens, fuel)
                == Some(ast::Statement::Delete { table, where_clause: None }));
            assert(delete_views(statement) == Some(tokens));
            assert(statement == ast::Statement::Delete { table, where_clause: None });
            assert(parse_delete_views(delete_views(statement).unwrap(), fuel)
                == Some(statement));
        },
        ast::Statement::Delete { table, where_clause: Some(expression) } => {
            assert(super::verified_expression::prefix_boundary(Seq::empty()));
            super::verified_expression::lemma_parse_print_prefix(
                &expression,
                Seq::empty(),
                fuel,
            );
            let body = super::verified_expression::print_expr(expression).unwrap();
            assert(super::verified_expression::parse_prefix(body, fuel)
                == (Some(expression), Seq::empty()));
            if body.len() == 0 {
                reveal_with_fuel(super::verified_expression::parse_prefix, 1);
                assert(false);
            }
            let tokens = seq![
                TokenView::Keyword(Keyword::Delete),
                TokenView::Keyword(Keyword::From),
                TokenView::Ident(table),
                TokenView::Keyword(Keyword::Where),
            ] + body;
            assert(tokens.len() > 4);
            assert(tokens.drop_first().drop_first().drop_first().drop_first() =~= body);
            assert(delete_views(statement) == Some(tokens));
            assert(parse_delete_views(tokens, fuel) == Some(
                ast::Statement::Delete { table, where_clause: Some(expression) },
            ));
            assert(statement
                == ast::Statement::Delete { table, where_clause: Some(expression) });
        },
        _ => assert(false),
    }
    assert(parse_delete_views(delete_views(statement).unwrap(), fuel) == Some(statement));
}

pub proof fn delete_roundtrip(statement: ast::Statement)
    requires delete_views(statement).is_some(),
    ensures parse_delete_views(delete_views(statement).unwrap(), delete_fuel(statement))
        == Some(statement),
{
    delete_parse_with_fuel(statement, delete_fuel(statement));
}

pub proof fn delete_injective(left: ast::Statement, right: ast::Statement)
    requires
        delete_views(left).is_some(),
        delete_views(right).is_some(),
        delete_views(left) == delete_views(right),
    ensures left == right,
{
    let fuel = if delete_fuel(left) >= delete_fuel(right) {
        delete_fuel(left)
    } else {
        delete_fuel(right)
    };
    delete_parse_with_fuel(left, fuel);
    delete_parse_with_fuel(right, fuel);
    assert(parse_delete_views(delete_views(left).unwrap(), fuel) == Some(left));
    assert(parse_delete_views(delete_views(right).unwrap(), fuel) == Some(right));
}

/// Whether the production expression printer can encode this AST without
/// changing its structure.
pub open spec fn printable_expression(expression: ast::Expression) -> bool
    decreases expression,
{
    match expression {
        ast::Expression::All => true,
        ast::Expression::Column(_, _) => true,
        ast::Expression::Literal(literal) => printable_literal(literal),
        ast::Expression::Function(_, arguments) =>
            forall|i: int| #![trigger printable_expression(arguments@[i])]
                0 <= i < arguments@.len() ==> printable_expression(arguments@[i]),
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
            | ast::Operator::Like(left, right) =>
                printable_expression(*left) && printable_expression(*right),
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => printable_expression(*inner),
            ast::Operator::Is(left, literal) =>
                printable_expression(*left) && match literal {
                    ast::Literal::Null => true,
                    ast::Literal::Float(value) =>
                        value.to_bits_spec() == float_trust::CANONICAL_NAN_BITS,
                    _ => false,
                },
        },
    }
}

/// Exact domain of the verified executable expression path. Function nodes stay
/// on the ordinary fallback because the spec-parser roundtrip cannot construct
/// or compare their `Vec<Expression>` payload; the executable-parser template in
/// `verified_function_list` is the path to lifting this restriction.
pub open spec fn core_printable_expression(expression: ast::Expression) -> bool
    decreases expression,
{
    match expression {
        ast::Expression::All | ast::Expression::Column(_, _) => true,
        ast::Expression::Literal(literal) => printable_literal(literal),
        ast::Expression::Function(_, _) => false,
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
            | ast::Operator::Like(left, right) =>
                core_printable_expression(*left) && core_printable_expression(*right),
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => core_printable_expression(*inner),
            ast::Operator::Is(left, literal) =>
                core_printable_expression(*left) && match literal {
                    ast::Literal::Null => true,
                    ast::Literal::Float(value) =>
                        value.to_bits_spec() == float_trust::CANONICAL_NAN_BITS,
                    _ => false,
                },
        },
    }
}

/// Whether an expression contains `*`. Statement positions use this to keep
/// `All` restricted to a direct, unaliased SELECT item.
pub open spec fn contains_all(expression: ast::Expression) -> bool
    decreases expression,
{
    match expression {
        ast::Expression::All => true,
        ast::Expression::Column(_, _) | ast::Expression::Literal(_) => false,
        ast::Expression::Function(_, arguments) =>
            exists|i: int| #![trigger contains_all(arguments@[i])]
                0 <= i < arguments@.len() && contains_all(arguments@[i]),
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
            | ast::Operator::Like(left, right) => contains_all(*left) || contains_all(*right),
            ast::Operator::Not(inner)
            | ast::Operator::Factorial(inner)
            | ast::Operator::Identity(inner)
            | ast::Operator::Negate(inner) => contains_all(*inner),
            ast::Operator::Is(left, _) => contains_all(*left),
        },
    }
}

/// Printer domain for expression positions outside the SELECT item list.
pub open spec fn printable_statement_expression(expression: ast::Expression) -> bool {
    printable_expression(expression) && !contains_all(expression)
}

/// Canonical FROM-item domain. Joins are left-deep, their right child is a
/// table, and only CROSS JOIN omits its predicate.
pub open spec fn printable_from(from: ast::From) -> bool
    decreases from,
{
    match from {
        ast::From::Table { .. } => true,
        ast::From::Join { left, right, join_type, predicate } =>
            printable_from(*left)
                && printable_from(*right)
                && matches!(*right, ast::From::Table { .. })
                && (matches!(join_type, ast::JoinType::Cross) <==> predicate.is_none())
                && match predicate {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                },
    }
}

/// Canonical CREATE TABLE column domain.
pub open spec fn printable_column(column: ast::Column) -> bool {
    match column.default {
        Some(expression) => printable_statement_expression(expression),
        None => true,
    }
}

/// Whether a production statement is in the canonical printer's domain.
pub open spec fn printable_statement(statement: ast::Statement) -> bool
    decreases statement,
{
    match statement {
        ast::Statement::Begin { .. }
        | ast::Statement::Commit
        | ast::Statement::Rollback
        | ast::Statement::DropTable { .. } => true,
        ast::Statement::Explain(inner) =>
            !matches!(*inner, ast::Statement::Explain(_)) && printable_statement(*inner),
        ast::Statement::CreateTable { columns, .. } =>
            columns@.len() > 0
                && forall|i: int| #![trigger printable_column(columns@[i])]
                    0 <= i < columns@.len() ==> printable_column(columns@[i]),
        ast::Statement::Delete { where_clause, .. } => match where_clause {
            Some(expression) => printable_statement_expression(expression),
            None => true,
        },
        ast::Statement::Insert { columns, values, .. } =>
            values@.len() > 0
                && match columns {
                    Some(names) => names@.len() > 0,
                    None => true,
                }
                && forall|row: int| #![trigger values@[row]]
                    0 <= row < values@.len() ==> {
                        let expressions = values@[row];
                        expressions@.len() > 0
                            && forall|i: int| #![trigger printable_statement_expression(expressions@[i])]
                                0 <= i < expressions@.len()
                                    ==> printable_statement_expression(expressions@[i])
                    },
        ast::Statement::Update { set, where_clause, .. } =>
            set@.len() > 0
                && forall|name: String| #![trigger set@.contains_key(name)]
                    set@.contains_key(name) ==> match set@[name] {
                        Some(expression) => printable_statement_expression(expression),
                        None => true,
                    }
                && match where_clause {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                },
        ast::Statement::Select {
            select,
            from,
            where_clause,
            group_by,
            having,
            order_by,
            limit,
            offset,
        } =>
            select@.len() > 0
                && forall|i: int| #![trigger select@[i]]
                    0 <= i < select@.len() ==> {
                        let item = select@[i];
                        if matches!(item.0, ast::Expression::All) {
                            item.1.is_none()
                        } else {
                            printable_statement_expression(item.0)
                        }
                    }
                && forall|i: int| #![trigger printable_from(from@[i])]
                    0 <= i < from@.len() ==> printable_from(from@[i])
                && match where_clause {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                }
                && forall|i: int| #![trigger printable_statement_expression(group_by@[i])]
                    0 <= i < group_by@.len()
                        ==> printable_statement_expression(group_by@[i])
                && match having {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                }
                && forall|i: int| #![trigger order_by@[i]]
                    0 <= i < order_by@.len()
                        ==> printable_statement_expression(order_by@[i].0)
                && match limit {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                }
                && match offset {
                    Some(expression) => printable_statement_expression(expression),
                    None => true,
                },
    }
}

pub proof fn direct_all_is_printable_but_not_a_statement_expression()
    ensures
        printable_expression(ast::Expression::All),
        !printable_statement_expression(ast::Expression::All),
{
}

pub proof fn transaction_statements_are_printable(read_only: bool, as_of: Option<u64>)
    ensures
        printable_statement(ast::Statement::Begin { read_only, as_of }),
        printable_statement(ast::Statement::Commit),
        printable_statement(ast::Statement::Rollback),
{
}

} // verus!
