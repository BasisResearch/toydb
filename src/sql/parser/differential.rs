
#![cfg(test)]

use super::ast::{self, Expression, Literal, Operator, Statement};
use super::{Parser, Token};
use crate::error::Result;

pub(crate) fn parse_new(sql: &str) -> Result<Statement> {
    Parser::parse(sql)
}

pub(crate) fn parse_expr_new(expr: &str) -> Result<Expression> {
    Parser::parse_expr(expr)
}

fn is_accepted_error_divergence(old: &str, new: &str) -> bool {
    new == "invalid input: unexpected token IS"
        && old.starts_with("invalid input: unexpected token ")
        && old != new
}

pub(crate) fn check_statement(sql: &str) {
    let old = Parser::parse_legacy(sql);
    let new = parse_new(sql);
    match (old, new) {
        (Ok(old), Ok(new)) => assert_eq!(
            old, new,
            "verified parser produced a different AST\n  sql: {sql:?}\n  old: {old:?}\n  new: {new:?}"
        ),
        (Err(old), Err(new)) => assert!(
            old.to_string() == new.to_string()
                || is_accepted_error_divergence(&old.to_string(), &new.to_string()),
            "verified parser produced a different error\n  sql: {sql:?}\n  old: {old}\n  new: {new}"
        ),
        (Ok(old), Err(err)) => panic!(
            "legacy accepted but verified rejected\n  sql: {sql:?}\n  ast: {old:?}\n  err: {err}"
        ),
        (Err(err), Ok(new)) => panic!(
            "legacy rejected but verified accepted\n  sql: {sql:?}\n  err: {err}\n  ast: {new:?}"
        ),
    }
}

pub(crate) fn check_expression(expr: &str) {
    let old = Parser::parse_expr_legacy(expr);
    let new = parse_expr_new(expr);
    match (old, new) {
        (Ok(old), Ok(new)) => assert_eq!(
            old, new,
            "verified parser produced a different expression AST\n  sql: {expr:?}\n  old: {old:?}\n  new: {new:?}"
        ),
        (Err(old), Err(new)) => assert!(
            old.to_string() == new.to_string()
                || is_accepted_error_divergence(&old.to_string(), &new.to_string()),
            "verified parser produced a different error\n  sql: {expr:?}\n  old: {old}\n  new: {new}"
        ),
        (Ok(old), Err(err)) => panic!(
            "legacy accepted but verified rejected\n  sql: {expr:?}\n  ast: {old:?}\n  err: {err}"
        ),
        (Err(err), Ok(new)) => panic!(
            "legacy rejected but verified accepted\n  sql: {expr:?}\n  err: {err}\n  ast: {new:?}"
        ),
    }
}

pub(crate) fn render_tokens(tokens: &[Token]) -> String {
    tokens
        .iter()
        .map(|token| match token {
            Token::Ident(name) => format!("\"{}\"", name.replace('"', "\"\"")),
            Token::String(value) => format!("'{}'", value.replace('\'', "''")),
            other => other.to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}


use proptest::prelude::*;

fn strings() -> impl Strategy<Value = String> {
    proptest::collection::vec(any::<char>(), 0..16).prop_map(|chars| chars.into_iter().collect())
}

fn expression_strategy(include_all: bool) -> BoxedStrategy<Expression> {
    let finite_float = (0u64..=0x7fef_ffff_ffff_ffff).prop_map(f64::from_bits);
    let atom = prop_oneof![
        (proptest::option::of(strings()), strings())
            .prop_map(|(table, column)| Expression::Column(table, column)),
        Just(Expression::Literal(Literal::Null)),
        any::<bool>().prop_map(|value| Expression::Literal(Literal::Boolean(value))),
        (0i64..=i64::MAX).prop_map(|value| Expression::Literal(Literal::Integer(value))),
        finite_float.prop_map(|value| Expression::Literal(Literal::Float(value))),
        strings().prop_map(|value| Expression::Literal(Literal::String(value))),
    ]
    .boxed();
    let leaf = if include_all { prop_oneof![Just(Expression::All), atom].boxed() } else { atom };

    leaf.prop_recursive(8, 192, 8, |inner| {
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

fn from_items() -> BoxedStrategy<ast::From> {
    use ast::{From, JoinType};

    let tables = (strings(), proptest::option::of(strings()))
        .prop_map(|(name, alias)| From::Table { name, alias })
        .boxed();
    let right_tables = tables.clone();
    tables
        .prop_recursive(4, 48, 2, move |left| {
            let cross = (left.clone(), right_tables.clone()).prop_map(|(left, right)| From::Join {
                left: Box::new(left),
                right: Box::new(right),
                join_type: JoinType::Cross,
                predicate: None,
            });
            let joined = (
                left,
                right_tables.clone(),
                prop_oneof![Just(JoinType::Inner), Just(JoinType::Left), Just(JoinType::Right),],
                statement_expressions(),
            )
                .prop_map(|(left, right, join_type, predicate)| From::Join {
                    left: Box::new(left),
                    right: Box::new(right),
                    join_type,
                    predicate: Some(predicate),
                });
            prop_oneof![cross, joined]
        })
        .boxed()
}

fn statements() -> BoxedStrategy<Statement> {
    use crate::sql::types::DataType;
    use ast::{Column, Direction};

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
            |(name, datatype, primary_key, nullable, default, unique, index, references)| Column {
                name,
                datatype,
                primary_key,
                nullable,
                default,
                unique,
                index,
                references,
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
        prop_oneof![Just(None), proptest::collection::vec(strings(), 1..5).prop_map(Some)];
    let insert = (
        strings(),
        insert_columns,
        proptest::collection::vec(proptest::collection::vec(statement_expressions(), 1..5), 1..5),
    )
        .prop_map(|(table, columns, values)| Statement::Insert { table, columns, values });
    let update = (
        strings(),
        proptest::collection::btree_map(
            strings(),
            proptest::option::of(statement_expressions()),
            1..5,
        ),
        proptest::option::of(statement_expressions()),
    )
        .prop_map(|(table, set, where_clause)| Statement::Update { table, set, where_clause });
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
        .prop_map(|(select, from, where_clause, group_by, having, order_by, limit, offset)| {
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
        });
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
    prop_oneof![base.clone(), base.prop_map(|statement| Statement::Explain(Box::new(statement))),]
        .boxed()
}


proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn expression_parsers_agree(expression in expressions()) {
        let tokens = super::print_expr(&expression)
            .expect("the strategy only generates parser-producible expressions");
        check_expression(&render_tokens(&tokens));
    }

    #[test]
    fn statement_parsers_agree(statement in statements()) {
        let tokens = super::print_statement(&statement)
            .expect("the strategy only generates parser-producible statements");
        check_statement(&render_tokens(&tokens));
    }

    #[test]
    fn expression_parsers_agree_minparens(expression in expressions()) {
        super::print_expr(&expression)
            .expect("the strategy only generates parser-producible expressions");
        let tokens = super::verified_minparen::print_min_expr(&expression);
        check_expression(&render_tokens(&tokens));
    }

    #[test]
    fn statement_parsers_agree_minparens(statement in statements()) {
        super::print_statement(&statement)
            .expect("the strategy only generates parser-producible statements");
        let tokens = super::verified_minparen_stmt::print_min_stmt(&statement);
        check_statement(&render_tokens(&tokens));
    }
}


const CONCRETE_SYNTAX_CORPUS: &[&str] = &[
    "SELECT 1 + 2 * 3",
    "SELECT 2 ^ 3 ^ 2 - 4 * 3",
    "SELECT a AND b OR c",
    "SELECT NOT a AND b",
    "SELECT -a + b",
    "SELECT a = b AND c != d",
    "SELECT 1 + NULL IS NULL",
    "SELECT a!",
    "SELECT a IS NOT NULL",
    "SELECT a LIKE b",
    "SELECT INFINITY, NAN",
    "SELECT *",
    "SELECT count(a), sum(b + 1)",
    "SELECT a b FROM t x",
    "SELECT a AS b FROM t AS x",
    "SELECT * FROM a JOIN b ON a.id = b.id",
    "SELECT * FROM a INNER JOIN b ON a.id = b.id",
    "SELECT * FROM a LEFT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a RIGHT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a CROSS JOIN b",
    "SELECT * FROM a, b",
    "BEGIN TRANSACTION READ ONLY",
    "BEGIN READ WRITE",
    "BEGIN AS OF SYSTEM TIME 42",
    "DROP TABLE IF EXISTS t",
    "UPDATE t SET a = 1, b = DEFAULT",
    "INSERT INTO t VALUES (1, 2), (3, 4)",
    "DELETE FROM t WHERE a > 1",
    "SELECT a FROM t GROUP BY a HAVING count(a) > 1 ORDER BY a DESC LIMIT 10 OFFSET 5",
];

#[test]
fn concrete_syntax_corpus_agrees() {
    for sql in CONCRETE_SYNTAX_CORPUS {
        check_statement(sql);
    }
}

const CONCRETE_EXPR_CORPUS: &[&str] = &[
    "1 + 2 * 3",
    "1 * 2 + 3",
    "2 ^ 3 ^ 2",
    "2 ^ 3 ^ 2 - 4 * 3",
    "1 - 2 - 3",
    "1 - 2 + 3",
    "a AND b OR c",
    "a OR b AND c",
    "NOT a AND b",
    "NOT NOT a",
    "-a + b",
    "- - a",
    "+a * -b",
    "a = b AND c != d",
    "a < b < c",
    "a IS NULL",
    "a IS NOT NULL",
    "a IS NAN",
    "a IS NOT NAN",
    "a IS b",
    "a IS 1",
    "a IS NOT b",
    "a!",
    "a! + b!",
    "1 + NULL IS NULL",
    "NOT a IS NULL",
    "a LIKE b AND c",
    "count(a)",
    "sum(a + b * c)",
    "f(g(h(x)))",
    "f(a, b, c)",
    "f()",
    "(1 + 2) * 3",
    "t.a + t.b",
    "INFINITY + NAN",
    "-2 ^ 2",
    "a >= b <= c",
    "a % b * c",
];

#[test]
fn concrete_expr_corpus_agrees() {
    for expr in CONCRETE_EXPR_CORPUS {
        check_expression(expr);
    }
}
