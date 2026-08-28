//! Differential-testing harness for the verified-parser cutover.
//!
//! The cutover (see `verus-parser-cutover-prompt.md`) replaces the unverified
//! recursive-descent parser in `parser.rs` with a Verus-verified parser,
//! feature by feature, without regressing any SQL the database accepts. Verus
//! proves the verified parser panic-/overflow-free and terminating; it does NOT
//! prove it grammatically equivalent to the old parser. That equivalence is
//! established *behaviourally*, by this harness: it runs both parsers on the
//! same input and asserts they agree — both accept with an identical
//! [`ast::Statement`]/[`ast::Expression`], or both reject.
//!
//! The old parser is the oracle and stays compiled and reachable throughout, so
//! the harness can gate every increment.
//!
//! # The seam
//!
//! [`parse_new`]/[`parse_expr_new`] name the "verified-path" side under test.
//! In Phase 1 they delegate to the legacy parser, so the harness is trivially
//! green (old vs old) and its plumbing — corpus wiring and generators — can be
//! validated before any behaviour changes. In later phases these seams route to
//! the verified exec parser (with a logged, tracked fallback to legacy for
//! forms it cannot yet handle), and the same assertions gate the change.

#![cfg(test)]

use super::ast::{self, Expression, Literal, Operator, Statement};
use super::{Lexer, Parser, Token, verified_precedence};
use crate::errinput;
use crate::error::Result;

/// The verified-path statement parser under test.
///
/// Phase 1: delegates to the legacy parser (`old == new`, trivially green).
/// Later phases repoint this at the verified exec parser.
pub(crate) fn parse_new(sql: &str) -> Result<Statement> {
    Parser::parse(sql)
}

/// The verified-path expression parser under test: lex with the production
/// lexer, then run the Verus-verified precedence-climbing parser
/// ([`verified_precedence`]). Requires the whole token vector to be consumed.
pub(crate) fn parse_expr_new(expr: &str) -> Result<Expression> {
    let tokens: Vec<Token> = Lexer::new(expr).collect::<Result<_>>()?;
    match verified_precedence::parse_expression(&tokens) {
        Some(expression) => Ok(expression),
        None => errinput!("failed to parse expression: {expr}"),
    }
}

/// Asserts the legacy and verified-path parsers agree on `sql`: both accept
/// with an identical AST, or both reject. Error *messages* are not compared —
/// only accept/reject and, on accept, AST equality.
pub(crate) fn check_statement(sql: &str) {
    let old = Parser::parse(sql);
    let new = parse_new(sql);
    match (old, new) {
        (Ok(old), Ok(new)) => assert_eq!(
            old, new,
            "verified parser produced a different AST\n  sql: {sql:?}\n  old: {old:?}\n  new: {new:?}"
        ),
        (Err(_), Err(_)) => {}
        (Ok(old), Err(err)) => panic!(
            "legacy accepted but verified rejected\n  sql: {sql:?}\n  ast: {old:?}\n  err: {err}"
        ),
        (Err(err), Ok(new)) => panic!(
            "legacy rejected but verified accepted\n  sql: {sql:?}\n  err: {err}\n  ast: {new:?}"
        ),
    }
}

/// Expression-level counterpart to [`check_statement`].
pub(crate) fn check_expression(expr: &str) {
    let old = Parser::parse_expr(expr);
    let new = parse_expr_new(expr);
    match (old, new) {
        (Ok(old), Ok(new)) => assert_eq!(
            old, new,
            "verified parser produced a different expression AST\n  sql: {expr:?}\n  old: {old:?}\n  new: {new:?}"
        ),
        (Err(_), Err(_)) => {}
        (Ok(old), Err(err)) => panic!(
            "legacy accepted but verified rejected\n  sql: {expr:?}\n  ast: {old:?}\n  err: {err}"
        ),
        (Err(err), Ok(new)) => panic!(
            "legacy rejected but verified accepted\n  sql: {expr:?}\n  err: {err}\n  ast: {new:?}"
        ),
    }
}

/// Serialises canonical tokens to SQL source text, quoting and escaping so the
/// lexer reproduces each token exactly. Mirrors `printer.rs`'s `render_tokens`:
/// `Token`'s `Display` is lossy for `Ident`/`String`, so always double-quote
/// identifiers and single-quote strings, and space-separate tokens (never
/// merging adjacent ones), making `print -> render -> lex -> parse` faithful.
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

// ---- generators ------------------------------------------------------------
//
// Self-contained proptest strategies covering the full accepted grammar. Kept
// local to the harness (rather than shared with `printer.rs`'s test module) so
// the cutover never has to touch a verified file.

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

fn from_items() -> BoxedStrategy<ast::From> {
    use ast::{From, JoinType};

    let tables = (strings(), proptest::option::of(strings()))
        .prop_map(|(name, alias)| From::Table { name, alias })
        .boxed();
    let right_tables = tables.clone();
    tables
        .prop_recursive(3, 32, 2, move |left| {
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

// ---- proptests -------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Old vs new agree on canonically-printed expressions rendered to SQL text.
    #[test]
    fn expression_parsers_agree(expression in expressions()) {
        let tokens = super::print_expr(&expression)
            .expect("the strategy only generates parser-producible expressions");
        check_expression(&render_tokens(&tokens));
    }

    /// Old vs new agree on canonically-printed statements rendered to SQL text.
    #[test]
    fn statement_parsers_agree(statement in statements()) {
        let tokens = super::print_statement(&statement)
            .expect("the strategy only generates parser-producible statements");
        check_statement(&render_tokens(&tokens));
    }
}

// ---- fixed corpus ----------------------------------------------------------

/// A hand-picked corpus of concrete-syntax SQL that the generators (which emit
/// only the canonical, fully-parenthesised printed form) do not reach:
/// precedence without parentheses, aliases without `AS`, join-keyword variants,
/// and optional keywords. This is the surface the verified parser must grow to
/// accept in later phases; today it just confirms old vs new agree.
const CONCRETE_SYNTAX_CORPUS: &[&str] = &[
    // Expression precedence / associativity (no parentheses).
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
    // Atoms the canonical printer reaches only via keywords.
    "SELECT INFINITY, NAN",
    "SELECT *",
    "SELECT count(a), sum(b + 1)",
    // Aliases without AS.
    "SELECT a b FROM t x",
    "SELECT a AS b FROM t AS x",
    // Join-keyword variants.
    "SELECT * FROM a JOIN b ON a.id = b.id",
    "SELECT * FROM a INNER JOIN b ON a.id = b.id",
    "SELECT * FROM a LEFT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a RIGHT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a CROSS JOIN b",
    "SELECT * FROM a, b",
    // Optional keywords.
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

/// Bare expressions with concrete precedence/associativity, function calls, and
/// postfix operators, feeding the verified precedence parser directly (the
/// statement corpus reaches it only through clauses). Every entry must build
/// the same AST as the production precedence-climbing parser.
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
