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
        .prop_map(|(table, set, where_clause)| Statement::Update {
            table,
            set,
            order: ast::AssignOrder::placeholder(),
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
    "UPDATE t SET a = 1, b = 2 WHERE c = 3",
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

// ---------------------------------------------------------------------------
// Input-driven differential lenses.
//
// The proptest/corpus lenses above only feed *printer output* back through
// both parsers. The printer is deterministic and collapses several concrete
// syntaxes onto one canonical spelling (e.g. `NotEqual` always prints `!=`,
// never `<>`). So any concrete syntax the printer can never emit is invisible
// to those lenses — which is exactly how the `<>` regression slipped through.
//
// The lenses below feed concrete SQL *strings* directly to both parsers,
// covering the printer-unreachable space: alternative operator spellings,
// keyword aliases the printer normalises away, and malformed inputs that both
// parsers must reject identically.
// ---------------------------------------------------------------------------

/// A: Every lexer-producible operator spelling in expression position,
/// including the printer-unreachable `<>`. Both `<>` and `!=` must parse (and
/// to the same tree, since they share the `NotEqual` tag).
const OPERATOR_SPELLING_EXPR_CORPUS: &[&str] = &[
    // Not-equal: both spellings. `<>` is printer-unreachable.
    "1 <> 2",
    "1 != 2",
    "a <> b",
    "a != b",
    "a <> b AND c != d",
    "a != b OR c <> d",
    "1 <> 2 <> 3",
    "NOT a <> b",
    "(a <> b) = (c != d)",
    // Comparison operators.
    "a < b",
    "a <= b",
    "a > b",
    "a >= b",
    "a = b",
    // Arithmetic operators.
    "a + b",
    "a - b",
    "a * b",
    "a / b",
    "a ^ b",
    "a % b",
    // Postfix factorial.
    "a!",
    "a! <> b!",
    // IS [NOT] NULL / NAN.
    "a IS NULL",
    "a IS NOT NULL",
    "a IS NAN",
    "a IS NOT NAN",
    // Logical operators and LIKE.
    "a AND b",
    "a OR b",
    "NOT a",
    "a LIKE b",
    "NOT a LIKE b AND c",
];

/// A: Operator spellings in clause position (statement-level), so `<>` and
/// friends are exercised through the statement parser too.
const OPERATOR_SPELLING_STMT_CORPUS: &[&str] = &[
    "SELECT 1 <> 2",
    "SELECT 1 != 2",
    "SELECT a <> b AND c != d",
    "SELECT a <> b, c != d",
    "DELETE FROM t WHERE a <> 1",
    "DELETE FROM t WHERE a != 1",
    "UPDATE t SET x = 1 WHERE a <> b",
    "UPDATE t SET x = 1 WHERE a != b",
    "SELECT * FROM t WHERE a <> b OR c <> d",
    "SELECT a FROM t GROUP BY a HAVING count(a) <> 1",
    "SELECT a FROM t ORDER BY a <> b",
    "SELECT a! FROM t",
    "SELECT a IS NOT NULL FROM t",
];

#[test]
fn operator_spelling_corpus_agrees() {
    for expr in OPERATOR_SPELLING_EXPR_CORPUS {
        check_expression(expr);
    }
    for sql in OPERATOR_SPELLING_STMT_CORPUS {
        check_statement(sql);
    }
}

/// B: Keyword-alias / normalisation forms the printer collapses onto a single
/// canonical spelling: join spellings, `BEGIN [TRANSACTION]`, optional `AS`,
/// every datatype alias, and various numeric/keyword literal forms.
const KEYWORD_ALIAS_CORPUS: &[&str] = &[
    // Join spellings (printer canonicalises OUTER away, comma-join to CROSS).
    "SELECT * FROM a JOIN b ON a.id = b.id",
    "SELECT * FROM a INNER JOIN b ON a.id = b.id",
    "SELECT * FROM a LEFT JOIN b ON a.id = b.id",
    "SELECT * FROM a LEFT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a RIGHT JOIN b ON a.id = b.id",
    "SELECT * FROM a RIGHT OUTER JOIN b ON a.id = b.id",
    "SELECT * FROM a CROSS JOIN b",
    "SELECT * FROM a, b",
    "SELECT * FROM a, b, c",
    // BEGIN with and without the optional TRANSACTION keyword.
    "BEGIN",
    "BEGIN TRANSACTION",
    "BEGIN READ ONLY",
    "BEGIN TRANSACTION READ ONLY",
    "BEGIN READ WRITE",
    "BEGIN TRANSACTION READ WRITE",
    // Optional AS in select items and table aliases.
    "SELECT a b FROM t x",
    "SELECT a AS b FROM t AS x",
    "SELECT a AS b FROM t x",
    "SELECT a b FROM t AS x",
    // Datatype aliases (BOOL/BOOLEAN, FLOAT/DOUBLE, INT/INTEGER,
    // STRING/TEXT/VARCHAR).
    "CREATE TABLE t (a BOOL)",
    "CREATE TABLE t (a BOOLEAN)",
    "CREATE TABLE t (a FLOAT)",
    "CREATE TABLE t (a DOUBLE)",
    "CREATE TABLE t (a INT)",
    "CREATE TABLE t (a INTEGER)",
    "CREATE TABLE t (a STRING)",
    "CREATE TABLE t (a TEXT)",
    "CREATE TABLE t (a VARCHAR)",
    // Float keyword literals.
    "SELECT INFINITY",
    "SELECT NAN",
    "SELECT INFINITY, NAN",
    // Number forms.
    "SELECT 007",
    "SELECT 1.",
    "SELECT 1.5",
    "SELECT 1e5",
    "SELECT 1E5",
    "SELECT 1e+5",
    "SELECT 1e-5",
    "SELECT 1.5e10",
];

#[test]
fn keyword_alias_corpus_agrees() {
    for sql in KEYWORD_ALIAS_CORPUS {
        check_statement(sql);
    }
}

/// C: Source-level string generator. Rather than printing an AST, this picks
/// among alternative *spellings* at the string level — so it structurally
/// reaches the printer-unreachable space (`<>`, `INNER JOIN`, optional `AS`,
/// optional `TRANSACTION`, datatype aliases) that the hand-written A/B corpora
/// only sample.
fn sql_operand() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("a".to_string()),
        Just("b".to_string()),
        Just("1".to_string()),
        Just("2".to_string()),
        Just("t.x".to_string()),
    ]
}

/// Not-equal spelled either way, plus the other comparison/arithmetic ops.
fn binary_op_spelling() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("<>"),
        Just("!="),
        Just("<"),
        Just("<="),
        Just(">"),
        Just(">="),
        Just("="),
        Just("+"),
        Just("-"),
        Just("*"),
        Just("/"),
        Just("^"),
        Just("%"),
        Just("AND"),
        Just("OR"),
        Just("LIKE"),
    ]
}

/// A source-level expression: an operand, or two operands joined by a
/// randomly-spelled binary operator, or a postfix `!`, or an `IS` predicate.
fn source_expression() -> impl Strategy<Value = String> {
    prop_oneof![
        sql_operand(),
        (sql_operand(), binary_op_spelling(), sql_operand())
            .prop_map(|(l, op, r)| format!("{l} {op} {r}")),
        sql_operand().prop_map(|e| format!("{e}!")),
        (
            sql_operand(),
            prop_oneof![Just("IS"), Just("IS NOT")],
            prop_oneof![Just("NULL"), Just("NAN")],
        )
            .prop_map(|(e, is, tail)| format!("{e} {is} {tail}")),
    ]
}

/// A source-level FROM clause choosing among join spellings and comma joins.
fn source_from() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("a".to_string()),
        Just("a, b".to_string()),
        prop_oneof![
            Just("JOIN"),
            Just("INNER JOIN"),
            Just("LEFT JOIN"),
            Just("LEFT OUTER JOIN"),
            Just("RIGHT JOIN"),
            Just("RIGHT OUTER JOIN"),
            Just("CROSS JOIN"),
        ]
        .prop_map(|join| {
            if join == "CROSS JOIN" {
                format!("a {join} b")
            } else {
                format!("a {join} b ON a.id = b.id")
            }
        }),
    ]
}

fn source_datatype() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("BOOL"),
        Just("BOOLEAN"),
        Just("FLOAT"),
        Just("DOUBLE"),
        Just("INT"),
        Just("INTEGER"),
        Just("STRING"),
        Just("TEXT"),
        Just("VARCHAR"),
    ]
}

/// A source-level statement choosing among alias/normalisation spellings.
fn source_statement() -> impl Strategy<Value = String> {
    prop_oneof![
        // SELECT with an optional-AS alias and a source-generated expression.
        (source_expression(), prop_oneof![Just(""), Just(" AS c"), Just(" c")])
            .prop_map(|(e, alias)| format!("SELECT {e}{alias}")),
        // SELECT ... FROM <join spelling> WHERE <expr>.
        (source_from(), source_expression())
            .prop_map(|(from, e)| format!("SELECT * FROM {from} WHERE {e}")),
        // DELETE / UPDATE exercising the WHERE-clause expression parser.
        source_expression().prop_map(|e| format!("DELETE FROM t WHERE {e}")),
        source_expression().prop_map(|e| format!("UPDATE t SET x = 1 WHERE {e}")),
        // BEGIN with optional TRANSACTION.
        prop_oneof![Just("BEGIN"), Just("BEGIN TRANSACTION")].prop_map(String::from),
        // CREATE TABLE with a datatype alias.
        source_datatype().prop_map(|dt| format!("CREATE TABLE t (a {dt})")),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// C: feed source-level expression strings (not printer output) to both
    /// parsers and assert agreement.
    #[test]
    fn source_expression_parsers_agree(expr in source_expression()) {
        check_expression(&expr);
    }

    /// C: feed source-level statement strings (not printer output) to both
    /// parsers and assert agreement.
    #[test]
    fn source_statement_parsers_agree(sql in source_statement()) {
        check_statement(&sql);
    }
}

/// D: Malformed inputs where both parsers must REJECT with matching messages
/// (modulo the single documented `IS` exemption). `check_*` already asserts
/// error-message parity; if a NEW divergence beyond the `IS` one surfaces here
/// the test panics rather than silently widening the exemption.
const ERROR_PARITY_EXPR_CORPUS: &[&str] = &[
    "1 +", "1 <> <>", "<> 1", "* 1", ")(", "(1 + 2", "1 + 2)", "a AND", "AND a", "1 2", "IS NULL",
    "f(", "f(a,", "(", ")", "!",
];

const ERROR_PARITY_STMT_CORPUS: &[&str] = &[
    "SELECT 1 +",
    "SELECT * FROM",
    "SELECT",
    "UPDATE",
    "DELETE FROM",
    "INSERT INTO t",
    "SELECT )( ",
    "SELECT 1 <> <>",
    "SELECT * FROM a JOIN b",
    "CREATE TABLE t",
    "CREATE TABLE t (",
    "SELECT 1 2 3",
    "DELETE FROM t WHERE",
    "UPDATE t SET",
    "SELECT * FROM a INNER b",
];

#[test]
fn error_parity_corpus_agrees() {
    for expr in ERROR_PARITY_EXPR_CORPUS {
        check_expression(expr);
    }
    for sql in ERROR_PARITY_STMT_CORPUS {
        check_statement(sql);
    }
}

/// E: Regression guard. Pins the `<>` not-equal class into the input-driven
/// harness so it cannot silently regress again: without the parser fix these
/// assertions fail with "legacy accepted but verified rejected". `<>` is
/// printer-unreachable, so ONLY the input-driven lenses (this one plus the A/C
/// lenses above) can catch it — the printer-based proptest lenses never emit
/// `<>`.
#[test]
fn not_equal_lt_gt_spelling_regression_guard() {
    // Bare `<>` in expression position.
    check_expression("1 <> 2");
    // `<>` alongside `!=` must produce identical trees.
    check_expression("a <> b");
    check_expression("a != b");
    // `<>` through each statement-level clause parser.
    check_statement("SELECT 1 <> 2");
    check_statement("DELETE FROM t WHERE a <> 1");
    check_statement("UPDATE t SET x = 1 WHERE a <> b");
    check_statement("SELECT * FROM t WHERE a <> b");
}
