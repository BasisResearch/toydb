use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

use vstd::prelude::*;

use crate::sql::types::DataType;

verus! {

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExDataType(DataType);

/// SQL statements are represented as an Abstract Syntax Tree (AST). The
/// statement is the root node of this tree, and describes the syntactic
/// structure of a SQL statement. It is built from a raw SQL string by the
/// parser, and passed on to the planner which validates it and builds an
/// execution plan from it.
#[allow(inconsistent_fields)]
#[derive(Debug, Eq, PartialEq)]
pub enum Statement {
    /// BEGIN: begins a new transaction.
    Begin {
        /// READ ONLY: if true, begin a read-only transaction.
        read_only: bool,
        /// AS OF: if given, the MVCC version to read at.
        as_of: Option<u64>,
    },
    /// COMMIT: commits a transaction.
    Commit,
    /// ROLLBACK: rolls back a transaction.
    Rollback,
    /// EXPLAIN: explains a SQL statement's execution plan.
    Explain(Box<Statement>),
    /// CREATE TABLE: creates a new table.
    CreateTable {
        /// The table name.
        name: String,
        /// Column specifications.
        columns: Vec<Column>,
    },
    /// DROP TABLE: drops a table.
    DropTable {
        /// The table to drop.
        name: String,
        /// IF EXISTS: if true, don't error if the table doesn't exist.
        if_exists: bool,
    },
    /// DELETE: deletes rows from a table.
    Delete {
        /// The table to delete from.
        table: String,
        /// WHERE: optional condition to match rows to delete.
        where_clause: Option<Expression>,
    },
    /// INSERT INTO: inserts new rows into a table.
    Insert {
        /// Table to insert into.
        table: String,
        /// Columns to insert values into. If None, all columns are used.
        columns: Option<Vec<String>>,
        /// Row values to insert.
        values: Vec<Vec<Expression>>,
    },
    /// UPDATE: updates rows in a table.
    Update {
        table: String,
        set: BTreeMap<String, Option<Expression>>, // column → value, None for default value
        where_clause: Option<Expression>,
    },
    /// SELECT: selects rows, possibly from a table.
    Select {
        /// Expressions to select, with an optional column alias.
        select: Vec<(Expression, Option<String>)>,
        /// FROM: tables to select from.
        from: Vec<From>,
        /// WHERE: optional condition to filter rows.
        where_clause: Option<Expression>,
        /// GROUP BY: expressions to group and aggregate by.
        group_by: Vec<Expression>,
        /// HAVING: expression to filter groups by.
        having: Option<Expression>,
        /// ORDER BY: expresisions to sort by, with direction.
        order_by: Vec<(Expression, Direction)>,
        /// OFFSET: row offset to start from.
        offset: Option<Expression>,
        /// LIMIT: maximum number of rows to return.
        limit: Option<Expression>,
    },
}

/// A FROM item.
#[allow(inconsistent_fields)]
#[derive(Debug, Eq, PartialEq)]
pub enum From {
    /// A table.
    Table {
        /// The table name.
        name: String,
        /// An optional alias for the table.
        alias: Option<String>,
    },
    /// A join of two or more tables (may be nested).
    Join {
        /// The left table to join,
        left: Box<From>,
        /// The right table to join.
        right: Box<From>,
        /// The join type.
        join_type: JoinType,
        /// The join condition. None for a cross join.
        predicate: Option<Expression>,
    },
}

/// A CREATE TABLE column definition.
#[derive(Debug, Eq, PartialEq)]
pub struct Column {
    pub name: String,
    pub datatype: DataType,
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<Expression>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

/// JOIN types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JoinType {
    Cross,
    Inner,
    Left,
    Right,
}

} // verus!

impl JoinType {
    // If true, the join is an outer join, where rows with no join matches are
    // emitted with a NULL match.
    pub fn is_outer(&self) -> bool {
        match self {
            Self::Left | Self::Right => true,
            Self::Cross | Self::Inner => false,
        }
    }
}

verus! {

/// ORDER BY direction.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Direction {
    #[default]
    Ascending,
    Descending,
}

} // verus!

impl Clone for Column {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            datatype: self.datatype,
            primary_key: self.primary_key,
            nullable: self.nullable,
            default: self.default.clone(),
            unique: self.unique,
            index: self.index,
            references: self.references.clone(),
        }
    }
}

impl Clone for Statement {
    fn clone(&self) -> Self {
        match self {
            Self::Begin { read_only, as_of } => {
                Self::Begin { read_only: *read_only, as_of: *as_of }
            }
            Self::Commit => Self::Commit,
            Self::Rollback => Self::Rollback,
            Self::Explain(statement) => Self::Explain(statement.clone()),
            Self::CreateTable { name, columns } => {
                Self::CreateTable { name: name.clone(), columns: columns.clone() }
            }
            Self::DropTable { name, if_exists } => {
                Self::DropTable { name: name.clone(), if_exists: *if_exists }
            }
            Self::Delete { table, where_clause } => {
                Self::Delete { table: table.clone(), where_clause: where_clause.clone() }
            }
            Self::Insert { table, columns, values } => Self::Insert {
                table: table.clone(),
                columns: columns.clone(),
                values: values.clone(),
            },
            Self::Update { table, set, where_clause } => Self::Update {
                table: table.clone(),
                set: set.clone(),
                where_clause: where_clause.clone(),
            },
            Self::Select {
                select,
                from,
                where_clause,
                group_by,
                having,
                order_by,
                limit,
                offset,
            } => Self::Select {
                select: select.clone(),
                from: from.clone(),
                where_clause: where_clause.clone(),
                group_by: group_by.clone(),
                having: having.clone(),
                order_by: order_by.clone(),
                limit: limit.clone(),
                offset: offset.clone(),
            },
        }
    }
}

impl Clone for From {
    fn clone(&self) -> Self {
        match self {
            Self::Table { name, alias } => Self::Table { name: name.clone(), alias: alias.clone() },
            Self::Join { left, right, join_type, predicate } => Self::Join {
                left: left.clone(),
                right: right.clone(),
                join_type: *join_type,
                predicate: predicate.clone(),
            },
        }
    }
}

verus! {

/// SQL expressions, e.g. `a + 7 > b`. Can be nested.
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum Expression {
    /// All columns, i.e. *.
    All,
    /// A column reference, optionally qualified with a table name.
    Column(Option<String>, String),
    /// A literal value.
    Literal(Literal),
    /// A function call (name and parameters).
    Function(String, Vec<Expression>),
    /// An operator.
    Operator(Operator),
}

/// Expression literal values.
#[derive(Debug)]
pub enum Literal {
    Null,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
}

} // verus!

/// To allow using expressions and literals in e.g. hashmaps, implement simple
/// equality by value for all types, including Null and f64::NAN. This only
/// checks that the values are the same, and ignores SQL semantics for e.g. NULL
/// and NaN (which is handled by SQL expression evaluation).
impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Boolean(l), Self::Boolean(r)) => l == r,
            (Self::Integer(l), Self::Integer(r)) => l == r,
            (Self::Float(l), Self::Float(r)) => l.to_bits() == r.to_bits(),
            (Self::String(l), Self::String(r)) => l == r,
            (_, _) => false,
        }
    }
}

impl Eq for Literal {}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Null => {}
            Self::Boolean(v) => v.hash(state),
            Self::Integer(v) => v.hash(state),
            Self::Float(v) => v.to_bits().hash(state),
            Self::String(v) => v.hash(state),
        }
    }
}

verus! {

/// Expression operators.
///
/// Since this is a recursive data structure, we have to box each child
/// expression, which incurs a heap allocation. There are clever ways to get
/// around this, but we keep it simple.
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum Operator {
    And(Box<Expression>, Box<Expression>), // a AND b
    Not(Box<Expression>),                  // NOT a
    Or(Box<Expression>, Box<Expression>),  // a OR b

    Equal(Box<Expression>, Box<Expression>),       // a = b
    GreaterThan(Box<Expression>, Box<Expression>), // a > b
    GreaterThanOrEqual(Box<Expression>, Box<Expression>), // a >= b
    Is(Box<Expression>, Literal),                  // IS NULL or IS NAN
    LessThan(Box<Expression>, Box<Expression>),    // a < b
    LessThanOrEqual(Box<Expression>, Box<Expression>), // a <= b
    NotEqual(Box<Expression>, Box<Expression>),    // a != b

    Add(Box<Expression>, Box<Expression>),          // a + b
    Divide(Box<Expression>, Box<Expression>),       // a / b
    Exponentiate(Box<Expression>, Box<Expression>), // a ^ b
    Factorial(Box<Expression>),                     // a!
    Identity(Box<Expression>),                      // +a
    Multiply(Box<Expression>, Box<Expression>),     // a * b
    Negate(Box<Expression>),                        // -a
    Remainder(Box<Expression>, Box<Expression>),    // a % b
    Subtract(Box<Expression>, Box<Expression>),     // a - b

    Like(Box<Expression>, Box<Expression>), // a LIKE b
}

} // verus!

impl Clone for Literal {
    fn clone(&self) -> Self {
        match self {
            Self::Null => Self::Null,
            Self::Boolean(value) => Self::Boolean(*value),
            Self::Integer(value) => Self::Integer(*value),
            Self::Float(value) => Self::Float(*value),
            Self::String(value) => Self::String(value.clone()),
        }
    }
}

impl Clone for Expression {
    fn clone(&self) -> Self {
        match self {
            Self::All => Self::All,
            Self::Column(table, column) => Self::Column(table.clone(), column.clone()),
            Self::Literal(literal) => Self::Literal(literal.clone()),
            Self::Function(name, arguments) => Self::Function(name.clone(), arguments.clone()),
            Self::Operator(operator) => Self::Operator(operator.clone()),
        }
    }
}

impl Clone for Operator {
    fn clone(&self) -> Self {
        match self {
            Self::And(lhs, rhs) => Self::And(lhs.clone(), rhs.clone()),
            Self::Not(expression) => Self::Not(expression.clone()),
            Self::Or(lhs, rhs) => Self::Or(lhs.clone(), rhs.clone()),
            Self::Equal(lhs, rhs) => Self::Equal(lhs.clone(), rhs.clone()),
            Self::GreaterThan(lhs, rhs) => Self::GreaterThan(lhs.clone(), rhs.clone()),
            Self::GreaterThanOrEqual(lhs, rhs) => {
                Self::GreaterThanOrEqual(lhs.clone(), rhs.clone())
            }
            Self::Is(expression, literal) => Self::Is(expression.clone(), literal.clone()),
            Self::LessThan(lhs, rhs) => Self::LessThan(lhs.clone(), rhs.clone()),
            Self::LessThanOrEqual(lhs, rhs) => Self::LessThanOrEqual(lhs.clone(), rhs.clone()),
            Self::NotEqual(lhs, rhs) => Self::NotEqual(lhs.clone(), rhs.clone()),
            Self::Add(lhs, rhs) => Self::Add(lhs.clone(), rhs.clone()),
            Self::Divide(lhs, rhs) => Self::Divide(lhs.clone(), rhs.clone()),
            Self::Exponentiate(lhs, rhs) => Self::Exponentiate(lhs.clone(), rhs.clone()),
            Self::Factorial(expression) => Self::Factorial(expression.clone()),
            Self::Identity(expression) => Self::Identity(expression.clone()),
            Self::Multiply(lhs, rhs) => Self::Multiply(lhs.clone(), rhs.clone()),
            Self::Negate(expression) => Self::Negate(expression.clone()),
            Self::Remainder(lhs, rhs) => Self::Remainder(lhs.clone(), rhs.clone()),
            Self::Subtract(lhs, rhs) => Self::Subtract(lhs.clone(), rhs.clone()),
            Self::Like(lhs, rhs) => Self::Like(lhs.clone(), rhs.clone()),
        }
    }
}

impl Expression {
    /// Walks the expression tree depth-first, calling a closure for every node.
    /// Halts and returns false if the closure returns false.
    pub fn walk(&self, visitor: &mut impl FnMut(&Expression) -> bool) -> bool {
        use Operator::*;

        if !visitor(self) {
            return false;
        }

        match self {
            Self::Operator(op) => match op {
                Add(lhs, rhs)
                | And(lhs, rhs)
                | Divide(lhs, rhs)
                | Equal(lhs, rhs)
                | Exponentiate(lhs, rhs)
                | GreaterThan(lhs, rhs)
                | GreaterThanOrEqual(lhs, rhs)
                | LessThan(lhs, rhs)
                | LessThanOrEqual(lhs, rhs)
                | Like(lhs, rhs)
                | Multiply(lhs, rhs)
                | NotEqual(lhs, rhs)
                | Or(lhs, rhs)
                | Remainder(lhs, rhs)
                | Subtract(lhs, rhs) => lhs.walk(visitor) && rhs.walk(visitor),

                Factorial(expr) | Identity(expr) | Is(expr, _) | Negate(expr) | Not(expr) => {
                    expr.walk(visitor)
                }
            },

            Self::Function(_, exprs) => exprs.iter().any(|expr| expr.walk(visitor)),

            Self::All | Self::Column(_, _) | Self::Literal(_) => true,
        }
    }

    /// Walks the expression tree depth-first while calling a closure until it
    /// returns true. This is the inverse of walk().
    pub fn contains(&self, visitor: &impl Fn(&Expression) -> bool) -> bool {
        !self.walk(&mut |expr| !visitor(expr))
    }

    /// Find and collects expressions for which the given closure returns true,
    /// adding them to c. Does not recurse into matching expressions.
    pub fn collect(&self, visitor: &impl Fn(&Expression) -> bool, exprs: &mut Vec<Expression>) {
        use Operator::*;

        if visitor(self) {
            exprs.push(self.clone());
            return;
        }

        match self {
            Self::Operator(op) => match op {
                Add(lhs, rhs)
                | And(lhs, rhs)
                | Divide(lhs, rhs)
                | Equal(lhs, rhs)
                | Exponentiate(lhs, rhs)
                | GreaterThan(lhs, rhs)
                | GreaterThanOrEqual(lhs, rhs)
                | LessThan(lhs, rhs)
                | LessThanOrEqual(lhs, rhs)
                | Like(lhs, rhs)
                | Multiply(lhs, rhs)
                | NotEqual(lhs, rhs)
                | Or(lhs, rhs)
                | Remainder(lhs, rhs)
                | Subtract(lhs, rhs) => {
                    lhs.collect(visitor, exprs);
                    rhs.collect(visitor, exprs);
                }
                Factorial(expr) | Identity(expr) | Is(expr, _) | Negate(expr) | Not(expr) => {
                    expr.collect(visitor, exprs);
                }
            },

            Self::Function(_, args) => args.iter().for_each(|arg| arg.collect(visitor, exprs)),

            Self::All | Self::Column(_, _) | Self::Literal(_) => {}
        }
    }
}

impl core::convert::From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        Self::Literal(literal)
    }
}

impl core::convert::From<Operator> for Expression {
    fn from(op: Operator) -> Self {
        Self::Operator(op)
    }
}

impl core::convert::From<Operator> for Box<Expression> {
    fn from(value: Operator) -> Self {
        Box::new(value.into())
    }
}
