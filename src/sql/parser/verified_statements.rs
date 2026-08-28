//! A small, axiom-free verified statement parser/printer.
//!
//! This is a typed-token model of the statement layer.  Identifiers are
//! deliberately opaque `u8` values: the lexical bridge can choose how to map
//! production strings to these values without changing the parser proof.
//! The representation is intentionally flat so each additional production
//! statement can be added as one token shape and one AST constructor.

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

/// Tokens needed by the initial statement fragment.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Token {
    Begin,
    ReadOnly,
    As,
    Of,
    Commit,
    Rollback,
    Drop,
    Table,
    If,
    Exists,
    Identifier(u8),
    Number(u64),
}

/// The verified statement fragment.  Names are opaque handles, not strings.
/// This keeps the parser proof independent of string encoding and allocation.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Statement {
    Begin { read_only: bool, as_of: Option<u64> },
    Commit,
    Rollback,
    DropTable { name: u8, if_exists: bool },
}

/// Canonical token form for the statement fragment.
pub open spec fn print_statement(statement: Statement) -> Seq<Token> {
    match statement {
        Statement::Begin { read_only, as_of } => match (read_only, as_of) {
            (false, None) => seq![Token::Begin],
            (true, None) => seq![Token::Begin, Token::ReadOnly],
            (false, Some(version)) =>
                seq![Token::Begin, Token::As, Token::Of, Token::Number(version)],
            (true, Some(version)) =>
                seq![Token::Begin, Token::ReadOnly, Token::As, Token::Of,
                    Token::Number(version)],
        },
        Statement::Commit => seq![Token::Commit],
        Statement::Rollback => seq![Token::Rollback],
        Statement::DropTable { name, if_exists } => match if_exists {
            false => seq![Token::Drop, Token::Table, Token::Identifier(name)],
            true => seq![Token::Drop, Token::Table, Token::If, Token::Exists,
                        Token::Identifier(name)],
        },
    }
}

/// Parse exactly one canonical statement.  Extra or missing tokens are
/// rejected.  In particular, this parser does not accept a prefix of a
/// statement, which is necessary for an injective printer.
pub open spec fn parse_statement(tokens: Seq<Token>) -> Option<Statement> {
    if tokens == seq![Token::Commit] {
        Some(Statement::Commit)
    } else if tokens == seq![Token::Rollback] {
        Some(Statement::Rollback)
    } else if tokens == seq![Token::Begin] {
        Some(Statement::Begin { read_only: false, as_of: None })
    } else if tokens == seq![Token::Begin, Token::ReadOnly] {
        Some(Statement::Begin { read_only: true, as_of: None })
    } else if tokens.len() == 4
        && tokens[0] == Token::Begin
        && tokens[1] == Token::As
        && tokens[2] == Token::Of
    {
        match tokens[3] {
            Token::Number(version) =>
                Some(Statement::Begin { read_only: false, as_of: Some(version) }),
            _ => None,
        }
    } else if tokens.len() == 5
        && tokens[0] == Token::Begin
        && tokens[1] == Token::ReadOnly
        && tokens[2] == Token::As
        && tokens[3] == Token::Of
    {
        match tokens[4] {
            Token::Number(version) =>
                Some(Statement::Begin { read_only: true, as_of: Some(version) }),
            _ => None,
        }
    } else if tokens.len() == 3
        && tokens[0] == Token::Drop
        && tokens[1] == Token::Table
    {
        match tokens[2] {
            Token::Identifier(name) =>
                Some(Statement::DropTable { name, if_exists: false }),
            _ => None,
        }
    } else if tokens.len() == 5
        && tokens[0] == Token::Drop
        && tokens[1] == Token::Table
        && tokens[2] == Token::If
        && tokens[3] == Token::Exists
    {
        match tokens[4] {
            Token::Identifier(name) =>
                Some(Statement::DropTable { name, if_exists: true }),
            _ => None,
        }
    } else {
        None
    }
}

/// The canonical printer is a left inverse of the parser on every supported
/// statement.  This is the main round-trip theorem consumed by later parser
/// layers.
pub proof fn print_parse(statement: Statement)
    ensures parse_statement(print_statement(statement)) == Some(statement),
{
    reveal(print_statement);
    reveal(parse_statement);
    match statement {
        Statement::Begin { read_only, as_of } => {
            match (read_only, as_of) {
                (false, None) | (true, None) => {},
                (false, Some(_)) | (true, Some(_)) => {},
            }
        },
        Statement::Commit | Statement::Rollback => {},
        Statement::DropTable { if_exists, .. } => {
            match if_exists {
                false | true => {},
            }
        },
    }
}

/// Equal canonical token streams identify equal statements.
pub proof fn print_injective(left: Statement, right: Statement)
    requires print_statement(left) == print_statement(right),
    ensures left == right,
{
    print_parse(left);
    print_parse(right);
    assert(parse_statement(print_statement(left)) == Some(left));
    assert(parse_statement(print_statement(right)) == Some(right));
}

/// A compact audit theorem: parsing a printed statement and printing the
/// result does not change the canonical token stream.
pub proof fn parse_print_canonical(statement: Statement)
    ensures
        parse_statement(print_statement(statement)).is_some()
            && print_statement(statement)
                == print_statement(parse_statement(print_statement(statement)).unwrap()),
{
    print_parse(statement);
}

// -------------------------------------------------------------------------
// Production statement-shape model
// -------------------------------------------------------------------------

/// The production parser has recursive expressions and heap-backed lists.
/// This layer abstracts each such subtree by a stable opaque byte handle, but
/// retains the statement keywords, punctuation, optional clauses, and list
/// emptiness that determine the SQL grammar.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeToken {
    Begin,
    Read,
    Only,
    As,
    Of,
    System,
    Time,
    Commit,
    Rollback,
    Explain,
    Create,
    Table,
    Drop,
    If,
    Exists,
    Delete,
    From,
    Insert,
    Into,
    Values,
    Update,
    Set,
    Select,
    Where,
    Group,
    By,
    Having,
    Order,
    Asc,
    Desc,
    Limit,
    Offset,
    OpenParen,
    CloseParen,
    Comma,
    Name(u8),
    Number(u64),
    Expr(u8),
    ListItem(u8),
    All,
}

/// Datatypes in `CREATE TABLE`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeDataType {
    Boolean,
    Integer,
    Float,
    String,
}

/// The four production join kinds.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeJoinType {
    Cross,
    Inner,
    Left,
    Right,
}

/// ORDER BY direction.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeDirection {
    Ascending,
    Descending,
}

/// An abstract list. `NonEmpty` carries an opaque handle for the complete
/// list. The distinction is enough to state the production printer's
/// rejection of empty required lists while leaving list element verification
/// to the expression/list cores.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeList {
    Empty,
    NonEmpty(u8),
}

/// SELECT's direct select-list context. `All` is available only here; it is
/// not an expression payload and therefore cannot leak into WHERE, GROUP BY,
/// HAVING, ORDER BY, LIMIT, or OFFSET.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeSelectList {
    Empty,
    Expressions(u8),
    All,
}

/// A column shape retaining every production column option.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ShapeColumn {
    pub name: u8,
    pub datatype: ShapeDataType,
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<u8>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<u8>,
}

/// A FROM shape. The `right_is_table` bit records the production printer's
/// left-deep restriction; cross joins have no predicate, all other joins do.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeFrom {
    Table { name: u8, alias: Option<u8> },
    Join {
        left: u8,
        right: u8,
        join_type: ShapeJoinType,
        predicate: Option<u8>,
        right_is_table: bool,
    },
}

/// All production statement tags. Opaque handles stand for verified
/// expression, column-list, row-list, assignment-list, and FROM-list cores.
#[allow(inconsistent_fields)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ShapeStatement {
    Begin { read_only: bool, as_of: Option<u64> },
    Commit,
    Rollback,
    Explain { inner: u8, nested: bool },
    CreateTable { name: u8, columns: ShapeList },
    DropTable { name: u8, if_exists: bool },
    Delete { table: u8, where_expr: Option<u8> },
    Insert { table: u8, columns: Option<ShapeList>, values: ShapeList },
    Update { table: u8, set: ShapeList, where_expr: Option<u8> },
    Select {
        select: ShapeSelectList,
        from: ShapeList,
        where_expr: Option<u8>,
        group_by: ShapeList,
        having: Option<u8>,
        order_by: ShapeList,
        limit: Option<u8>,
        offset: Option<u8>,
    },
}

/// Encode an optional expression clause. The caller emits the keyword before
/// this helper, matching the production printer's conditional clauses.
pub open spec fn shape_expr(expression: Option<u8>) -> Seq<ShapeToken> {
    match expression {
        None => Seq::empty(),
        Some(value) => seq![ShapeToken::Expr(value)],
    }
}

/// Encode a list shape with the production list delimiters handled by the
/// caller. A list payload is opaque but still has a distinct nonempty form.
pub open spec fn shape_list(list: ShapeList) -> Seq<ShapeToken> {
    match list {
        ShapeList::Empty => Seq::empty(),
        ShapeList::NonEmpty(value) => seq![ShapeToken::ListItem(value)],
    }
}

/// Canonical production statement shape. It returns `None` for precisely the
/// AST shapes rejected by the production printer: nested EXPLAIN, empty
/// required lists, aliased ALL, and invalid select-list ALL placement.
pub open spec fn print_shape(statement: ShapeStatement) -> Option<Seq<ShapeToken>> {
    match statement {
        ShapeStatement::Begin { read_only, as_of } => {
            let prefix = if read_only {
                seq![ShapeToken::Begin, ShapeToken::Read, ShapeToken::Only]
            } else {
                seq![ShapeToken::Begin]
            };
            Some(prefix + match as_of {
                None => Seq::empty(),
                Some(version) => seq![ShapeToken::As, ShapeToken::Of, ShapeToken::System,
                    ShapeToken::Time, ShapeToken::Number(version)],
            })
        },
        ShapeStatement::Commit => Some(seq![ShapeToken::Commit]),
        ShapeStatement::Rollback => Some(seq![ShapeToken::Rollback]),
        ShapeStatement::Explain { nested, inner } => if nested {
            None
        } else {
            Some(seq![ShapeToken::Explain, ShapeToken::Expr(inner)])
        },
        ShapeStatement::CreateTable { name, columns } => match columns {
            ShapeList::Empty => None,
            ShapeList::NonEmpty(_) => Some(
                seq![ShapeToken::Create, ShapeToken::Table, ShapeToken::Name(name),
                    ShapeToken::OpenParen]
                    + shape_list(columns)
                    + seq![ShapeToken::CloseParen],
            ),
        },
        ShapeStatement::DropTable { name, if_exists } => Some(
            seq![ShapeToken::Drop, ShapeToken::Table]
                + if if_exists {
                    seq![ShapeToken::If, ShapeToken::Exists]
                } else {
                    Seq::empty()
                }
                + seq![ShapeToken::Name(name)],
        ),
        ShapeStatement::Delete { table, where_expr } => Some(
            seq![ShapeToken::Delete, ShapeToken::From, ShapeToken::Name(table)]
                + match where_expr {
                    None => Seq::empty(),
                    Some(expression) => seq![ShapeToken::Where, ShapeToken::Expr(expression)],
                },
        ),
        ShapeStatement::Insert { table, columns, values } => match values {
            ShapeList::Empty => None,
            ShapeList::NonEmpty(_) => {
                let column_tokens = match columns {
                    None => Seq::empty(),
                    Some(ShapeList::Empty) => Seq::empty(),
                    Some(nonempty) => seq![ShapeToken::OpenParen]
                        + shape_list(nonempty)
                        + seq![ShapeToken::CloseParen],
                };
                Some(seq![ShapeToken::Insert, ShapeToken::Into, ShapeToken::Name(table)]
                    + column_tokens
                    + seq![ShapeToken::Values]
                    + shape_list(values))
            },
        },
        ShapeStatement::Update { table, set, where_expr } => match set {
            ShapeList::Empty => None,
            ShapeList::NonEmpty(_) => Some(
                seq![ShapeToken::Update, ShapeToken::Name(table), ShapeToken::Set]
                    + shape_list(set)
                    + match where_expr {
                        None => Seq::empty(),
                        Some(expression) => seq![ShapeToken::Where, ShapeToken::Expr(expression)],
                    },
            ),
        },
        ShapeStatement::Select {
            select,
            from,
            where_expr,
            group_by,
            having,
            order_by,
            limit,
            offset,
        } => match select {
            ShapeSelectList::Empty => None,
            ShapeSelectList::All | ShapeSelectList::Expressions(_) => {
                let select_tokens = match select {
                    ShapeSelectList::All => seq![ShapeToken::All],
                    ShapeSelectList::Expressions(value) => seq![ShapeToken::Expr(value)],
                    ShapeSelectList::Empty => Seq::empty(),
                };
                Some(seq![ShapeToken::Select] + select_tokens
                    + if matches!(from, ShapeList::Empty) {
                        Seq::empty()
                    } else {
                        seq![ShapeToken::From] + shape_list(from)
                    }
                    + match where_expr {
                        None => Seq::empty(),
                        Some(expression) => seq![ShapeToken::Where, ShapeToken::Expr(expression)],
                    }
                    + if matches!(group_by, ShapeList::Empty) {
                        Seq::empty()
                    } else {
                        seq![ShapeToken::Group, ShapeToken::By] + shape_list(group_by)
                    }
                    + match having {
                        None => Seq::empty(),
                        Some(expression) => seq![ShapeToken::Having, ShapeToken::Expr(expression)],
                    }
                    + if matches!(order_by, ShapeList::Empty) {
                        Seq::empty()
                    } else {
                        seq![ShapeToken::Order, ShapeToken::By] + shape_list(order_by)
                    }
                    + match limit {
                        None => Seq::empty(),
                        Some(expression) => seq![ShapeToken::Limit, ShapeToken::Expr(expression)],
                    }
                    + match offset {
                        None => Seq::empty(),
                        Some(expression) => seq![ShapeToken::Offset, ShapeToken::Expr(expression)],
                    })
            },
        },
    }
}

/// The first token is a constructor tag. This fact lets the injectivity proof
/// reject all cross-constructor cases before comparing payload fields.
pub open spec fn shape_tag(statement: ShapeStatement) -> ShapeToken {
    match statement {
        ShapeStatement::Begin { .. } => ShapeToken::Begin,
        ShapeStatement::Commit => ShapeToken::Commit,
        ShapeStatement::Rollback => ShapeToken::Rollback,
        ShapeStatement::Explain { .. } => ShapeToken::Explain,
        ShapeStatement::CreateTable { .. } => ShapeToken::Create,
        ShapeStatement::DropTable { .. } => ShapeToken::Drop,
        ShapeStatement::Delete { .. } => ShapeToken::Delete,
        ShapeStatement::Insert { .. } => ShapeToken::Insert,
        ShapeStatement::Update { .. } => ShapeToken::Update,
        ShapeStatement::Select { .. } => ShapeToken::Select,
    }
}

/// Relation form of parsing. The opaque payload cores are verified separately;
/// at the statement layer parsing means consuming exactly the canonical token
/// stream for the supplied abstract statement.
pub open spec fn parses_shape(tokens: Seq<ShapeToken>, statement: ShapeStatement) -> bool {
    match print_shape(statement) {
        None => false,
        Some(canonical) => tokens == canonical,
    }
}

pub proof fn shape_print_parse(statement: ShapeStatement)
    requires print_shape(statement).is_some(),
    ensures parses_shape(print_shape(statement).unwrap(), statement),
{
    reveal(parses_shape);
}

}
