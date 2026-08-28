//! Full-grammar statement roundtrip in the mirror + executable style.
//!
//! This is the statement-level analogue of `verified_roundtrip`: `SStmt` is a
//! `Seq`-based mirror of `ast::Statement` whose expression children are the
//! expression mirror `SExpr` (through the existing `view_expr` bridge) and whose
//! containers (`Vec`s, join trees, the `BTreeMap` set) become `Seq`s. It carries
//! the canonical statement printer `sprint_stmt`, the fuel measure `sdepth_stmt`,
//! the mirror parser `sparse_stmt`, and the roundtrip proof
//! `lemma_sparse_stmt_sprint`. The bridge to production values is
//! `view_stmt: ast::Statement -> SStmt`; the executable layer
//! (`parse_stmt_exec` / `print_stmt_exec`) refines the mirror at the `view_stmt`
//! level, delegating every embedded expression to `parse_expr_exec` /
//! `print_expr_exec` from `verified_roundtrip`.
//!
//! Trust surface is unchanged: the only axioms remain the `float_trust`
//! boundary, reached transitively through the expression layer.
//!
//! The mirror grows one phase at a time (S0-S5 in
//! `verus-parser-roundtrip-plan.md`). Statement kinds that are not yet mirrored
//! map to `SStmt::Unsupported`, which is outside the printable domain, so the
//! roundtrip lemma never has to reason about them.

#![allow(dead_code, unused_variables)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::{
    all_printable_se, boundary, lemma_sparse_args_sprint, lemma_sparse_sprint, printable_se, sdepth,
    slist_depth, sparse, sparse_args, sprint, sprint_args, view_args, view_expr, SExpr,
};
#[allow(unused_imports)]
use super::{ast, verified_integer, verified_production, verified_roundtrip, Keyword};
#[allow(unused_imports)]
use crate::sql::types::DataType;

verus! {

// ---- Seq-based mirror of the statement grammar (grown per phase S0-S5) ------

/// Mirror of `ast::Statement`. Expression children are `SExpr` (via `view_expr`)
/// and containers become `Seq`s. `Unsupported` is the placeholder for statement
/// kinds not yet mirrored; it is outside `printable_stmt`, so the roundtrip
/// proof never touches it.
pub enum SStmt {
    Begin { read_only: bool, as_of: Option<u64> },
    Commit,
    Rollback,
    CreateTable { name: String, columns: Seq<SColumn> },
    DropTable { name: String, if_exists: bool },
    Delete { table: String, where_clause: Option<SExpr> },
    Insert { table: String, columns: Option<Seq<String>>, values: Seq<Seq<SExpr>> },
    Explain(Box<SStmt>),
    Unsupported,
}

/// View a `Vec<Vec<Expression>>` row list as `Seq<Seq<SExpr>>`.
pub open spec fn view_rows(rows: Seq<Vec<ast::Expression>>) -> Seq<Seq<SExpr>>
    decreases rows,
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        seq![view_args(rows[0]@)] + view_rows(rows.drop_first())
    }
}

/// Mirror of `ast::Column`: identical except the `default` expression becomes an
/// `SExpr`. `datatype` is carried directly (`DataType` is `Copy` and has an
/// external type spec).
pub struct SColumn {
    pub name: String,
    pub datatype: DataType,
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<SExpr>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

pub open spec fn view_column(c: ast::Column) -> SColumn {
    SColumn {
        name: c.name,
        datatype: c.datatype,
        primary_key: c.primary_key,
        nullable: c.nullable,
        default: match c.default {
            Some(e) => Some(view_expr(e)),
            None => None,
        },
        unique: c.unique,
        index: c.index,
        references: c.references,
    }
}

pub open spec fn view_columns(cols: Seq<ast::Column>) -> Seq<SColumn>
    decreases cols,
{
    if cols.len() == 0 {
        Seq::empty()
    } else {
        seq![view_column(cols[0])] + view_columns(cols.drop_first())
    }
}

/// Structural view of a production statement as a mirror statement.
pub open spec fn view_stmt(s: ast::Statement) -> SStmt
    decreases s,
{
    match s {
        ast::Statement::Begin { read_only, as_of } => SStmt::Begin { read_only, as_of },
        ast::Statement::Commit => SStmt::Commit,
        ast::Statement::Rollback => SStmt::Rollback,
        ast::Statement::CreateTable { name, columns } =>
            SStmt::CreateTable { name, columns: view_columns(columns@) },
        ast::Statement::DropTable { name, if_exists } => SStmt::DropTable { name, if_exists },
        ast::Statement::Delete { table, where_clause } => SStmt::Delete {
            table,
            where_clause: match where_clause {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
        ast::Statement::Insert { table, columns, values } => SStmt::Insert {
            table,
            columns: match columns {
                Some(cols) => Some(cols@),
                None => None,
            },
            values: view_rows(values@),
        },
        ast::Statement::Explain(inner) => SStmt::Explain(Box::new(view_stmt(*inner))),
        _ => SStmt::Unsupported,
    }
}

// ---- column codec (S2) -----------------------------------------------------

pub open spec fn datatype_kw(d: DataType) -> TokenView {
    match d {
        DataType::Boolean => TokenView::Keyword(Keyword::Boolean),
        DataType::Integer => TokenView::Keyword(Keyword::Integer),
        DataType::Float => TokenView::Keyword(Keyword::Float),
        DataType::String => TokenView::Keyword(Keyword::String),
    }
}

pub open spec fn parse_datatype_kw(t: TokenView) -> Option<DataType> {
    match t {
        TokenView::Keyword(Keyword::Boolean) => Some(DataType::Boolean),
        TokenView::Keyword(Keyword::Integer) => Some(DataType::Integer),
        TokenView::Keyword(Keyword::Float) => Some(DataType::Float),
        TokenView::Keyword(Keyword::String) => Some(DataType::String),
        _ => None,
    }
}

pub open spec fn printable_column(c: SColumn) -> bool {
    match c.default {
        Some(e) => printable_se(e),
        None => true,
    }
}

pub open spec fn all_printable_columns(cols: Seq<SColumn>) -> bool
    decreases cols,
{
    if cols.len() == 0 {
        true
    } else {
        printable_column(cols[0]) && all_printable_columns(cols.drop_first())
    }
}

/// The optional-clause tokens, in canonical order. DEFAULT is emitted last so
/// the embedded expression's tail is always the column terminator (comma or
/// close-paren), making its boundary trivial.
pub open spec fn col_pk_toks(c: SColumn) -> Seq<TokenView> {
    if c.primary_key {
        seq![TokenView::Keyword(Keyword::Primary), TokenView::Keyword(Keyword::Key)]
    } else {
        Seq::empty()
    }
}

pub open spec fn col_null_toks(c: SColumn) -> Seq<TokenView> {
    match c.nullable {
        Some(true) => seq![TokenView::Keyword(Keyword::Null)],
        Some(false) => seq![TokenView::Keyword(Keyword::Not), TokenView::Keyword(Keyword::Null)],
        None => Seq::empty(),
    }
}

pub open spec fn col_unique_toks(c: SColumn) -> Seq<TokenView> {
    if c.unique { seq![TokenView::Keyword(Keyword::Unique)] } else { Seq::empty() }
}

pub open spec fn col_index_toks(c: SColumn) -> Seq<TokenView> {
    if c.index { seq![TokenView::Keyword(Keyword::Index)] } else { Seq::empty() }
}

pub open spec fn col_ref_toks(c: SColumn) -> Seq<TokenView> {
    match c.references {
        Some(t) => seq![TokenView::Keyword(Keyword::References), TokenView::Ident(t)],
        None => Seq::empty(),
    }
}

pub open spec fn col_default_toks(c: SColumn) -> Seq<TokenView> {
    match c.default {
        Some(e) => seq![TokenView::Keyword(Keyword::Default)] + sprint(e),
        None => Seq::empty(),
    }
}

pub open spec fn sprint_column(c: SColumn) -> Seq<TokenView> {
    seq![TokenView::Ident(c.name), datatype_kw(c.datatype)]
        + col_pk_toks(c) + col_null_toks(c) + col_unique_toks(c) + col_index_toks(c)
        + col_ref_toks(c) + col_default_toks(c)
}

pub open spec fn sprint_columns(cols: Seq<SColumn>) -> Seq<TokenView>
    decreases cols,
{
    if cols.len() == 0 {
        Seq::empty()
    } else if cols.len() == 1 {
        sprint_column(cols[0])
    } else {
        sprint_column(cols[0]) + seq![TokenView::Comma] + sprint_columns(cols.drop_first())
    }
}

pub open spec fn sdepth_column(c: SColumn) -> nat {
    match c.default {
        Some(e) => 1 + sdepth(e),
        None => 1,
    }
}

pub open spec fn slist_depth_columns(cols: Seq<SColumn>) -> nat
    decreases cols,
{
    if cols.len() == 0 {
        1
    } else {
        let d = sdepth_column(cols[0]);
        let rest = slist_depth_columns(cols.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

// -- optional-clause parse helpers (each with a trivial roundtrip) -----------

/// Consume an optional single-keyword flag. Returns whether it was present and
/// the remaining tokens. Opaque: reasoned about only through `peel_flag`, so the
/// column roundtrip composes cheap per-clause facts instead of inlining the
/// whole optional chain into one solver query.
#[verifier::opaque]
pub open spec fn opt_flag(input: Seq<TokenView>, kw: Keyword) -> (bool, Seq<TokenView>) {
    if input.len() >= 1 && input[0] == TokenView::Keyword(kw) {
        (true, input.drop_first())
    } else {
        (false, input)
    }
}

#[verifier::opaque]
pub open spec fn col_parse_null(input: Seq<TokenView>) -> (Option<bool>, Seq<TokenView>) {
    if input.len() >= 2
        && input[0] == TokenView::Keyword(Keyword::Not)
        && input[1] == TokenView::Keyword(Keyword::Null) {
        (Some(false), input.drop_first().drop_first())
    } else if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Null) {
        (Some(true), input.drop_first())
    } else {
        (None, input)
    }
}

#[verifier::opaque]
pub open spec fn col_parse_pk(input: Seq<TokenView>) -> (bool, Seq<TokenView>) {
    if input.len() >= 2
        && input[0] == TokenView::Keyword(Keyword::Primary)
        && input[1] == TokenView::Keyword(Keyword::Key) {
        (true, input.drop_first().drop_first())
    } else {
        (false, input)
    }
}

#[verifier::opaque]
pub open spec fn col_parse_ref(input: Seq<TokenView>) -> (Option<String>, Seq<TokenView>) {
    if input.len() >= 2 && input[0] == TokenView::Keyword(Keyword::References) {
        match input[1] {
            TokenView::Ident(t) => (Some(t), input.drop_first().drop_first()),
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

/// Parse one column. `input[0]` should be the column-name identifier.
pub open spec fn sparse_column(input: Seq<TokenView>, fuel: nat) -> (Option<SColumn>, Seq<TokenView>) {
    if input.len() < 2 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => match parse_datatype_kw(input[1]) {
                Some(datatype) => {
                    let r0 = input.drop_first().drop_first();
                    let (primary_key, r1) = col_parse_pk(r0);
                    let (nullable, r2) = col_parse_null(r1);
                    let (unique, r3) = opt_flag(r2, Keyword::Unique);
                    let (index, r4) = opt_flag(r3, Keyword::Index);
                    let (references, r5) = col_parse_ref(r4);
                    if r5.len() >= 1 && r5[0] == TokenView::Keyword(Keyword::Default) {
                        match sparse(r5.drop_first(), fuel) {
                            (Some(e), r6) => (
                                Some(SColumn {
                                    name, datatype, primary_key, nullable,
                                    default: Some(e), unique, index, references,
                                }),
                                r6,
                            ),
                            (None, _) => (None, input),
                        }
                    } else {
                        (
                            Some(SColumn {
                                name, datatype, primary_key, nullable,
                                default: None, unique, index, references,
                            }),
                            r5,
                        )
                    }
                },
                None => (None, input),
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_columns(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<SColumn>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse_column(input, fuel) {
            (Some(c), rest) => {
                if rest.len() == 0 {
                    (None, input)
                } else if rest[0] == TokenView::CloseParen {
                    (Some(seq![c]), rest)
                } else if rest[0] == TokenView::Comma {
                    match sparse_columns(rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), rest2) => (Some(seq![c] + more), rest2),
                        (None, _) => (None, input),
                    }
                } else {
                    (None, input)
                }
            },
            (None, _) => (None, input),
        }
    }
}

/// Whether a mirror statement is a (nested) `Explain`, used to forbid the
/// degenerate `EXPLAIN EXPLAIN ...` which the printer would not disambiguate.
pub open spec fn is_sexplain(s: SStmt) -> bool {
    match s {
        SStmt::Explain(_) => true,
        _ => false,
    }
}

// ---- printer domain --------------------------------------------------------

/// Whether the canonical statement printer can encode this mirror statement.
pub open spec fn printable_stmt(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Begin { .. } => true,
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::DropTable { .. } => true,
        SStmt::CreateTable { columns, .. } => columns.len() >= 1 && all_printable_columns(columns),
        SStmt::Delete { where_clause: Some(e), .. } => printable_se(e),
        SStmt::Delete { where_clause: None, .. } => true,
        SStmt::Insert { columns, values, .. } =>
            values.len() >= 1 && all_printable_rows(values)
                && (match columns {
                    Some(names) => names.len() >= 1,
                    None => true,
                }),
        SStmt::Explain(inner) => !is_sexplain(*inner) && printable_stmt(*inner),
        SStmt::Unsupported => false,
    }
}

// ---- canonical statement printer over the mirror ---------------------------

pub open spec fn sprint_stmt(s: SStmt) -> Seq<TokenView>
    decreases s,
{
    match s {
        SStmt::Begin { read_only, as_of } => {
            let prefix = if read_only {
                seq![
                    TokenView::Keyword(Keyword::Begin),
                    TokenView::Keyword(Keyword::Read),
                    TokenView::Keyword(Keyword::Only),
                ]
            } else {
                seq![TokenView::Keyword(Keyword::Begin)]
            };
            prefix + match as_of {
                Some(version) => seq![
                    TokenView::Keyword(Keyword::As),
                    TokenView::Keyword(Keyword::Of),
                    TokenView::Keyword(Keyword::System),
                    TokenView::Keyword(Keyword::Time),
                    TokenView::Number(verified_integer::decimal_digits(version)),
                ],
                None => Seq::empty(),
            }
        },
        SStmt::Commit => seq![TokenView::Keyword(Keyword::Commit)],
        SStmt::Rollback => seq![TokenView::Keyword(Keyword::Rollback)],
        SStmt::CreateTable { name, columns } => seq![
            TokenView::Keyword(Keyword::Create),
            TokenView::Keyword(Keyword::Table),
            TokenView::Ident(name),
            TokenView::OpenParen,
        ] + sprint_columns(columns) + seq![TokenView::CloseParen],
        SStmt::DropTable { name, if_exists: false } => seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Ident(name),
        ],
        SStmt::DropTable { name, if_exists: true } => seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Keyword(Keyword::If),
            TokenView::Keyword(Keyword::Exists),
            TokenView::Ident(name),
        ],
        SStmt::Delete { table, where_clause: None } => seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
        ],
        SStmt::Delete { table, where_clause: Some(e) } => seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
            TokenView::Keyword(Keyword::Where),
        ] + sprint(e),
        SStmt::Insert { table, columns, values } => seq![
            TokenView::Keyword(Keyword::Insert),
            TokenView::Keyword(Keyword::Into),
            TokenView::Ident(table),
        ] + (match columns {
            Some(names) => seq![TokenView::OpenParen] + sprint_names(names) + seq![TokenView::CloseParen],
            None => Seq::empty(),
        }) + seq![TokenView::Keyword(Keyword::Values)] + sprint_rows(values),
        SStmt::Explain(inner) => seq![TokenView::Keyword(Keyword::Explain)] + sprint_stmt(*inner),
        SStmt::Unsupported => Seq::empty(),
    }
}

// ---- fuel measure ----------------------------------------------------------

pub open spec fn sdepth_stmt(s: SStmt) -> nat
    decreases s,
{
    match s {
        SStmt::CreateTable { columns, .. } => 1 + slist_depth_columns(columns),
        SStmt::Delete { where_clause: Some(e), .. } => 1 + sdepth(e),
        SStmt::Insert { columns, values, .. } => insert_fuel(columns, values),
        SStmt::Explain(inner) => 1 + sdepth_stmt(*inner),
        _ => 1,
    }
}

// ---- mirror parser ---------------------------------------------------------

/// `BEGIN` forms. `input[0]` is known to be `BEGIN`.
pub open spec fn sparse_begin(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    let (read_only, after) = if input.len() >= 3
        && input[1] == TokenView::Keyword(Keyword::Read)
        && input[2] == TokenView::Keyword(Keyword::Only) {
        (true, input.drop_first().drop_first().drop_first())
    } else {
        (false, input.drop_first())
    };
    if after.len() >= 5
        && after[0] == TokenView::Keyword(Keyword::As)
        && after[1] == TokenView::Keyword(Keyword::Of)
        && after[2] == TokenView::Keyword(Keyword::System)
        && after[3] == TokenView::Keyword(Keyword::Time) {
        match after[4] {
            TokenView::Number(bytes) => match verified_integer::parse_digits_spec(bytes) {
                Some(version) => (
                    Some(SStmt::Begin { read_only, as_of: Some(version) }),
                    after.drop_first().drop_first().drop_first().drop_first().drop_first(),
                ),
                None => (Some(SStmt::Begin { read_only, as_of: None }), after),
            },
            _ => (Some(SStmt::Begin { read_only, as_of: None }), after),
        }
    } else {
        (Some(SStmt::Begin { read_only, as_of: None }), after)
    }
}

/// `DROP TABLE` forms. `input[0]` is known to be `DROP`.
pub open spec fn sparse_drop(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() >= 4
        && input[1] == TokenView::Keyword(Keyword::Table)
        && input[2] == TokenView::Keyword(Keyword::If)
        && input[3] == TokenView::Keyword(Keyword::Exists) {
        if input.len() >= 5 {
            match input[4] {
                TokenView::Ident(name) => (
                    Some(SStmt::DropTable { name, if_exists: true }),
                    input.drop_first().drop_first().drop_first().drop_first().drop_first(),
                ),
                _ => (None, input),
            }
        } else {
            (None, input)
        }
    } else if input.len() >= 3 && input[1] == TokenView::Keyword(Keyword::Table) {
        match input[2] {
            TokenView::Ident(name) => (
                Some(SStmt::DropTable { name, if_exists: false }),
                input.drop_first().drop_first().drop_first(),
            ),
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

/// `DELETE FROM` forms. `input[0]` is known to be `DELETE`.
pub open spec fn sparse_delete(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 3 || input[1] != TokenView::Keyword(Keyword::From) {
        (None, input)
    } else {
        match input[2] {
            TokenView::Ident(table) => {
                if input.len() >= 4 && input[3] == TokenView::Keyword(Keyword::Where) {
                    match sparse(input.drop_first().drop_first().drop_first().drop_first(), fuel) {
                        (Some(e), rest) => (
                            Some(SStmt::Delete { table, where_clause: Some(e) }),
                            rest,
                        ),
                        (None, _) => (None, input),
                    }
                } else {
                    (
                        Some(SStmt::Delete { table, where_clause: None }),
                        input.drop_first().drop_first().drop_first(),
                    )
                }
            },
            _ => (None, input),
        }
    }
}

/// `CREATE TABLE name ( columns )`. `input[0]` is known to be `CREATE`.
pub open spec fn sparse_create(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() >= 4
        && input[1] == TokenView::Keyword(Keyword::Table)
        && input[3] == TokenView::OpenParen {
        match input[2] {
            TokenView::Ident(name) => match sparse_columns(
                input.drop_first().drop_first().drop_first().drop_first(),
                fuel,
            ) {
                (Some(cols), rest) if rest.len() > 0 && rest[0] == TokenView::CloseParen => (
                    Some(SStmt::CreateTable { name, columns: cols }),
                    rest.drop_first(),
                ),
                _ => (None, input),
            },
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

pub open spec fn sparse_stmt(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Keyword(Keyword::Commit) => (Some(SStmt::Commit), input.drop_first()),
            TokenView::Keyword(Keyword::Rollback) => (Some(SStmt::Rollback), input.drop_first()),
            TokenView::Keyword(Keyword::Begin) => sparse_begin(input),
            TokenView::Keyword(Keyword::Create) => sparse_create(input, fuel),
            TokenView::Keyword(Keyword::Drop) => sparse_drop(input),
            TokenView::Keyword(Keyword::Delete) => sparse_delete(input, fuel),
            TokenView::Keyword(Keyword::Insert) => sparse_insert(input, fuel),
            TokenView::Keyword(Keyword::Explain) => {
                match sparse_stmt(input.drop_first(), (fuel - 1) as nat) {
                    (Some(inner), rest) if !is_sexplain(inner) => (
                        Some(SStmt::Explain(Box::new(inner))),
                        rest,
                    ),
                    _ => (None, input),
                }
            },
            _ => (None, input),
        }
    }
}

// ---- headline: the mirror statement roundtrip ------------------------------

/// Parsing the canonical print of any printable mirror statement recovers it
/// exactly and consumes all of it.
#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_stmt_sprint(s: SStmt, fuel: nat)
    requires
        printable_stmt(s),
        fuel >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel) == (Some(s), Seq::<TokenView>::empty()),
    decreases s,
{
    reveal(printable_stmt);
    reveal_with_fuel(sparse_stmt, 1);
    let tokens = sprint_stmt(s);
    match s {
        SStmt::Commit => {
            assert(tokens[0] == TokenView::Keyword(Keyword::Commit));
            assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Rollback => {
            assert(tokens[0] == TokenView::Keyword(Keyword::Rollback));
            assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Begin { read_only, as_of } => {
            let (r_prefix, after0) = if read_only {
                (
                    seq![
                        TokenView::Keyword(Keyword::Begin),
                        TokenView::Keyword(Keyword::Read),
                        TokenView::Keyword(Keyword::Only),
                    ],
                    3int,
                )
            } else {
                (seq![TokenView::Keyword(Keyword::Begin)], 1int)
            };
            assert(tokens[0] == TokenView::Keyword(Keyword::Begin));
            // sparse_begin recomputes the read_only prefix positionally.
            match as_of {
                None => {
                    if read_only {
                        assert(tokens =~= r_prefix);
                        assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
                    } else {
                        assert(tokens =~= r_prefix);
                        assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
                    }
                },
                Some(version) => {
                    verified_integer::print_parse_u64_roundtrip(version);
                    let as_of_toks = seq![
                        TokenView::Keyword(Keyword::As),
                        TokenView::Keyword(Keyword::Of),
                        TokenView::Keyword(Keyword::System),
                        TokenView::Keyword(Keyword::Time),
                        TokenView::Number(verified_integer::decimal_digits(version)),
                    ];
                    if read_only {
                        assert(tokens =~= r_prefix + as_of_toks);
                        assert(tokens[1] == TokenView::Keyword(Keyword::Read));
                        assert(tokens[2] == TokenView::Keyword(Keyword::Only));
                        assert(tokens.drop_first().drop_first().drop_first() =~= as_of_toks);
                        assert(as_of_toks.drop_first().drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<TokenView>::empty());
                    } else {
                        assert(tokens =~= r_prefix + as_of_toks);
                        assert(tokens[1] == TokenView::Keyword(Keyword::As));
                        assert(tokens.drop_first() =~= as_of_toks);
                        assert(as_of_toks.drop_first().drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<TokenView>::empty());
                    }
                },
            }
        },
        SStmt::CreateTable { name, columns } => {
            let inner_tail = seq![TokenView::CloseParen];
            lemma_sparse_columns_sprint(columns, inner_tail, fuel);
            let head = seq![
                TokenView::Keyword(Keyword::Create),
                TokenView::Keyword(Keyword::Table),
                TokenView::Ident(name),
                TokenView::OpenParen,
            ];
            assert(tokens =~= head + sprint_columns(columns) + inner_tail);
            assert(tokens[0] == TokenView::Keyword(Keyword::Create));
            assert(tokens[1] == TokenView::Keyword(Keyword::Table));
            assert(tokens[2] == TokenView::Ident(name));
            assert(tokens[3] == TokenView::OpenParen);
            assert(tokens.drop_first().drop_first().drop_first().drop_first()
                =~= sprint_columns(columns) + inner_tail);
            assert(inner_tail[0] == TokenView::CloseParen);
            assert(inner_tail.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::DropTable { name, if_exists } => {
            if if_exists {
                assert(tokens[0] == TokenView::Keyword(Keyword::Drop));
                assert(tokens[1] == TokenView::Keyword(Keyword::Table));
                assert(tokens[2] == TokenView::Keyword(Keyword::If));
                assert(tokens[3] == TokenView::Keyword(Keyword::Exists));
                assert(tokens[4] == TokenView::Ident(name));
                assert(tokens.drop_first().drop_first().drop_first().drop_first().drop_first()
                    =~= Seq::<TokenView>::empty());
            } else {
                assert(tokens[0] == TokenView::Keyword(Keyword::Drop));
                assert(tokens[1] == TokenView::Keyword(Keyword::Table));
                assert(tokens[2] == TokenView::Ident(name));
                assert(tokens[2] != TokenView::Keyword(Keyword::If));
                assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
            }
        },
        SStmt::Delete { table, where_clause } => {
            match where_clause {
                None => {
                    assert(tokens[0] == TokenView::Keyword(Keyword::Delete));
                    assert(tokens[1] == TokenView::Keyword(Keyword::From));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens.len() == 3);
                    assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
                },
                Some(e) => {
                    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel);
                    let head = seq![
                        TokenView::Keyword(Keyword::Delete),
                        TokenView::Keyword(Keyword::From),
                        TokenView::Ident(table),
                        TokenView::Keyword(Keyword::Where),
                    ];
                    assert(tokens =~= head + sprint(e));
                    assert(tokens[0] == TokenView::Keyword(Keyword::Delete));
                    assert(tokens[1] == TokenView::Keyword(Keyword::From));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens[3] == TokenView::Keyword(Keyword::Where));
                    assert(tokens.drop_first().drop_first().drop_first().drop_first() =~= sprint(e));
                    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
                },
            }
        },
        SStmt::Insert { table, columns, values } => {
            lemma_sparse_rows_sprint(values, fuel);
            let head = seq![
                TokenView::Keyword(Keyword::Insert),
                TokenView::Keyword(Keyword::Into),
                TokenView::Ident(table),
            ];
            match columns {
                None => {
                    let after_head = seq![TokenView::Keyword(Keyword::Values)] + sprint_rows(values);
                    assert(tokens =~= head + after_head);
                    assert(tokens[0] == TokenView::Keyword(Keyword::Insert));
                    assert(tokens[1] == TokenView::Keyword(Keyword::Into));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens.drop_first().drop_first().drop_first() =~= after_head);
                    assert(after_head[0] == TokenView::Keyword(Keyword::Values));
                    assert(after_head[0] != TokenView::OpenParen);
                    assert(after_head.drop_first() =~= sprint_rows(values));
                },
                Some(names) => {
                    let names_tail = seq![
                        TokenView::CloseParen,
                        TokenView::Keyword(Keyword::Values),
                    ] + sprint_rows(values);
                    lemma_sparse_names_sprint(names, names_tail, fuel);
                    let after_head = seq![TokenView::OpenParen] + sprint_names(names) + names_tail;
                    assert(tokens =~= head + after_head);
                    assert(tokens[0] == TokenView::Keyword(Keyword::Insert));
                    assert(tokens[1] == TokenView::Keyword(Keyword::Into));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens.drop_first().drop_first().drop_first() =~= after_head);
                    assert(after_head[0] == TokenView::OpenParen);
                    assert(after_head.drop_first() =~= sprint_names(names) + names_tail);
                    assert(names_tail[0] == TokenView::CloseParen);
                    assert(names_tail.drop_first() =~= seq![TokenView::Keyword(Keyword::Values)] + sprint_rows(values));
                    assert(names_tail.drop_first().drop_first() =~= sprint_rows(values));
                },
            }
        },
        SStmt::Explain(inner) => {
            lemma_sparse_stmt_sprint(*inner, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::Keyword(Keyword::Explain));
            assert(tokens.drop_first() =~= sprint_stmt(*inner));
        },
        SStmt::Unsupported => {
            assert(false);
        },
    }
}

// ---- column roundtrip (S2) -------------------------------------------------

pub proof fn datatype_kw_roundtrip(d: DataType)
    ensures parse_datatype_kw(datatype_kw(d)) == Some(d),
{
    match d {
        DataType::Boolean => {},
        DataType::Integer => {},
        DataType::Float => {},
        DataType::String => {},
    }
}

// -- per-clause peel lemmas (each a cheap, isolated fact) --------------------

pub proof fn peel_unique(c: SColumn, rest: Seq<TokenView>)
    requires rest.len() == 0 || rest[0] != TokenView::Keyword(Keyword::Unique),
    ensures opt_flag(col_unique_toks(c) + rest, Keyword::Unique) == (c.unique, rest),
{
    reveal(opt_flag);
    let toks = col_unique_toks(c) + rest;
    if c.unique {
        assert(toks[0] == TokenView::Keyword(Keyword::Unique));
        assert(toks.drop_first() =~= rest);
    } else {
        assert(toks =~= rest);
    }
}

pub proof fn peel_index(c: SColumn, rest: Seq<TokenView>)
    requires rest.len() == 0 || rest[0] != TokenView::Keyword(Keyword::Index),
    ensures opt_flag(col_index_toks(c) + rest, Keyword::Index) == (c.index, rest),
{
    reveal(opt_flag);
    let toks = col_index_toks(c) + rest;
    if c.index {
        assert(toks[0] == TokenView::Keyword(Keyword::Index));
        assert(toks.drop_first() =~= rest);
    } else {
        assert(toks =~= rest);
    }
}

pub proof fn peel_pk(c: SColumn, rest: Seq<TokenView>)
    requires rest.len() == 0 || rest[0] != TokenView::Keyword(Keyword::Primary),
    ensures col_parse_pk(col_pk_toks(c) + rest) == (c.primary_key, rest),
{
    reveal(col_parse_pk);
    let toks = col_pk_toks(c) + rest;
    if c.primary_key {
        assert(toks[0] == TokenView::Keyword(Keyword::Primary));
        assert(toks[1] == TokenView::Keyword(Keyword::Key));
        assert(toks.drop_first().drop_first() =~= rest);
    } else {
        assert(toks =~= rest);
    }
}

pub proof fn peel_null(c: SColumn, rest: Seq<TokenView>)
    requires
        rest.len() == 0
            || (rest[0] != TokenView::Keyword(Keyword::Not)
                && rest[0] != TokenView::Keyword(Keyword::Null)),
    ensures col_parse_null(col_null_toks(c) + rest) == (c.nullable, rest),
{
    reveal(col_parse_null);
    let toks = col_null_toks(c) + rest;
    match c.nullable {
        Some(true) => {
            assert(toks[0] == TokenView::Keyword(Keyword::Null));
            assert(toks[0] != TokenView::Keyword(Keyword::Not));
            assert(toks.drop_first() =~= rest);
        },
        Some(false) => {
            assert(toks[0] == TokenView::Keyword(Keyword::Not));
            assert(toks[1] == TokenView::Keyword(Keyword::Null));
            assert(toks.drop_first().drop_first() =~= rest);
        },
        None => {
            assert(toks =~= rest);
        },
    }
}

pub proof fn peel_ref(c: SColumn, rest: Seq<TokenView>)
    requires rest.len() == 0 || rest[0] != TokenView::Keyword(Keyword::References),
    ensures col_parse_ref(col_ref_toks(c) + rest) == (c.references, rest),
{
    reveal(col_parse_ref);
    let toks = col_ref_toks(c) + rest;
    match c.references {
        Some(t) => {
            assert(toks[0] == TokenView::Keyword(Keyword::References));
            assert(toks[1] == TokenView::Ident(t));
            assert(toks.drop_first().drop_first() =~= rest);
        },
        None => {
            assert(toks =~= rest);
        },
    }
}

/// Parsing the canonical print of one printable column, followed by a
/// column-terminator tail (comma or close-paren), recovers the column exactly.
#[verifier::rlimit(8000)]
pub proof fn lemma_sparse_column_sprint(c: SColumn, tail: Seq<TokenView>, fuel: nat)
    requires
        printable_column(c),
        fuel >= sdepth_column(c),
        tail.len() > 0,
        tail[0] == TokenView::Comma || tail[0] == TokenView::CloseParen,
    ensures
        sparse_column(sprint_column(c) + tail, fuel) == (Some(c), tail),
{
    datatype_kw_roundtrip(c.datatype);
    let pk = col_pk_toks(c);
    let nul = col_null_toks(c);
    let uniq = col_unique_toks(c);
    let idx = col_index_toks(c);
    let rf = col_ref_toks(c);
    let df = col_default_toks(c);
    // Suffixes, bottom-up.
    let sd = df + tail;
    let sr = rf + sd;
    let sx = idx + sr;
    let su = uniq + sx;
    let sn = nul + su;
    let s0 = pk + sn;
    // Full printed column + tail decomposes at the (name, datatype) prefix.
    let full = sprint_column(c) + tail;
    assert(full =~= seq![TokenView::Ident(c.name), datatype_kw(c.datatype)] + s0);
    assert(full[0] == TokenView::Ident(c.name));
    assert(full[1] == datatype_kw(c.datatype));
    assert(full.drop_first().drop_first() =~= s0);

    // Head facts for each suffix (used to reject absent clauses).
    // sd: head is DEFAULT (present) or tail[0] (absent); len >= 1.
    assert(sd.len() >= 1 && sd[0] != TokenView::Keyword(Keyword::References)) by {
        match c.default {
            Some(e) => { assert(sd =~= seq![TokenView::Keyword(Keyword::Default)] + sprint(e) + tail); },
            None => { assert(sd =~= tail); },
        }
    }
    // sr: head is REFERENCES (present) else head(sd).
    assert(sr.len() >= 1
        && sr[0] != TokenView::Keyword(Keyword::Index)
        && sr[0] != TokenView::Keyword(Keyword::Unique)) by {
        match c.references {
            Some(t) => { assert(sr =~= seq![TokenView::Keyword(Keyword::References), TokenView::Ident(t)] + sd); },
            None => { assert(sr =~= sd); },
        }
    }
    // sx: head is INDEX (present) else head(sr).
    assert(sx.len() >= 1 && sx[0] != TokenView::Keyword(Keyword::Unique)) by {
        if c.index {
            assert(sx =~= seq![TokenView::Keyword(Keyword::Index)] + sr);
        } else {
            assert(sx =~= sr);
        }
    }
    // su: head is UNIQUE (present) else head(sx); never NOT or NULL.
    assert(su.len() >= 1
        && su[0] != TokenView::Keyword(Keyword::Not)
        && su[0] != TokenView::Keyword(Keyword::Null)) by {
        if c.unique {
            assert(su =~= seq![TokenView::Keyword(Keyword::Unique)] + sx);
        } else {
            assert(su =~= sx);
        }
    }
    // sn: head via nullability, else head(su); never PRIMARY.
    assert(sn.len() >= 1 && sn[0] != TokenView::Keyword(Keyword::Primary)) by {
        match c.nullable {
            Some(true) => { assert(sn =~= seq![TokenView::Keyword(Keyword::Null)] + su); },
            Some(false) => { assert(sn =~= seq![TokenView::Keyword(Keyword::Not), TokenView::Keyword(Keyword::Null)] + su); },
            None => { assert(sn =~= su); },
        }
    }

    // Peel each optional clause off `s0`, using the head facts to reject the
    // absent ones. Each peel is a cheap, isolated fact about an opaque helper;
    // `sparse_column` then composes them without inlining the whole chain.
    peel_pk(c, sn);
    peel_null(c, su);
    peel_unique(c, sx);
    peel_index(c, sr);
    peel_ref(c, sd);
    // Restate each peel at exactly the argument `sparse_column` uses internally
    // (r0 == s0, then r1 == sn, ...), so the chain resolves in the postcondition.
    assert(col_parse_pk(s0) == (c.primary_key, sn));
    assert(col_parse_null(sn) == (c.nullable, su));
    assert(opt_flag(su, Keyword::Unique) == (c.unique, sx));
    assert(opt_flag(sx, Keyword::Index) == (c.index, sr));
    assert(col_parse_ref(sr) == (c.references, sd));
    // Default (last): its embedded expression's tail is exactly the column
    // terminator, so its boundary is trivially satisfied.
    match c.default {
        Some(e) => {
            assert(printable_se(e));
            assert(fuel >= sdepth(e));
            assert(sd =~= seq![TokenView::Keyword(Keyword::Default)] + sprint(e) + tail);
            assert(sd[0] == TokenView::Keyword(Keyword::Default));
            assert(sd.drop_first() =~= sprint(e) + tail);
            lemma_sparse_sprint(e, tail, fuel);
            assert(sparse(sd.drop_first(), fuel) == (Some(e), tail));
        },
        None => {
            assert(sd =~= tail);
            assert(sd.len() >= 1);
            assert(sd[0] != TokenView::Keyword(Keyword::Default));
        },
    }
    assert(sparse_column(full, fuel) == (Some(c), tail));
}

/// Comma-list companion: parsing the canonical print of a printable column
/// sequence, closed by a `)`-led tail, recovers the sequence exactly.
pub proof fn lemma_sparse_columns_sprint(cols: Seq<SColumn>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_columns(cols),
        cols.len() >= 1,
        fuel >= slist_depth_columns(cols),
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
    ensures
        sparse_columns(sprint_columns(cols) + tail, fuel) == (Some(cols), tail),
    decreases cols,
{
    reveal_with_fuel(sparse_columns, 1);
    if cols.len() == 1 {
        lemma_sparse_column_sprint(cols[0], tail, fuel);
        assert(sprint_columns(cols) + tail =~= sprint_column(cols[0]) + tail);
        assert(seq![cols[0]] =~= cols);
    } else {
        let rest_cols = cols.drop_first();
        let col_tail = seq![TokenView::Comma] + sprint_columns(rest_cols) + tail;
        assert(col_tail[0] == TokenView::Comma);
        lemma_sparse_column_sprint(cols[0], col_tail, fuel);
        lemma_sparse_columns_sprint(rest_cols, tail, (fuel - 1) as nat);
        assert(sprint_columns(cols) + tail =~= sprint_column(cols[0]) + col_tail);
        assert(col_tail.drop_first() =~= sprint_columns(rest_cols) + tail);
        assert(seq![cols[0]] + rest_cols =~= cols);
    }
}

// ---- Insert codec (S3): name list + nested rows list -----------------------

pub open spec fn sprint_names(names: Seq<String>) -> Seq<TokenView>
    decreases names,
{
    if names.len() == 0 {
        Seq::empty()
    } else if names.len() == 1 {
        seq![TokenView::Ident(names[0])]
    } else {
        seq![TokenView::Ident(names[0]), TokenView::Comma] + sprint_names(names.drop_first())
    }
}

pub open spec fn names_fuel(names: Seq<String>) -> nat {
    (names.len() + 1) as nat
}

pub open spec fn sparse_names(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<String>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                let rest = input.drop_first();
                if rest.len() == 0 {
                    (None, input)
                } else if rest[0] == TokenView::CloseParen {
                    (Some(seq![name]), rest)
                } else if rest[0] == TokenView::Comma {
                    match sparse_names(rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), r2) => (Some(seq![name] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (None, input)
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sprint_row(row: Seq<SExpr>) -> Seq<TokenView> {
    seq![TokenView::OpenParen] + sprint_args(row) + seq![TokenView::CloseParen]
}

pub open spec fn sprint_rows(rows: Seq<Seq<SExpr>>) -> Seq<TokenView>
    decreases rows,
{
    if rows.len() == 0 {
        Seq::empty()
    } else if rows.len() == 1 {
        sprint_row(rows[0])
    } else {
        sprint_row(rows[0]) + seq![TokenView::Comma] + sprint_rows(rows.drop_first())
    }
}

pub open spec fn slist_depth_rows(rows: Seq<Seq<SExpr>>) -> nat
    decreases rows,
{
    if rows.len() == 0 {
        1
    } else {
        let d = slist_depth(rows[0]);
        let rest = slist_depth_rows(rows.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

pub open spec fn all_printable_rows(rows: Seq<Seq<SExpr>>) -> bool
    decreases rows,
{
    if rows.len() == 0 {
        true
    } else {
        all_printable_se(rows[0]) && all_printable_rows(rows.drop_first())
    }
}

pub open spec fn sparse_rows(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<Seq<SExpr>>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 || input[0] != TokenView::OpenParen {
        (None, input)
    } else {
        match sparse_args(input.drop_first(), fuel) {
            (Some(row), r) => {
                if r.len() > 0 && r[0] == TokenView::CloseParen {
                    let r2 = r.drop_first();
                    if r2.len() > 0 && r2[0] == TokenView::Comma {
                        match sparse_rows(r2.drop_first(), (fuel - 1) as nat) {
                            (Some(more), r3) => (Some(seq![row] + more), r3),
                            (None, _) => (None, input),
                        }
                    } else {
                        (Some(seq![row]), r2)
                    }
                } else {
                    (None, input)
                }
            },
            (None, _) => (None, input),
        }
    }
}

pub open spec fn insert_fuel(columns: Option<Seq<String>>, values: Seq<Seq<SExpr>>) -> nat {
    (1 + (match columns {
        Some(names) => names_fuel(names),
        None => 0nat,
    }) + slist_depth_rows(values)) as nat
}

pub proof fn lemma_sparse_names_sprint(names: Seq<String>, tail: Seq<TokenView>, fuel: nat)
    requires
        names.len() >= 1,
        fuel >= names_fuel(names),
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
    ensures
        sparse_names(sprint_names(names) + tail, fuel) == (Some(names), tail),
    decreases names,
{
    reveal_with_fuel(sparse_names, 2);
    if names.len() == 1 {
        let input = sprint_names(names) + tail;
        assert(input =~= seq![TokenView::Ident(names[0])] + tail);
        assert(input[0] == TokenView::Ident(names[0]));
        assert(input.drop_first() =~= tail);
        assert(input.drop_first()[0] == TokenView::CloseParen);
        assert(sparse_names(input, fuel) == (Some(seq![names[0]]), tail));
        assert(seq![names[0]] =~= names);
    } else {
        let input = sprint_names(names) + tail;
        let rest_names = names.drop_first();
        let comma_tail = seq![TokenView::Comma] + sprint_names(rest_names) + tail;
        lemma_sparse_names_sprint(rest_names, tail, (fuel - 1) as nat);
        assert(input =~= seq![TokenView::Ident(names[0])] + comma_tail);
        assert(input[0] == TokenView::Ident(names[0]));
        assert(input.drop_first() =~= comma_tail);
        assert(comma_tail[0] == TokenView::Comma);
        assert(comma_tail.drop_first() =~= sprint_names(rest_names) + tail);
        assert(sparse_names(input, fuel) == (Some(seq![names[0]] + rest_names), tail));
        assert(seq![names[0]] + rest_names =~= names);
    }
}

/// Two-level list roundtrip: a comma list of parenthesised expression rows.
#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_rows_sprint(rows: Seq<Seq<SExpr>>, fuel: nat)
    requires
        all_printable_rows(rows),
        rows.len() >= 1,
        fuel >= slist_depth_rows(rows),
    ensures
        sparse_rows(sprint_rows(rows), fuel) == (Some(rows), Seq::<TokenView>::empty()),
    decreases rows,
{
    reveal_with_fuel(sparse_rows, 1);
    if rows.len() == 1 {
        lemma_sparse_args_sprint(rows[0], seq![TokenView::CloseParen], fuel);
        assert(sprint_rows(rows) =~= seq![TokenView::OpenParen]
            + (sprint_args(rows[0]) + seq![TokenView::CloseParen]));
        assert(sprint_rows(rows).drop_first() =~= sprint_args(rows[0]) + seq![TokenView::CloseParen]);
        assert(seq![rows[0]] =~= rows);
    } else {
        let rest = rows.drop_first();
        let args_tail = seq![TokenView::CloseParen, TokenView::Comma] + sprint_rows(rest);
        lemma_sparse_args_sprint(rows[0], args_tail, fuel);
        lemma_sparse_rows_sprint(rest, (fuel - 1) as nat);
        assert(sprint_rows(rows) =~= seq![TokenView::OpenParen] + (sprint_args(rows[0]) + args_tail));
        assert(sprint_rows(rows).drop_first() =~= sprint_args(rows[0]) + args_tail);
        assert(args_tail[0] == TokenView::CloseParen);
        assert(args_tail.drop_first() =~= seq![TokenView::Comma] + sprint_rows(rest));
        assert(args_tail.drop_first().drop_first() =~= sprint_rows(rest));
        assert(seq![rows[0]] + rest =~= rows);
    }
}

/// `INSERT INTO table [(names)] VALUES rows`. `input[0]` is known to be `INSERT`.
pub open spec fn sparse_insert(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() >= 3 && input[1] == TokenView::Keyword(Keyword::Into) {
        match input[2] {
            TokenView::Ident(table) => {
                let rest = input.drop_first().drop_first().drop_first();
                if rest.len() >= 1 && rest[0] == TokenView::OpenParen {
                    match sparse_names(rest.drop_first(), fuel) {
                        (Some(names), r) => {
                            if r.len() > 0 && r[0] == TokenView::CloseParen {
                                let r2 = r.drop_first();
                                if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::Values) {
                                    match sparse_rows(r2.drop_first(), fuel) {
                                        (Some(rows), r3) => (
                                            Some(SStmt::Insert { table, columns: Some(names), values: rows }),
                                            r3,
                                        ),
                                        (None, _) => (None, input),
                                    }
                                } else {
                                    (None, input)
                                }
                            } else {
                                (None, input)
                            }
                        },
                        (None, _) => (None, input),
                    }
                } else if rest.len() >= 1 && rest[0] == TokenView::Keyword(Keyword::Values) {
                    match sparse_rows(rest.drop_first(), fuel) {
                        (Some(rows), r3) => (
                            Some(SStmt::Insert { table, columns: None, values: rows }),
                            r3,
                        ),
                        (None, _) => (None, input),
                    }
                } else {
                    (None, input)
                }
            },
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

// ---- FROM join tree (S3) ---------------------------------------------------
//
// A `From` item is a left-deep join tree whose right child is always a table.
// The printer emits it left-to-right; the parser reads the leftmost table then
// a forward list of join steps and folds them left-deep, so no left-recursion
// is needed. `fold_joins`/`from_head`/`from_steps` decompose the tree into
// (head table, step list) and the identities below reassemble it.

pub struct SJoinStep {
    pub join_type: ast::JoinType,
    pub right: SFrom,
    pub predicate: Option<SExpr>,
}

pub enum SFrom {
    Table { name: String, alias: Option<String> },
    Join { left: Box<SFrom>, right: Box<SFrom>, join_type: ast::JoinType, predicate: Option<SExpr> },
}

pub open spec fn view_from(f: ast::From) -> SFrom
    decreases f,
{
    match f {
        ast::From::Table { name, alias } => SFrom::Table { name, alias },
        ast::From::Join { left, right, join_type, predicate } => SFrom::Join {
            left: Box::new(view_from(*left)),
            right: Box::new(view_from(*right)),
            join_type,
            predicate: match predicate {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
    }
}

pub open spec fn is_stable(f: SFrom) -> bool {
    match f {
        SFrom::Table { .. } => true,
        _ => false,
    }
}

pub open spec fn printable_from(f: SFrom) -> bool
    decreases f,
{
    match f {
        SFrom::Table { .. } => true,
        SFrom::Join { left, right, join_type, predicate } =>
            is_stable(*right)
            && (match join_type {
                ast::JoinType::Cross => predicate is None,
                _ => predicate is Some && printable_se(predicate->Some_0),
            })
            && printable_from(*left),
    }
}

// -- tree <-> (head table, step list) decomposition --------------------------

pub open spec fn from_head(f: SFrom) -> SFrom
    decreases f,
{
    match f {
        SFrom::Table { .. } => f,
        SFrom::Join { left, .. } => from_head(*left),
    }
}

pub open spec fn from_steps(f: SFrom) -> Seq<SJoinStep>
    decreases f,
{
    match f {
        SFrom::Table { .. } => Seq::empty(),
        SFrom::Join { left, right, join_type, predicate } =>
            from_steps(*left) + seq![SJoinStep { join_type, right: *right, predicate }],
    }
}

pub open spec fn apply_step(acc: SFrom, step: SJoinStep) -> SFrom {
    SFrom::Join {
        left: Box::new(acc),
        right: Box::new(step.right),
        join_type: step.join_type,
        predicate: step.predicate,
    }
}

pub open spec fn fold_joins(head: SFrom, steps: Seq<SJoinStep>) -> SFrom
    decreases steps,
{
    if steps.len() == 0 {
        head
    } else {
        fold_joins(apply_step(head, steps[0]), steps.drop_first())
    }
}

pub proof fn fold_append(h: SFrom, xs: Seq<SJoinStep>, ys: Seq<SJoinStep>)
    ensures fold_joins(h, xs + ys) == fold_joins(fold_joins(h, xs), ys),
    decreases xs,
{
    if xs.len() == 0 {
        assert(xs + ys =~= ys);
    } else {
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys);
        fold_append(apply_step(h, xs[0]), xs.drop_first(), ys);
    }
}

pub proof fn fold_decomp(f: SFrom)
    ensures fold_joins(from_head(f), from_steps(f)) == f,
    decreases f,
{
    match f {
        SFrom::Table { .. } => {},
        SFrom::Join { left, right, join_type, predicate } => {
            fold_decomp(*left);
            let step = SJoinStep { join_type, right: *right, predicate };
            fold_append(from_head(*left), from_steps(*left), seq![step]);
            assert(from_steps(f) =~= from_steps(*left) + seq![step]);
            reveal_with_fuel(fold_joins, 2);
            assert(seq![step][0] == step);
            assert(seq![step].drop_first() =~= Seq::<SJoinStep>::empty());
            assert(fold_joins(*left, seq![step]) == apply_step(*left, step));
            assert(apply_step(*left, step) == f);
        },
    }
}

// -- printer -----------------------------------------------------------------

pub open spec fn sprint_table(f: SFrom) -> Seq<TokenView> {
    match f {
        SFrom::Table { name, alias: None } => seq![TokenView::Ident(name)],
        SFrom::Table { name, alias: Some(a) } =>
            seq![TokenView::Ident(name), TokenView::Keyword(Keyword::As), TokenView::Ident(a)],
        _ => Seq::empty(),
    }
}

pub open spec fn join_kws(jt: ast::JoinType) -> Seq<TokenView> {
    match jt {
        ast::JoinType::Cross => seq![TokenView::Keyword(Keyword::Cross), TokenView::Keyword(Keyword::Join)],
        ast::JoinType::Inner => seq![TokenView::Keyword(Keyword::Inner), TokenView::Keyword(Keyword::Join)],
        ast::JoinType::Left => seq![TokenView::Keyword(Keyword::Left), TokenView::Keyword(Keyword::Join)],
        ast::JoinType::Right => seq![TokenView::Keyword(Keyword::Right), TokenView::Keyword(Keyword::Join)],
    }
}

pub open spec fn is_cross(jt: ast::JoinType) -> bool {
    match jt {
        ast::JoinType::Cross => true,
        _ => false,
    }
}

pub open spec fn step_toks(step: SJoinStep) -> Seq<TokenView> {
    join_kws(step.join_type) + sprint_table(step.right)
        + (match step.predicate {
            Some(e) => seq![TokenView::Keyword(Keyword::On)] + sprint(e),
            None => Seq::empty(),
        })
}

pub open spec fn sprint_steps(steps: Seq<SJoinStep>) -> Seq<TokenView>
    decreases steps,
{
    if steps.len() == 0 {
        Seq::empty()
    } else {
        step_toks(steps[0]) + sprint_steps(steps.drop_first())
    }
}

pub open spec fn sprint_from(f: SFrom) -> Seq<TokenView>
    decreases f,
{
    match f {
        SFrom::Table { .. } => sprint_table(f),
        SFrom::Join { left, right, join_type, predicate } =>
            sprint_from(*left)
                + join_kws(join_type) + sprint_table(*right)
                + (match predicate {
                    Some(e) => seq![TokenView::Keyword(Keyword::On)] + sprint(e),
                    None => Seq::empty(),
                }),
    }
}

pub proof fn sprint_steps_append(xs: Seq<SJoinStep>, ys: Seq<SJoinStep>)
    ensures sprint_steps(xs + ys) == sprint_steps(xs) + sprint_steps(ys),
    decreases xs,
{
    if xs.len() == 0 {
        assert(xs + ys =~= ys);
    } else {
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys);
        sprint_steps_append(xs.drop_first(), ys);
    }
}

/// `sprint_from(f) == sprint_table(from_head(f)) + sprint_steps(from_steps(f))`.
pub proof fn sprint_decomp(f: SFrom)
    ensures sprint_from(f) == sprint_table(from_head(f)) + sprint_steps(from_steps(f)),
    decreases f,
{
    match f {
        SFrom::Table { .. } => {
            assert(sprint_steps(from_steps(f)) =~= Seq::<TokenView>::empty());
        },
        SFrom::Join { left, right, join_type, predicate } => {
            sprint_decomp(*left);
            let step = SJoinStep { join_type, right: *right, predicate };
            sprint_steps_append(from_steps(*left), seq![step]);
            assert(from_steps(f) =~= from_steps(*left) + seq![step]);
            assert(sprint_steps(seq![step]) =~= step_toks(step)) by {
                reveal_with_fuel(sprint_steps, 2);
                assert(seq![step][0] == step);
                assert(seq![step].drop_first() =~= Seq::<SJoinStep>::empty());
            }
            assert(sprint_from(f) =~= sprint_from(*left) + step_toks(step));
        },
    }
}

// -- FROM fuel + printable over the step decomposition -----------------------

pub open spec fn step_depth(step: SJoinStep) -> nat {
    match step.predicate {
        Some(e) => 1 + sdepth(e),
        None => 1,
    }
}

pub open spec fn steps_depth(steps: Seq<SJoinStep>) -> nat
    decreases steps,
{
    if steps.len() == 0 {
        1
    } else {
        let d = step_depth(steps[0]);
        let rest = steps_depth(steps.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

pub open spec fn sdepth_from(f: SFrom) -> nat {
    (1 + steps_depth(from_steps(f))) as nat
}

pub open spec fn printable_step(step: SJoinStep) -> bool {
    is_stable(step.right)
        && (match step.join_type {
            ast::JoinType::Cross => step.predicate is None,
            _ => step.predicate is Some && printable_se(step.predicate->Some_0),
        })
}

pub open spec fn all_printable_steps(steps: Seq<SJoinStep>) -> bool
    decreases steps,
{
    if steps.len() == 0 {
        true
    } else {
        printable_step(steps[0]) && all_printable_steps(steps.drop_first())
    }
}

pub proof fn all_printable_steps_append(xs: Seq<SJoinStep>, ys: Seq<SJoinStep>)
    ensures all_printable_steps(xs + ys) == (all_printable_steps(xs) && all_printable_steps(ys)),
    decreases xs,
{
    if xs.len() == 0 {
        assert(xs + ys =~= ys);
    } else {
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys);
        all_printable_steps_append(xs.drop_first(), ys);
    }
}

/// `printable_from` guarantees a stable head table and printable step list.
pub proof fn printable_from_decomp(f: SFrom)
    requires printable_from(f),
    ensures
        is_stable(from_head(f)),
        all_printable_steps(from_steps(f)),
    decreases f,
{
    match f {
        SFrom::Table { .. } => {},
        SFrom::Join { left, right, join_type, predicate } => {
            printable_from_decomp(*left);
            let step = SJoinStep { join_type, right: *right, predicate };
            all_printable_steps_append(from_steps(*left), seq![step]);
            assert(printable_step(step));
            assert(all_printable_steps(seq![step])) by {
                reveal_with_fuel(all_printable_steps, 2);
                assert(seq![step][0] == step);
                assert(printable_step(step));
                assert(seq![step].drop_first() =~= Seq::<SJoinStep>::empty());
            }
            assert(from_steps(f) =~= from_steps(*left) + seq![step]);
        },
    }
}

// -- parser ------------------------------------------------------------------

pub open spec fn is_join_kw(t: TokenView) -> bool {
    t == TokenView::Keyword(Keyword::Cross)
        || t == TokenView::Keyword(Keyword::Inner)
        || t == TokenView::Keyword(Keyword::Left)
        || t == TokenView::Keyword(Keyword::Right)
}

pub open spec fn join_type_of(t: TokenView) -> Option<ast::JoinType> {
    if t == TokenView::Keyword(Keyword::Cross) {
        Some(ast::JoinType::Cross)
    } else if t == TokenView::Keyword(Keyword::Inner) {
        Some(ast::JoinType::Inner)
    } else if t == TokenView::Keyword(Keyword::Left) {
        Some(ast::JoinType::Left)
    } else if t == TokenView::Keyword(Keyword::Right) {
        Some(ast::JoinType::Right)
    } else {
        None
    }
}

pub open spec fn sparse_table(input: Seq<TokenView>) -> (Option<SFrom>, Seq<TokenView>) {
    if input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                if input.len() >= 3 && input[1] == TokenView::Keyword(Keyword::As) {
                    match input[2] {
                        TokenView::Ident(a) => (
                            Some(SFrom::Table { name, alias: Some(a) }),
                            input.drop_first().drop_first().drop_first(),
                        ),
                        _ => (None, input),
                    }
                } else {
                    (Some(SFrom::Table { name, alias: None }), input.drop_first())
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_step(input: Seq<TokenView>, fuel: nat) -> (Option<SJoinStep>, Seq<TokenView>) {
    if input.len() >= 2 && input[1] == TokenView::Keyword(Keyword::Join) {
        match join_type_of(input[0]) {
            Some(jt) => match sparse_table(input.drop_first().drop_first()) {
                (Some(right), r) => {
                    if is_cross(jt) {
                        (Some(SJoinStep { join_type: jt, right, predicate: None }), r)
                    } else if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::On) {
                        match sparse(r.drop_first(), fuel) {
                            (Some(e), r2) => (
                                Some(SJoinStep { join_type: jt, right, predicate: Some(e) }),
                                r2,
                            ),
                            (None, _) => (None, input),
                        }
                    } else {
                        (None, input)
                    }
                },
                (None, _) => (None, input),
            },
            None => (None, input),
        }
    } else {
        (None, input)
    }
}

pub open spec fn sparse_steps(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<SJoinStep>>, Seq<TokenView>)
    decreases fuel,
{
    if input.len() >= 1 && is_join_kw(input[0]) {
        if fuel == 0 {
            (None, input)
        } else {
            match sparse_step(input, fuel) {
                (Some(step), rest) => match sparse_steps(rest, (fuel - 1) as nat) {
                    (Some(more), rest2) => (Some(seq![step] + more), rest2),
                    (None, _) => (None, input),
                },
                (None, _) => (None, input),
            }
        }
    } else {
        (Some(Seq::empty()), input)
    }
}

pub open spec fn sparse_from(input: Seq<TokenView>, fuel: nat) -> (Option<SFrom>, Seq<TokenView>) {
    match sparse_table(input) {
        (Some(head), r) => match sparse_steps(r, fuel) {
            (Some(steps), r2) => (Some(fold_joins(head, steps)), r2),
            (None, _) => (None, input),
        },
        (None, _) => (None, input),
    }
}

// -- roundtrip ---------------------------------------------------------------

pub open spec fn step_tail_ok(tail: Seq<TokenView>) -> bool {
    tail.len() == 0
        || (tail[0] != TokenView::Keyword(Keyword::As)
            && tail[0] != TokenView::Period
            && tail[0] != TokenView::OpenParen)
}

pub open spec fn from_tail_ok(tail: Seq<TokenView>) -> bool {
    step_tail_ok(tail) && (tail.len() == 0 || !is_join_kw(tail[0]))
}

pub proof fn lemma_sparse_table_sprint(t: SFrom, tail: Seq<TokenView>)
    requires
        is_stable(t),
        tail.len() == 0 || tail[0] != TokenView::Keyword(Keyword::As),
    ensures
        sparse_table(sprint_table(t) + tail) == (Some(t), tail),
{
    match t {
        SFrom::Table { name, alias: None } => {
            assert(sprint_table(t) + tail =~= seq![TokenView::Ident(name)] + tail);
            assert((sprint_table(t) + tail).drop_first() =~= tail);
        },
        SFrom::Table { name, alias: Some(a) } => {
            assert(sprint_table(t) + tail =~= seq![
                TokenView::Ident(name), TokenView::Keyword(Keyword::As), TokenView::Ident(a),
            ] + tail);
            assert((sprint_table(t) + tail).drop_first().drop_first().drop_first() =~= tail);
        },
        _ => {},
    }
}

pub proof fn lemma_sparse_step_sprint(step: SJoinStep, tail: Seq<TokenView>, fuel: nat)
    requires
        printable_step(step),
        fuel >= step_depth(step),
        step_tail_ok(tail),
    ensures
        sparse_step(step_toks(step) + tail, fuel) == (Some(step), tail),
{
    let input = step_toks(step) + tail;
    // join keywords
    assert(input[0] == join_kws(step.join_type)[0]);
    assert(input[1] == TokenView::Keyword(Keyword::Join));
    assert(join_type_of(input[0]) == Some(step.join_type)) by {
        match step.join_type {
            ast::JoinType::Cross => {},
            ast::JoinType::Inner => {},
            ast::JoinType::Left => {},
            ast::JoinType::Right => {},
        }
    }
    let after_jt = input.drop_first().drop_first();
    let pred_toks = match step.predicate {
        Some(e) => seq![TokenView::Keyword(Keyword::On)] + sprint(e),
        None => Seq::<TokenView>::empty(),
    };
    assert(after_jt =~= sprint_table(step.right) + (pred_toks + tail));
    // the right table's tail (pred_toks + tail) never starts with AS
    assert((pred_toks + tail).len() == 0 || (pred_toks + tail)[0] != TokenView::Keyword(Keyword::As)) by {
        match step.predicate {
            Some(e) => { assert((pred_toks + tail)[0] == TokenView::Keyword(Keyword::On)); },
            None => { assert(pred_toks + tail =~= tail); },
        }
    }
    lemma_sparse_table_sprint(step.right, pred_toks + tail);
    match step.predicate {
        Some(e) => {
            assert(!is_cross(step.join_type));
            assert(pred_toks + tail =~= seq![TokenView::Keyword(Keyword::On)] + (sprint(e) + tail));
            assert((pred_toks + tail)[0] == TokenView::Keyword(Keyword::On));
            assert((pred_toks + tail).drop_first() =~= sprint(e) + tail);
            lemma_sparse_sprint(e, tail, fuel);
        },
        None => {
            assert(is_cross(step.join_type));
            assert(pred_toks + tail =~= tail);
        },
    }
}

/// The step-list roundtrip (a forward list of join steps).
#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_steps_sprint(steps: Seq<SJoinStep>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_steps(steps),
        fuel >= steps_depth(steps),
        from_tail_ok(tail),
    ensures
        sparse_steps(sprint_steps(steps) + tail, fuel) == (Some(steps), tail),
    decreases steps,
{
    reveal_with_fuel(sparse_steps, 1);
    if steps.len() == 0 {
        assert(sprint_steps(steps) + tail =~= tail);
    } else {
        let rest = steps.drop_first();
        let rest_tail = sprint_steps(rest) + tail;
        // input starts with steps[0]'s join keyword
        assert(sprint_steps(steps) + tail =~= step_toks(steps[0]) + rest_tail);
        assert(step_toks(steps[0])[0] == join_kws(steps[0].join_type)[0]);
        assert(is_join_kw(step_toks(steps[0])[0]));
        assert((sprint_steps(steps) + tail)[0] == step_toks(steps[0])[0]);
        // rest_tail is a valid step tail (starts with a join kw, comma, or clause kw)
        assert(step_tail_ok(rest_tail)) by {
            if rest.len() == 0 {
                assert(rest_tail =~= tail);
            } else {
                assert(rest_tail =~= step_toks(rest[0]) + (sprint_steps(rest.drop_first()) + tail));
                assert(rest_tail[0] == join_kws(rest[0].join_type)[0]);
            }
        }
        lemma_sparse_step_sprint(steps[0], rest_tail, fuel);
        lemma_sparse_steps_sprint(rest, tail, (fuel - 1) as nat);
        assert(seq![steps[0]] + rest =~= steps);
        assert(sparse_steps(sprint_steps(steps) + tail, fuel) == (Some(steps), tail));
    }
}

/// The FROM join-tree roundtrip.
pub proof fn lemma_sparse_from_sprint(f: SFrom, tail: Seq<TokenView>, fuel: nat)
    requires
        printable_from(f),
        fuel >= steps_depth(from_steps(f)),
        from_tail_ok(tail),
    ensures
        sparse_from(sprint_from(f) + tail, fuel) == (Some(f), tail),
{
    sprint_decomp(f);
    printable_from_decomp(f);
    fold_decomp(f);
    let steps = from_steps(f);
    let head = from_head(f);
    let head_tail = sprint_steps(steps) + tail;
    assert(sprint_from(f) + tail =~= sprint_table(head) + head_tail);
    // head_tail never starts with AS (join kw or from tail)
    assert(head_tail.len() == 0 || head_tail[0] != TokenView::Keyword(Keyword::As)) by {
        if steps.len() == 0 {
            assert(head_tail =~= tail);
        } else {
            assert(head_tail =~= step_toks(steps[0]) + (sprint_steps(steps.drop_first()) + tail));
            assert(head_tail[0] == join_kws(steps[0].join_type)[0]);
        }
    }
    lemma_sparse_table_sprint(head, head_tail);
    lemma_sparse_steps_sprint(steps, tail, fuel);
}

/// The canonical mirror statement printer roundtrips at self-supplied fuel.
pub proof fn mirror_roundtrip_stmt(s: SStmt)
    requires printable_stmt(s),
    ensures sparse_stmt(sprint_stmt(s), sdepth_stmt(s)) == (Some(s), Seq::<TokenView>::empty()),
{
    lemma_sparse_stmt_sprint(s, sdepth_stmt(s));
}

/// The canonical mirror statement printer is injective on its printable domain.
pub proof fn mirror_injective_stmt(left: SStmt, right: SStmt)
    requires printable_stmt(left), printable_stmt(right),
    ensures sprint_stmt(left) == sprint_stmt(right) ==> left == right,
{
    if sprint_stmt(left) == sprint_stmt(right) {
        let fuel = if sdepth_stmt(left) >= sdepth_stmt(right) {
            sdepth_stmt(left)
        } else {
            sdepth_stmt(right)
        };
        lemma_sparse_stmt_sprint(left, fuel);
        lemma_sparse_stmt_sprint(right, fuel);
    }
}

} // verus!
