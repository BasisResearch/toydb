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
    all_printable_se, boundary, lemma_sparse_args_sprint, lemma_sparse_sprint, parse_args_exec,
    parse_expr_exec, print_args_slice, print_expr_exec, printable_se, sdepth, sdepth_le_len,
    slist_depth, sparse, sparse_args, sprint, sprint_args, token_views_len, token_views_suffix,
    view_args, view_args_len, view_expr, SExpr,
};
#[allow(unused_imports)]
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
#[allow(unused_imports)]
use super::verified_production::{token_view, token_views, token_views_concat};
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
    Update { table: String, set: Seq<(String, Option<SExpr>)>, where_clause: Option<SExpr> },
    Select {
        select: Seq<(SExpr, Option<String>)>,
        from: Seq<SFrom>,
        where_clause: Option<SExpr>,
        group_by: Seq<SExpr>,
        having: Option<SExpr>,
        order_by: Seq<(SExpr, ast::Direction)>,
        limit: Option<SExpr>,
        offset: Option<SExpr>,
    },
    Explain(Box<SStmt>),
    Unsupported,
}

pub open spec fn view_select_list(items: Seq<(ast::Expression, Option<String>)>) -> Seq<(SExpr, Option<String>)>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![(view_expr(items[0].0), items[0].1)] + view_select_list(items.drop_first())
    }
}

pub open spec fn view_froms(froms: Seq<ast::From>) -> Seq<SFrom>
    decreases froms,
{
    if froms.len() == 0 {
        Seq::empty()
    } else {
        seq![view_from(froms[0])] + view_froms(froms.drop_first())
    }
}

pub open spec fn view_order_list(items: Seq<(ast::Expression, ast::Direction)>) -> Seq<(SExpr, ast::Direction)>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![(view_expr(items[0].0), items[0].1)] + view_order_list(items.drop_first())
    }
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
        ast::Statement::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } => SStmt::Select {
            select: view_select_list(select@),
            from: view_froms(from@),
            where_clause: match where_clause {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            group_by: view_args(group_by@),
            having: match having {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            order_by: view_order_list(order_by@),
            limit: match limit {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            offset: match offset {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
        // S4: `Update.set` is a `BTreeMap`, whose spec view is an *unordered*
        // `Map` — a pure `spec fn` cannot canonicalise it to the sorted mirror
        // sequence in general (see plan). The single-assignment case needs no
        // ordering: the sole (key, value) is recovered with `dom().choose()`.
        // Multi-assignment maps map to `Unsupported` until the executable,
        // sorted-`iter()` bridge lands.
        ast::Statement::Update { table, set, where_clause } => {
            if set@.dom().len() == 1 {
                let k = set@.dom().choose();
                SStmt::Update {
                    table,
                    set: seq![(k, match set@[k] {
                        Some(e) => Some(view_expr(e)),
                        None => None,
                    })],
                    where_clause: match where_clause {
                        Some(e) => Some(view_expr(e)),
                        None => None,
                    },
                }
            } else {
                SStmt::Unsupported
            }
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

// The column codec (`sprint_column`'s six optional clauses especially) is the
// single heaviest chunk of the module. Kept opaque so its body is not a global
// SMT axiom weighing on every unrelated proof — revealed locally in the column
// lemmas and the column exec printers/parsers.
#[verifier::opaque]
pub open spec fn sprint_column(c: SColumn) -> Seq<TokenView> {
    seq![TokenView::Ident(c.name), datatype_kw(c.datatype)]
        + col_pk_toks(c) + col_null_toks(c) + col_unique_toks(c) + col_index_toks(c)
        + col_ref_toks(c) + col_default_toks(c)
}

#[verifier::opaque]
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

#[verifier::opaque]
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
        SStmt::Update { set, where_clause, .. } =>
            set.len() >= 1 && all_printable_assigns(set)
                && (match where_clause {
                    Some(e) => printable_se(e),
                    None => true,
                }),
        // This checkpoint handles SELECT list + FROM + WHERE; the remaining
        // clauses are constrained empty/None until they are wired in.
        SStmt::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } =>
            select.len() >= 1 && all_printable_select(select)
                && all_printable_froms(from)
                && (match where_clause {
                    Some(e) => printable_se(e),
                    None => true,
                })
                && all_printable_se(group_by)
                && (match having { Some(e) => printable_se(e), None => true })
                && all_printable_order(order_by)
                && (match limit { Some(e) => printable_se(e), None => true })
                && (match offset { Some(e) => printable_se(e), None => true }),
        SStmt::Explain(inner) => !is_sexplain(*inner) && printable_stmt(*inner),
        SStmt::Unsupported => false,
    }
}

// ---- canonical statement printer over the mirror ---------------------------

/// Canonical print of a Select's clauses. Opaque so the Select grammar (which
/// grows clause by clause) stays out of the global SMT context — otherwise the
/// enlarged `sprint_stmt` axiom degrades unrelated proofs (e.g. the fragile
/// CreateTable `slist_depth_columns_le_len`). Revealed only in the Select lemma
/// and `print_select_exec`.
#[verifier::opaque]
pub open spec fn sprint_select_body(
    select: Seq<(SExpr, Option<String>)>,
    from: Seq<SFrom>,
    where_clause: Option<SExpr>,
    group_by: Seq<SExpr>,
    having: Option<SExpr>,
    order_by: Seq<(SExpr, ast::Direction)>,
    limit: Option<SExpr>,
    offset: Option<SExpr>,
) -> Seq<TokenView> {
    seq![TokenView::Keyword(Keyword::Select)] + sprint_select_list(select)
        + (if from.len() > 0 {
            seq![TokenView::Keyword(Keyword::From)] + sprint_from_list(from)
        } else {
            Seq::empty()
        })
        + (match where_clause {
            Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
            None => Seq::empty(),
        })
        + (if group_by.len() > 0 {
            seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]
                + sprint_args(group_by)
        } else {
            Seq::empty()
        })
        + (match having {
            Some(e) => seq![TokenView::Keyword(Keyword::Having)] + sprint(e),
            None => Seq::empty(),
        })
        + (if order_by.len() > 0 {
            seq![TokenView::Keyword(Keyword::Order), TokenView::Keyword(Keyword::By)]
                + sprint_order_list(order_by)
        } else {
            Seq::empty()
        })
        + (match limit {
            Some(e) => seq![TokenView::Keyword(Keyword::Limit)] + sprint(e),
            None => Seq::empty(),
        })
        + (match offset {
            Some(e) => seq![TokenView::Keyword(Keyword::Offset)] + sprint(e),
            None => Seq::empty(),
        })
}

/// Fuel measure of a Select's clauses. Opaque for the same reason as
/// `sprint_select_body`.
#[verifier::opaque]
pub open spec fn sdepth_select_body(
    select: Seq<(SExpr, Option<String>)>,
    from: Seq<SFrom>,
    where_clause: Option<SExpr>,
    group_by: Seq<SExpr>,
    having: Option<SExpr>,
    order_by: Seq<(SExpr, ast::Direction)>,
    limit: Option<SExpr>,
    offset: Option<SExpr>,
) -> nat {
    (1 + select_list_depth(select) + from_list_depth(from)
        + (match where_clause { Some(e) => sdepth(e), None => 0nat })
        + slist_depth(group_by)
        + (match having { Some(e) => sdepth(e), None => 0nat })
        + (if order_by.len() > 0 { order_list_depth(order_by) } else { 0nat })
        + (match limit { Some(e) => sdepth(e), None => 0nat })
        + (match offset { Some(e) => sdepth(e), None => 0nat })) as nat
}

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
        SStmt::Update { table, set, where_clause } => seq![
            TokenView::Keyword(Keyword::Update),
            TokenView::Ident(table),
            TokenView::Keyword(Keyword::Set),
        ] + sprint_set_list(set)
            + (match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
                None => Seq::empty(),
            }),
        SStmt::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } =>
            sprint_select_body(
                select, from, where_clause, group_by, having, order_by, limit, offset,
            ),
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
        SStmt::Update { set, where_clause, .. } =>
            (1 + set_list_depth(set) + (match where_clause {
                Some(e) => sdepth(e),
                None => 0nat,
            })) as nat,
        SStmt::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } =>
            sdepth_select_body(
                select, from, where_clause, group_by, having, order_by, limit, offset,
            ),
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

/// Parse the `[WHERE e] [GROUP BY exprs] [HAVING e]` tail. Opaque + its own
/// roundtrip lemma so `sparse_select`'s body and lemma stay small (else the
/// one-shot symbolic evaluation of the whole nested match blows up the solver).
#[verifier::opaque]
pub open spec fn sparse_where_group(r2: Seq<TokenView>, fuel: nat)
    -> (Option<(Option<SExpr>, Seq<SExpr>, Option<SExpr>)>, Seq<TokenView>) {
    let where_res: (Option<Option<SExpr>>, Seq<TokenView>) =
        if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::Where) {
            match sparse(r2.drop_first(), fuel) {
                (Some(e), r3) => (Some(Some(e)), r3),
                (None, _) => (None, r2),
            }
        } else {
            (Some(None), r2)
        };
    match where_res {
        (Some(where_clause), rw) => {
            let group_res: (Option<Seq<SExpr>>, Seq<TokenView>) =
                if rw.len() >= 2 && rw[0] == TokenView::Keyword(Keyword::Group)
                    && rw[1] == TokenView::Keyword(Keyword::By) {
                    sparse_expr_list(rw.drop_first().drop_first(), fuel)
                } else {
                    (Some(Seq::<SExpr>::empty()), rw)
                };
            match group_res {
                (Some(group_by), rg) => {
                    let having_res: (Option<Option<SExpr>>, Seq<TokenView>) =
                        if rg.len() >= 1 && rg[0] == TokenView::Keyword(Keyword::Having) {
                            match sparse(rg.drop_first(), fuel) {
                                (Some(e), rh) => (Some(Some(e)), rh),
                                (None, _) => (None, rg),
                            }
                        } else {
                            (Some(None), rg)
                        };
                    match having_res {
                        (Some(having), rh) => (Some((where_clause, group_by, having)), rh),
                        (None, _) => (None, r2),
                    }
                },
                (None, _) => (None, r2),
            }
        },
        (None, _) => (None, r2),
    }
}

/// Roundtrip for the WHERE+GROUP+HAVING tail, followed by an arbitrary boundary
/// `tail` (the LIMIT/OFFSET tokens, which open with `LIMIT`/`OFFSET` or end).
#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
pub proof fn lemma_sparse_where_group_sprint(
    where_clause: Option<SExpr>,
    group_by: Seq<SExpr>,
    having: Option<SExpr>,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        match where_clause { Some(e) => printable_se(e) && fuel >= sdepth(e), None => true },
        all_printable_se(group_by),
        fuel >= slist_depth(group_by),
        match having { Some(e) => printable_se(e) && fuel >= sdepth(e), None => true },
        tail.len() == 0
            || (tail[0] != TokenView::Comma && tail[0] != TokenView::Period
                && tail[0] != TokenView::OpenParen
                && tail[0] != TokenView::Keyword(Keyword::Where)
                && tail[0] != TokenView::Keyword(Keyword::Group)
                && tail[0] != TokenView::Keyword(Keyword::Having)),
    ensures ({
        let wherepart = kw_expr_part(where_clause, Keyword::Where);
        let grouppart = if group_by.len() > 0 {
            seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]
                + sprint_args(group_by)
        } else {
            Seq::<TokenView>::empty()
        };
        let havingpart = kw_expr_part(having, Keyword::Having);
        sparse_where_group(wherepart + grouppart + havingpart + tail, fuel)
            == (Some((where_clause, group_by, having)), tail)
    }),
{
    reveal(sparse_where_group);
    let grouppart = if group_by.len() > 0 {
        seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]
            + sprint_args(group_by)
    } else {
        Seq::<TokenView>::empty()
    };
    let wherepart = kw_expr_part(where_clause, Keyword::Where);
    let havingpart = kw_expr_part(having, Keyword::Having);
    assert(wherepart.len() == 0 || wherepart[0] == TokenView::Keyword(Keyword::Where)) by {
        if where_clause is Some { assert(wherepart[0] == TokenView::Keyword(Keyword::Where)); }
    }
    assert(havingpart.len() == 0 || havingpart[0] == TokenView::Keyword(Keyword::Having)) by {
        if having is Some { assert(havingpart[0] == TokenView::Keyword(Keyword::Having)); }
    }
    assert(grouppart.len() == 0 || grouppart[0] == TokenView::Keyword(Keyword::Group)) by {
        if group_by.len() > 0 { assert(grouppart[0] == TokenView::Keyword(Keyword::Group)); }
    }
    let ht = havingpart + tail;
    let gh = grouppart + ht;
    assert(boundary(ht)) by {
        if having is Some { assert(ht[0] == TokenView::Keyword(Keyword::Having)); }
    }
    assert(gh.len() == 0
        || (gh[0] != TokenView::Comma && gh[0] != TokenView::Period
            && gh[0] != TokenView::OpenParen)) by {
        if group_by.len() > 0 { assert(gh[0] == TokenView::Keyword(Keyword::Group)); }
        else { assert(gh =~= ht); }
    }
    assert(boundary(gh));
    let r2 = wherepart + gh;
    assert(r2 =~= wherepart + grouppart + havingpart + tail);
    // WHERE stage — tail is grouppart ++ havingpart ++ tail.
    match where_clause {
        Some(e) => {
            assert(r2 =~= seq![TokenView::Keyword(Keyword::Where)] + (sprint(e) + gh));
            assert(r2[0] == TokenView::Keyword(Keyword::Where));
            assert(r2.drop_first() =~= sprint(e) + gh);
            lemma_sparse_sprint(e, gh, fuel);
        },
        None => {
            assert(r2 =~= gh);
            assert(r2.len() == 0 || r2[0] != TokenView::Keyword(Keyword::Where)) by {
                if group_by.len() > 0 { assert(r2[0] == TokenView::Keyword(Keyword::Group)); }
                else if having is Some { assert(r2[0] == TokenView::Keyword(Keyword::Having)); }
            }
        },
    }
    // GROUP stage — leaves rw == gh, and its expr-list tail is havingpart ++ tail.
    if group_by.len() > 0 {
        assert(gh[0] == TokenView::Keyword(Keyword::Group));
        assert(gh[1] == TokenView::Keyword(Keyword::By));
        assert(gh.drop_first().drop_first() =~= sprint_args(group_by) + ht);
        assert(ht.len() == 0
            || (ht[0] != TokenView::Comma && ht[0] != TokenView::Period
                && ht[0] != TokenView::OpenParen)) by {
            if having is Some { assert(ht[0] == TokenView::Keyword(Keyword::Having)); }
        }
        lemma_sparse_expr_list_sprint(group_by, ht, fuel);
    } else {
        assert(gh =~= ht);
    }
    // HAVING stage — leaves rh == tail.
    assert(having is None ==> (ht.len() == 0 || ht[0] != TokenView::Keyword(Keyword::Having)));
    lemma_sparse_kw_expr_sprint(having, Keyword::Having, tail, fuel);
    assert(ht =~= kw_expr_part(having, Keyword::Having) + tail);
}

/// Parse an optional `KW <expr>` clause (LIMIT / OFFSET).
pub open spec fn sparse_kw_expr(r: Seq<TokenView>, kw: Keyword, fuel: nat)
    -> (Option<Option<SExpr>>, Seq<TokenView>) {
    if r.len() >= 1 && r[0] == TokenView::Keyword(kw) {
        match sparse(r.drop_first(), fuel) {
            (Some(e), r2) => (Some(Some(e)), r2),
            (None, _) => (None, r),
        }
    } else {
        (Some(None), r)
    }
}

/// Canonical print of an optional `KW <expr>` clause.
pub open spec fn kw_expr_part(clause: Option<SExpr>, kw: Keyword) -> Seq<TokenView> {
    match clause {
        Some(e) => seq![TokenView::Keyword(kw)] + sprint(e),
        None => Seq::<TokenView>::empty(),
    }
}

/// Roundtrip for one optional `KW <expr>` clause with an arbitrary boundary tail.
pub proof fn lemma_sparse_kw_expr_sprint(
    clause: Option<SExpr>,
    kw: Keyword,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        match clause { Some(e) => printable_se(e) && fuel >= sdepth(e), None => true },
        boundary(tail),
        clause is None ==> (tail.len() == 0 || tail[0] != TokenView::Keyword(kw)),
    ensures
        sparse_kw_expr(kw_expr_part(clause, kw) + tail, kw, fuel) == (Some(clause), tail),
{
    let input = kw_expr_part(clause, kw) + tail;
    match clause {
        Some(e) => {
            assert(input =~= seq![TokenView::Keyword(kw)] + (sprint(e) + tail));
            assert(input[0] == TokenView::Keyword(kw));
            assert(input.drop_first() =~= sprint(e) + tail);
            lemma_sparse_sprint(e, tail, fuel);
        },
        None => { assert(input =~= tail); },
    }
}

/// Parse the `[LIMIT e] [OFFSET e]` tail (2 clauses, kept separate from
/// `sparse_where_group` so each opaque parser's exec refinement stays tractable).
#[verifier::opaque]
pub open spec fn sparse_limit_offset(rh: Seq<TokenView>, fuel: nat)
    -> (Option<(Option<SExpr>, Option<SExpr>)>, Seq<TokenView>) {
    match sparse_kw_expr(rh, Keyword::Limit, fuel) {
        (Some(limit), rl) => {
            match sparse_kw_expr(rl, Keyword::Offset, fuel) {
                (Some(offset), ro) => (Some((limit, offset)), ro),
                (None, _) => (None, rh),
            }
        },
        (None, _) => (None, rh),
    }
}

/// Roundtrip for the LIMIT+OFFSET tail.
pub proof fn lemma_sparse_limit_offset_sprint(
    limit: Option<SExpr>,
    offset: Option<SExpr>,
    fuel: nat,
)
    requires
        match limit { Some(e) => printable_se(e) && fuel >= sdepth(e), None => true },
        match offset { Some(e) => printable_se(e) && fuel >= sdepth(e), None => true },
    ensures
        sparse_limit_offset(kw_expr_part(limit, Keyword::Limit)
            + kw_expr_part(offset, Keyword::Offset), fuel)
            == (Some((limit, offset)), Seq::<TokenView>::empty()),
{
    reveal(sparse_limit_offset);
    let limitpart = kw_expr_part(limit, Keyword::Limit);
    let offsetpart = kw_expr_part(offset, Keyword::Offset);
    assert(offsetpart.len() == 0 || offsetpart[0] == TokenView::Keyword(Keyword::Offset)) by {
        if offset is Some { assert(offsetpart[0] == TokenView::Keyword(Keyword::Offset)); }
    }
    assert(boundary(offsetpart));
    lemma_sparse_kw_expr_sprint(offset, Keyword::Offset, Seq::<TokenView>::empty(), fuel);
    assert(limit is None ==> (offsetpart.len() == 0
        || offsetpart[0] != TokenView::Keyword(Keyword::Limit)));
    lemma_sparse_kw_expr_sprint(limit, Keyword::Limit, offsetpart, fuel);
    assert(offsetpart + Seq::<TokenView>::empty() =~= offsetpart);
}

/// Canonical print of the optional `ORDER BY <items>` clause.
pub open spec fn order_part(order_by: Seq<(SExpr, ast::Direction)>) -> Seq<TokenView> {
    if order_by.len() > 0 {
        seq![TokenView::Keyword(Keyword::Order), TokenView::Keyword(Keyword::By)]
            + sprint_order_list(order_by)
    } else {
        Seq::<TokenView>::empty()
    }
}

/// Parse the optional `ORDER BY <items>` clause (kept as its own opaque so each
/// parser's exec refinement stays tractable — the proven 3+2 split recipe).
#[verifier::opaque]
pub open spec fn sparse_order_clause(r: Seq<TokenView>, fuel: nat)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>) {
    if r.len() >= 2 && r[0] == TokenView::Keyword(Keyword::Order)
        && r[1] == TokenView::Keyword(Keyword::By) {
        match sparse_order_list(r.drop_first().drop_first(), fuel) {
            (Some(items), r2) => (Some(items), r2),
            (None, _) => (None, r),
        }
    } else {
        (Some(Seq::<(SExpr, ast::Direction)>::empty()), r)
    }
}

/// Roundtrip for the ORDER BY clause with an arbitrary boundary tail (the
/// LIMIT/OFFSET tokens, opening with `LIMIT`/`OFFSET` or end).
pub proof fn lemma_sparse_order_clause_sprint(
    order_by: Seq<(SExpr, ast::Direction)>,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        all_printable_order(order_by),
        order_by.len() > 0 ==> fuel >= order_list_depth(order_by),
        tail.len() == 0
            || (tail[0] != TokenView::Comma && tail[0] != TokenView::Period
                && tail[0] != TokenView::OpenParen
                && tail[0] != TokenView::Keyword(Keyword::Order)),
    ensures
        sparse_order_clause(order_part(order_by) + tail, fuel) == (Some(order_by), tail),
{
    reveal(sparse_order_clause);
    if order_by.len() > 0 {
        let input = order_part(order_by) + tail;
        assert(input =~= seq![TokenView::Keyword(Keyword::Order), TokenView::Keyword(Keyword::By)]
            + (sprint_order_list(order_by) + tail));
        assert(input[0] == TokenView::Keyword(Keyword::Order));
        assert(input[1] == TokenView::Keyword(Keyword::By));
        assert(input.drop_first().drop_first() =~= sprint_order_list(order_by) + tail);
        lemma_sparse_order_list_sprint(order_by, tail, fuel);
    } else {
        assert(order_part(order_by) =~= Seq::<TokenView>::empty());
        assert(order_part(order_by) + tail =~= tail);
    }
}

/// `SELECT items [FROM froms] [WHERE e] [GROUP BY exprs] [HAVING e] [ORDER BY ..]
/// [LIMIT e] [OFFSET e]`. `input[0]` is `SELECT`.
pub open spec fn sparse_select(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    match sparse_select_list(input.drop_first(), fuel) {
        (Some(select), r1) => {
            let from_result = if r1.len() >= 1 && r1[0] == TokenView::Keyword(Keyword::From) {
                sparse_from_list(r1.drop_first(), fuel)
            } else {
                (Some(Seq::<SFrom>::empty()), r1)
            };
            match from_result {
                (Some(from), r2) => {
                    match sparse_where_group(r2, fuel) {
                        (Some((where_clause, group_by, having)), rg) => {
                            match sparse_order_clause(rg, fuel) {
                                (Some(order_by), rord) => {
                                    match sparse_limit_offset(rord, fuel) {
                                        (Some((limit, offset)), ro) => (
                                            Some(SStmt::Select {
                                                select, from, where_clause,
                                                group_by, having,
                                                order_by, limit, offset,
                                            }),
                                            ro,
                                        ),
                                        (None, _) => (None, input),
                                    }
                                },
                                (None, _) => (None, input),
                            }
                        },
                        (None, _) => (None, input),
                    }
                },
                (None, _) => (None, input),
            }
        },
        (None, _) => (None, input),
    }
}

/// `UPDATE table SET assignments [WHERE e]`. `input[0]` is known to be `UPDATE`.
pub open spec fn sparse_update(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() >= 3 && input[2] == TokenView::Keyword(Keyword::Set) {
        match input[1] {
            TokenView::Ident(table) => match sparse_set_list(
                input.drop_first().drop_first().drop_first(),
                fuel,
            ) {
                (Some(set), r) => {
                    if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Where) {
                        match sparse(r.drop_first(), fuel) {
                            (Some(e), r2) => (
                                Some(SStmt::Update { table, set, where_clause: Some(e) }),
                                r2,
                            ),
                            (None, _) => (None, input),
                        }
                    } else {
                        (Some(SStmt::Update { table, set, where_clause: None }), r)
                    }
                },
                (None, _) => (None, input),
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
            TokenView::Keyword(Keyword::Update) => sparse_update(input, fuel),
            TokenView::Keyword(Keyword::Select) => sparse_select(input, fuel),
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

/// The Select slice of the statement roundtrip, extracted into its own
/// `spinoff_prover` lemma so the WHERE/GROUP/HAVING + LIMIT/OFFSET composition is
/// evaluated in a fresh minimal context (too big for the main statement lemma).
#[verifier::spinoff_prover]
#[verifier::rlimit(120000)]
pub proof fn lemma_sparse_select_sprint(s: SStmt, fuel: nat)
    requires
        is_sselect(s),
        printable_stmt(s),
        fuel >= sdepth_stmt(s),
    ensures
        sparse_select(sprint_stmt(s), fuel) == (Some(s), Seq::<TokenView>::empty()),
{
    reveal(printable_stmt);
    let tokens = sprint_stmt(s);
    match s {
        SStmt::Select { select, from, where_clause, group_by, having, order_by, limit, offset } => {
            reveal(sprint_select_body);
            reveal(sdepth_select_body);
            let frompart = if from.len() > 0 {
                seq![TokenView::Keyword(Keyword::From)] + sprint_from_list(from)
            } else {
                Seq::<TokenView>::empty()
            };
            let wherepart = match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
                None => Seq::<TokenView>::empty(),
            };
            let grouppart = if group_by.len() > 0 {
                seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]
                    + sprint_args(group_by)
            } else {
                Seq::<TokenView>::empty()
            };
            let havingpart = kw_expr_part(having, Keyword::Having);
            let limitpart = kw_expr_part(limit, Keyword::Limit);
            let offsetpart = kw_expr_part(offset, Keyword::Offset);
            let lo = limitpart + offsetpart;
            let orderpart = order_part(order_by);
            let orderlo = orderpart + lo;
            assert(grouppart.len() == 0 || grouppart[0] == TokenView::Keyword(Keyword::Group)) by {
                if group_by.len() > 0 { assert(grouppart[0] == TokenView::Keyword(Keyword::Group)); }
            }
            assert(havingpart.len() == 0 || havingpart[0] == TokenView::Keyword(Keyword::Having)) by {
                if having is Some { assert(havingpart[0] == TokenView::Keyword(Keyword::Having)); }
            }
            assert(limitpart.len() == 0 || limitpart[0] == TokenView::Keyword(Keyword::Limit)) by {
                if limit is Some { assert(limitpart[0] == TokenView::Keyword(Keyword::Limit)); }
            }
            assert(offsetpart.len() == 0 || offsetpart[0] == TokenView::Keyword(Keyword::Offset)) by {
                if offset is Some { assert(offsetpart[0] == TokenView::Keyword(Keyword::Offset)); }
            }
            assert(orderpart.len() == 0 || orderpart[0] == TokenView::Keyword(Keyword::Order)) by {
                if order_by.len() > 0 { assert(orderpart[0] == TokenView::Keyword(Keyword::Order)); }
            }
            assert(lo.len() == 0
                || (lo[0] != TokenView::Comma && lo[0] != TokenView::Period
                    && lo[0] != TokenView::OpenParen
                    && lo[0] != TokenView::Keyword(Keyword::Where)
                    && lo[0] != TokenView::Keyword(Keyword::Group)
                    && lo[0] != TokenView::Keyword(Keyword::Having)
                    && lo[0] != TokenView::Keyword(Keyword::Order))) by {
                if limit is Some { assert(lo[0] == TokenView::Keyword(Keyword::Limit)); }
                else { assert(lo =~= offsetpart); }
            }
            assert(orderlo.len() == 0
                || (orderlo[0] != TokenView::Comma && orderlo[0] != TokenView::Period
                    && orderlo[0] != TokenView::OpenParen
                    && orderlo[0] != TokenView::Keyword(Keyword::Where)
                    && orderlo[0] != TokenView::Keyword(Keyword::Group)
                    && orderlo[0] != TokenView::Keyword(Keyword::Having))) by {
                if order_by.len() > 0 { assert(orderlo[0] == TokenView::Keyword(Keyword::Order)); }
                else { assert(orderlo =~= lo); }
            }
            let wg = wherepart + grouppart + havingpart + orderlo;
            let select_tail = frompart + wg;
            assert(tokens =~= seq![TokenView::Keyword(Keyword::Select)]
                + sprint_select_list(select) + select_tail);
            assert(tokens[0] == TokenView::Keyword(Keyword::Select));
            assert(tokens.drop_first() =~= sprint_select_list(select) + select_tail);
            assert(wg.len() == 0
                || (wg[0] != TokenView::Comma && !is_join_kw(wg[0])
                    && wg[0] != TokenView::Keyword(Keyword::As)
                    && wg[0] != TokenView::Period && wg[0] != TokenView::OpenParen)) by {
                match where_clause {
                    Some(e) => { assert(wg[0] == TokenView::Keyword(Keyword::Where)); },
                    None => {
                        assert(wg =~= grouppart + havingpart + orderlo);
                        if group_by.len() > 0 { assert(wg[0] == TokenView::Keyword(Keyword::Group)); }
                        else if having is Some { assert(wg[0] == TokenView::Keyword(Keyword::Having)); }
                        else if order_by.len() > 0 { assert(wg[0] == TokenView::Keyword(Keyword::Order)); }
                        else if limit is Some { assert(wg[0] == TokenView::Keyword(Keyword::Limit)); }
                        else if offset is Some { assert(wg[0] == TokenView::Keyword(Keyword::Offset)); }
                    },
                }
            }
            assert(select_tail.len() == 0
                || (select_tail[0] != TokenView::Comma
                    && select_tail[0] != TokenView::Keyword(Keyword::As)
                    && select_tail[0] != TokenView::Period
                    && select_tail[0] != TokenView::OpenParen)) by {
                if from.len() > 0 {
                    assert(select_tail[0] == TokenView::Keyword(Keyword::From));
                } else {
                    assert(select_tail =~= wg);
                }
            }
            lemma_sparse_select_list_sprint(select, select_tail, fuel);
            if from.len() > 0 {
                assert(select_tail =~= seq![TokenView::Keyword(Keyword::From)]
                    + (sprint_from_list(from) + wg));
                assert(select_tail[0] == TokenView::Keyword(Keyword::From));
                assert(select_tail.drop_first() =~= sprint_from_list(from) + wg);
                lemma_sparse_from_list_sprint(from, wg, fuel);
            } else {
                assert(select_tail =~= wg);
                assert(from =~= Seq::<SFrom>::empty());
            }
            assert(sdepth_stmt(s)
                == sdepth_select_body(
                    select, from, where_clause, group_by, having, order_by, limit, offset));
            assert(fuel >= slist_depth(group_by));
            assert(match where_clause { Some(e) => fuel >= sdepth(e), None => true });
            assert(match having { Some(e) => fuel >= sdepth(e), None => true });
            assert(order_by.len() > 0 ==> fuel >= order_list_depth(order_by));
            assert(match limit { Some(e) => fuel >= sdepth(e), None => true });
            assert(match offset { Some(e) => fuel >= sdepth(e), None => true });
            // WHERE/GROUP/HAVING stage — leaves `orderlo` (ORDER BY ++ LIMIT/OFFSET).
            lemma_sparse_where_group_sprint(where_clause, group_by, having, orderlo, fuel);
            assert(wg =~= wherepart + grouppart + havingpart + orderlo);
            assert(sparse_where_group(wg, fuel)
                == (Some((where_clause, group_by, having)), orderlo));
            // ORDER BY stage — consumes `orderpart`, leaves `lo`.
            assert(lo.len() == 0 || lo[0] != TokenView::Keyword(Keyword::Order));
            lemma_sparse_order_clause_sprint(order_by, lo, fuel);
            assert(sparse_order_clause(orderlo, fuel) == (Some(order_by), lo));
            // LIMIT/OFFSET stage — leaves empty.
            lemma_sparse_limit_offset_sprint(limit, offset, fuel);
            assert(sparse_limit_offset(lo, fuel)
                == (Some((limit, offset)), Seq::<TokenView>::empty()));
            assert(sparse_where_group(wg, fuel).1 =~= orderlo);
            assert(sparse_order_clause(sparse_where_group(wg, fuel).1, fuel)
                == (Some(order_by), lo));
            assert(sparse_select(tokens, fuel) == (Some(s), Seq::<TokenView>::empty()));
        },
        _ => { assert(false); },
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
        SStmt::Update { table, set, where_clause } => {
            let wherepart = match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
                None => Seq::<TokenView>::empty(),
            };
            let head = seq![
                TokenView::Keyword(Keyword::Update),
                TokenView::Ident(table),
                TokenView::Keyword(Keyword::Set),
            ];
            assert(tokens =~= head + sprint_set_list(set) + wherepart);
            assert(tokens[0] == TokenView::Keyword(Keyword::Update));
            assert(tokens[1] == TokenView::Ident(table));
            assert(tokens[2] == TokenView::Keyword(Keyword::Set));
            assert(tokens.drop_first().drop_first().drop_first() =~= sprint_set_list(set) + wherepart);
            assert(wherepart.len() == 0
                || (wherepart[0] != TokenView::Comma
                    && wherepart[0] != TokenView::Period
                    && wherepart[0] != TokenView::OpenParen)) by {
                match where_clause {
                    Some(e) => { assert(wherepart[0] == TokenView::Keyword(Keyword::Where)); },
                    None => { assert(wherepart =~= Seq::<TokenView>::empty()); },
                }
            }
            lemma_sparse_set_list_sprint(set, wherepart, fuel);
            match where_clause {
                Some(e) => {
                    assert(wherepart =~= seq![TokenView::Keyword(Keyword::Where)] + sprint(e));
                    assert(wherepart[0] == TokenView::Keyword(Keyword::Where));
                    assert(wherepart.drop_first() =~= sprint(e));
                    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
                    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel);
                },
                None => {
                    assert(wherepart =~= Seq::<TokenView>::empty());
                },
            }
            assert(sparse_update(tokens, fuel) == (Some(s), Seq::<TokenView>::empty()));
        },
        SStmt::Select { .. } => {
            lemma_sparse_select_sprint(s, fuel);
            reveal(sprint_select_body);
            reveal(sdepth_select_body);
            assert(sdepth_stmt(s) >= 1);
            assert(fuel >= 1);
            assert(tokens.len() >= 1);
            assert(tokens[0] == TokenView::Keyword(Keyword::Select));
            assert(sparse_select(tokens, fuel) == (Some(s), Seq::<TokenView>::empty()));
            assert(sparse_stmt(tokens, fuel) == sparse_select(tokens, fuel));
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
#[verifier::spinoff_prover]
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
    reveal(sprint_column);
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
    reveal(sprint_columns);
    reveal(sprint_column);
    reveal(slist_depth_columns);
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

#[verifier::opaque]
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

#[verifier::rlimit(15000)]
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
#[verifier::rlimit(8000)]
pub proof fn lemma_sparse_from_sprint(f: SFrom, tail: Seq<TokenView>, fuel: nat)
    requires
        printable_from(f),
        fuel >= steps_depth(from_steps(f)),
        from_tail_ok(tail),
    ensures
        sparse_from(sprint_from(f) + tail, fuel) == (Some(f), tail),
{
    reveal(sparse_from);
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

// ---- SELECT codec (S3): from-list, select-list, clause soup ----------------

pub open spec fn sprint_from_list(froms: Seq<SFrom>) -> Seq<TokenView>
    decreases froms,
{
    if froms.len() == 0 {
        Seq::empty()
    } else if froms.len() == 1 {
        sprint_from(froms[0])
    } else {
        sprint_from(froms[0]) + seq![TokenView::Comma] + sprint_from_list(froms.drop_first())
    }
}

pub open spec fn from_list_depth(froms: Seq<SFrom>) -> nat
    decreases froms,
{
    if froms.len() == 0 {
        1
    } else {
        let d = steps_depth(from_steps(froms[0]));
        let rest = from_list_depth(froms.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

pub open spec fn all_printable_froms(froms: Seq<SFrom>) -> bool
    decreases froms,
{
    if froms.len() == 0 {
        true
    } else {
        printable_from(froms[0]) && all_printable_froms(froms.drop_first())
    }
}

#[verifier::opaque]
pub open spec fn sparse_from_list(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<SFrom>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse_from(input, fuel) {
            (Some(f), r) => {
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    match sparse_from_list(r.drop_first(), (fuel - 1) as nat) {
                        (Some(more), r2) => (Some(seq![f] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(seq![f]), r)
                }
            },
            (None, _) => (None, input),
        }
    }
}

/// The from-list roundtrip: a comma list of join trees, terminated by a tail
/// that starts with neither a comma nor a join keyword (a clause keyword or end).
#[verifier::rlimit(8000)]
pub proof fn lemma_sparse_from_list_sprint(froms: Seq<SFrom>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_froms(froms),
        froms.len() >= 1,
        fuel >= from_list_depth(froms),
        tail.len() == 0 || (tail[0] != TokenView::Comma && !is_join_kw(tail[0])
            && tail[0] != TokenView::Keyword(Keyword::As)
            && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen),
    ensures
        sparse_from_list(sprint_from_list(froms) + tail, fuel) == (Some(froms), tail),
    decreases froms,
{
    reveal_with_fuel(sparse_from_list, 2);
    if froms.len() == 1 {
        assert(from_tail_ok(tail));
        lemma_sparse_from_sprint(froms[0], tail, fuel);
        assert(sprint_from_list(froms) + tail =~= sprint_from(froms[0]) + tail);
        // after parsing froms[0], leftover is tail; tail[0] != Comma so list stops
        assert(seq![froms[0]] =~= froms);
        assert(sparse_from_list(sprint_from_list(froms) + tail, fuel) == (Some(froms), tail));
    } else {
        let rest = froms.drop_first();
        let item_tail = seq![TokenView::Comma] + (sprint_from_list(rest) + tail);
        assert(from_tail_ok(item_tail)) by {
            assert(item_tail[0] == TokenView::Comma);
        }
        lemma_sparse_from_sprint(froms[0], item_tail, fuel);
        lemma_sparse_from_list_sprint(rest, tail, (fuel - 1) as nat);
        assert(sprint_from_list(froms) + tail =~= sprint_from(froms[0]) + item_tail);
        assert(item_tail[0] == TokenView::Comma);
        assert(item_tail.drop_first() =~= sprint_from_list(rest) + tail);
        assert(seq![froms[0]] + rest =~= froms);
        assert(sparse_from_list(sprint_from_list(froms) + tail, fuel) == (Some(froms), tail));
    }
}

// -- UPDATE SET list (S4): `k = expr` or `k = DEFAULT`, comma-separated -------

pub open spec fn sprint_assign(a: (String, Option<SExpr>)) -> Seq<TokenView> {
    seq![TokenView::Ident(a.0), TokenView::Equal] + (match a.1 {
        Some(e) => sprint(e),
        None => seq![TokenView::Keyword(Keyword::Default)],
    })
}

pub open spec fn printable_assign(a: (String, Option<SExpr>)) -> bool {
    match a.1 {
        Some(e) => printable_se(e),
        None => true,
    }
}

pub open spec fn assign_depth(a: (String, Option<SExpr>)) -> nat {
    match a.1 {
        Some(e) => sdepth(e),
        None => 1,
    }
}

pub open spec fn sprint_set_list(items: Seq<(String, Option<SExpr>)>) -> Seq<TokenView>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_assign(items[0])
    } else {
        sprint_assign(items[0]) + seq![TokenView::Comma] + sprint_set_list(items.drop_first())
    }
}

/// Appending one entry at the end of a set-list: `sprint_set_list` grows by a
/// leading `Comma` then the new assignment (or just the assignment if the list
/// was empty). The append identity the print `iter()` loop's invariant steps on.
pub proof fn sprint_set_list_snoc(s: Seq<(String, Option<SExpr>)>, x: (String, Option<SExpr>))
    ensures
        sprint_set_list(s + seq![x]) == (if s.len() == 0 {
            sprint_assign(x)
        } else {
            sprint_set_list(s) + seq![TokenView::Comma] + sprint_assign(x)
        }),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s + seq![x] =~= seq![x]);
    } else {
        assert((s + seq![x])[0] == s[0]);
        assert((s + seq![x]).drop_first() =~= s.drop_first() + seq![x]);
        assert((s + seq![x]).len() >= 2);
        sprint_set_list_snoc(s.drop_first(), x);
        if s.len() == 1 {
            assert(s.drop_first().len() == 0);
            assert(sprint_set_list(s) == sprint_assign(s[0]));
            assert(sprint_set_list(s + seq![x])
                =~= sprint_set_list(s) + seq![TokenView::Comma] + sprint_assign(x));
        } else {
            assert(sprint_set_list(s)
                == sprint_assign(s[0]) + seq![TokenView::Comma] + sprint_set_list(s.drop_first()));
            assert(sprint_set_list(s + seq![x])
                =~= sprint_set_list(s) + seq![TokenView::Comma] + sprint_assign(x));
        }
    }
}

pub open spec fn set_list_depth(items: Seq<(String, Option<SExpr>)>) -> nat
    decreases items,
{
    if items.len() == 0 {
        1
    } else {
        let d = assign_depth(items[0]);
        let rest = set_list_depth(items.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

pub open spec fn all_printable_assigns(items: Seq<(String, Option<SExpr>)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        printable_assign(items[0]) && all_printable_assigns(items.drop_first())
    }
}

/// Parse `k = expr` or `k = DEFAULT`. The expr is tried first; `DEFAULT` is a
/// keyword that never starts an expression, so `sparse` fails on it and the
/// `DEFAULT` fallback fires — no `sprint(e)[0] != DEFAULT` fact is needed.
#[verifier::opaque]
pub open spec fn sparse_assign(input: Seq<TokenView>, fuel: nat) -> (Option<(String, Option<SExpr>)>, Seq<TokenView>) {
    if input.len() >= 2 && input[1] == TokenView::Equal {
        match input[0] {
            TokenView::Ident(k) => {
                let rest = input.drop_first().drop_first();
                match sparse(rest, fuel) {
                    (Some(e), r) => (Some((k, Some(e))), r),
                    (None, _) => {
                        if rest.len() >= 1 && rest[0] == TokenView::Keyword(Keyword::Default) {
                            (Some((k, None)), rest.drop_first())
                        } else {
                            (None, input)
                        }
                    },
                }
            },
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

pub open spec fn assign_tail_ok(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || (tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
}

pub proof fn lemma_sparse_assign_sprint(a: (String, Option<SExpr>), tail: Seq<TokenView>, fuel: nat)
    requires
        printable_assign(a),
        fuel >= assign_depth(a),
        assign_tail_ok(tail),
    ensures
        sparse_assign(sprint_assign(a) + tail, fuel) == (Some(a), tail),
{
    reveal(sparse_assign);
    let input = sprint_assign(a) + tail;
    assert(input[0] == TokenView::Ident(a.0));
    assert(input[1] == TokenView::Equal);
    let rest = input.drop_first().drop_first();
    match a.1 {
        Some(e) => {
            assert(rest =~= sprint(e) + tail);
            assert(boundary(tail));
            lemma_sparse_sprint(e, tail, fuel);
            assert(sparse_assign(input, fuel) == (Some((a.0, Some(e))), tail));
            assert((a.0, Some(e)) == a);
        },
        None => {
            assert(rest =~= seq![TokenView::Keyword(Keyword::Default)] + tail);
            assert(rest[0] == TokenView::Keyword(Keyword::Default));
            assert(sparse(rest, fuel).0 is None) by {
                reveal_with_fuel(sparse, 1);
            }
            assert(rest.drop_first() =~= tail);
            assert(sparse_assign(input, fuel) == (Some((a.0, None::<SExpr>)), tail));
            assert((a.0, None::<SExpr>) == a);
        },
    }
}

#[verifier::opaque]
pub open spec fn sparse_set_list(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<(String, Option<SExpr>)>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse_assign(input, fuel) {
            (Some(a), r) => {
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    match sparse_set_list(r.drop_first(), (fuel - 1) as nat) {
                        (Some(more), r2) => (Some(seq![a] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(seq![a]), r)
                }
            },
            (None, _) => (None, input),
        }
    }
}

#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_set_list_sprint(items: Seq<(String, Option<SExpr>)>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_assigns(items),
        items.len() >= 1,
        fuel >= set_list_depth(items),
        tail.len() == 0 || (tail[0] != TokenView::Comma
            && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen),
    ensures
        sparse_set_list(sprint_set_list(items) + tail, fuel) == (Some(items), tail),
    decreases items,
{
    reveal_with_fuel(sparse_set_list, 2);
    if items.len() == 1 {
        assert(assign_tail_ok(tail));
        lemma_sparse_assign_sprint(items[0], tail, fuel);
        assert(sprint_set_list(items) + tail =~= sprint_assign(items[0]) + tail);
        assert(seq![items[0]] =~= items);
        assert(sparse_set_list(sprint_set_list(items) + tail, fuel) == (Some(items), tail));
    } else {
        let rest = items.drop_first();
        let item_tail = seq![TokenView::Comma] + (sprint_set_list(rest) + tail);
        assert(assign_tail_ok(item_tail)) by {
            assert(item_tail[0] == TokenView::Comma);
        }
        lemma_sparse_assign_sprint(items[0], item_tail, fuel);
        lemma_sparse_set_list_sprint(rest, tail, (fuel - 1) as nat);
        assert(sprint_set_list(items) + tail =~= sprint_assign(items[0]) + item_tail);
        assert(item_tail[0] == TokenView::Comma);
        assert(item_tail.drop_first() =~= sprint_set_list(rest) + tail);
        assert(seq![items[0]] + rest =~= items);
        assert(sparse_set_list(sprint_set_list(items) + tail, fuel) == (Some(items), tail));
    }
}

// -- bare expr comma-list terminated by a boundary (GROUP BY) -----------------
//
// `sparse_args` is parenthesis-terminated (it stops on `CloseParen`), so it can't
// read `GROUP BY a, b` (terminated by a clause keyword or end). This is the
// boundary-terminated analogue, printing with the shared `sprint_args`.

#[verifier::opaque]
pub open spec fn sparse_expr_list(input: Seq<TokenView>, fuel: nat)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse(input, fuel) {
            (Some(e), r) => {
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    match sparse_expr_list(r.drop_first(), (fuel - 1) as nat) {
                        (Some(more), r2) => (Some(seq![e] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(seq![e]), r)
                }
            },
            (None, _) => (None, input),
        }
    }
}

#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_expr_list_sprint(items: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_se(items),
        items.len() >= 1,
        fuel >= slist_depth(items),
        tail.len() == 0 || (tail[0] != TokenView::Comma
            && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen),
    ensures
        sparse_expr_list(sprint_args(items) + tail, fuel) == (Some(items), tail),
    decreases items,
{
    reveal_with_fuel(sparse_expr_list, 2);
    if items.len() == 1 {
        assert(boundary(tail));
        lemma_sparse_sprint(items[0], tail, fuel);
        assert(sprint_args(items) + tail =~= sprint(items[0]) + tail);
        assert(seq![items[0]] =~= items);
    } else {
        let rest = items.drop_first();
        let item_tail = seq![TokenView::Comma] + (sprint_args(rest) + tail);
        assert(boundary(item_tail)) by { assert(item_tail[0] == TokenView::Comma); }
        lemma_sparse_sprint(items[0], item_tail, fuel);
        lemma_sparse_expr_list_sprint(rest, tail, (fuel - 1) as nat);
        assert(sprint_args(items) =~= sprint(items[0]) + seq![TokenView::Comma] + sprint_args(rest));
        assert(sprint_args(items) + tail =~= sprint(items[0]) + item_tail);
        assert(item_tail[0] == TokenView::Comma);
        assert(item_tail.drop_first() =~= sprint_args(rest) + tail);
        assert(seq![items[0]] + rest =~= items);
    }
}

// -- ORDER BY: (expr, direction) comma-list terminated by a boundary ---------
//
// Each item prints as `<expr> ASC|DESC`. The direction is always emitted (even
// when the source omitted it and defaulted to ASC), so the printed form is
// self-delimiting and the roundtrip is exact. Items are comma-separated and the
// list is terminated by a clause keyword or end of input, like `sparse_expr_list`.

pub open spec fn sprint_direction(d: ast::Direction) -> TokenView {
    match d {
        ast::Direction::Ascending => TokenView::Keyword(Keyword::Asc),
        ast::Direction::Descending => TokenView::Keyword(Keyword::Desc),
    }
}

pub open spec fn sprint_order_item(item: (SExpr, ast::Direction)) -> Seq<TokenView> {
    sprint(item.0) + seq![sprint_direction(item.1)]
}

pub open spec fn sprint_order_list(items: Seq<(SExpr, ast::Direction)>) -> Seq<TokenView>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_order_item(items[0])
    } else {
        sprint_order_item(items[0]) + seq![TokenView::Comma]
            + sprint_order_list(items.drop_first())
    }
}

pub open spec fn all_printable_order(items: Seq<(SExpr, ast::Direction)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        printable_se(items[0].0) && all_printable_order(items.drop_first())
    }
}

pub open spec fn order_list_depth(items: Seq<(SExpr, ast::Direction)>) -> nat
    decreases items,
{
    if items.len() == 0 {
        1
    } else {
        let d = sdepth(items[0].0);
        let rest = order_list_depth(items.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

#[verifier::opaque]
pub open spec fn sparse_order_list(input: Seq<TokenView>, fuel: nat)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse(input, fuel) {
            (Some(e), r) => {
                if r.len() >= 1 && (r[0] == TokenView::Keyword(Keyword::Asc)
                    || r[0] == TokenView::Keyword(Keyword::Desc)) {
                    let d = if r[0] == TokenView::Keyword(Keyword::Asc) {
                        ast::Direction::Ascending
                    } else {
                        ast::Direction::Descending
                    };
                    let r1 = r.drop_first();
                    if r1.len() >= 1 && r1[0] == TokenView::Comma {
                        match sparse_order_list(r1.drop_first(), (fuel - 1) as nat) {
                            (Some(more), r2) => (Some(seq![(e, d)] + more), r2),
                            (None, _) => (None, input),
                        }
                    } else {
                        (Some(seq![(e, d)]), r1)
                    }
                } else {
                    (None, input)
                }
            },
            (None, _) => (None, input),
        }
    }
}

#[verifier::rlimit(8000)]
pub proof fn lemma_sparse_order_list_sprint(
    items: Seq<(SExpr, ast::Direction)>,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        all_printable_order(items),
        items.len() >= 1,
        fuel >= order_list_depth(items),
        tail.len() == 0 || (tail[0] != TokenView::Comma
            && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen),
    ensures
        sparse_order_list(sprint_order_list(items) + tail, fuel) == (Some(items), tail),
    decreases items,
{
    reveal_with_fuel(sparse_order_list, 2);
    let e = items[0].0;
    let d = items[0].1;
    let dir_tok = sprint_direction(d);
    assert((e, d) == items[0]);
    if items.len() == 1 {
        let etail = seq![dir_tok] + tail;
        assert(boundary(etail)) by { assert(etail[0] == dir_tok); }
        lemma_sparse_sprint(e, etail, fuel);
        assert(sprint_order_list(items) + tail =~= sprint(e) + etail);
        assert(etail.drop_first() =~= tail);
        assert(seq![(e, d)] =~= items);
    } else {
        let rest = items.drop_first();
        let ctail = seq![TokenView::Comma] + (sprint_order_list(rest) + tail);
        let etail = seq![dir_tok] + ctail;
        assert(boundary(etail)) by { assert(etail[0] == dir_tok); }
        lemma_sparse_sprint(e, etail, fuel);
        lemma_sparse_order_list_sprint(rest, tail, (fuel - 1) as nat);
        assert(sprint_order_list(items) =~= sprint_order_item(items[0])
            + seq![TokenView::Comma] + sprint_order_list(rest));
        assert(sprint_order_item(items[0]) =~= sprint(e) + seq![dir_tok]);
        assert(sprint_order_list(items) + tail =~= sprint(e) + etail);
        assert(etail.drop_first() =~= ctail);
        assert(ctail[0] == TokenView::Comma);
        assert(ctail.drop_first() =~= sprint_order_list(rest) + tail);
        assert(seq![(e, d)] + rest =~= items);
    }
}

// -- select-list (exprs with optional AS alias; `*` may not be aliased) ------

pub open spec fn sprint_select_item(item: (SExpr, Option<String>)) -> Seq<TokenView> {
    sprint(item.0) + (match item.1 {
        Some(a) => seq![TokenView::Keyword(Keyword::As), TokenView::Ident(a)],
        None => Seq::empty(),
    })
}

pub open spec fn printable_select_item(item: (SExpr, Option<String>)) -> bool {
    printable_se(item.0) && (match item.0 {
        SExpr::All => item.1 is None,
        _ => true,
    })
}

pub open spec fn sprint_select_list(items: Seq<(SExpr, Option<String>)>) -> Seq<TokenView>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_select_item(items[0])
    } else {
        sprint_select_item(items[0]) + seq![TokenView::Comma] + sprint_select_list(items.drop_first())
    }
}

pub open spec fn select_item_depth(item: (SExpr, Option<String>)) -> nat {
    sdepth(item.0)
}

pub open spec fn select_list_depth(items: Seq<(SExpr, Option<String>)>) -> nat
    decreases items,
{
    if items.len() == 0 {
        1
    } else {
        let d = select_item_depth(items[0]);
        let rest = select_list_depth(items.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

pub open spec fn all_printable_select(items: Seq<(SExpr, Option<String>)>) -> bool
    decreases items,
{
    if items.len() == 0 {
        true
    } else {
        printable_select_item(items[0]) && all_printable_select(items.drop_first())
    }
}

#[verifier::opaque]
pub open spec fn sparse_select_item(input: Seq<TokenView>, fuel: nat) -> (Option<(SExpr, Option<String>)>, Seq<TokenView>) {
    match sparse(input, fuel) {
        (Some(e), r) => {
            if r.len() >= 2 && r[0] == TokenView::Keyword(Keyword::As) {
                match r[1] {
                    TokenView::Ident(a) => (Some((e, Some(a))), r.drop_first().drop_first()),
                    _ => (None, input),
                }
            } else {
                (Some((e, None)), r)
            }
        },
        (None, _) => (None, input),
    }
}

/// A select item ends at a token that is not `AS` (else a bare expr grabs an
/// alias), `.` or `(` (expr boundary).
pub open spec fn select_tail_ok(tail: Seq<TokenView>) -> bool {
    tail.len() == 0
        || (tail[0] != TokenView::Keyword(Keyword::As)
            && tail[0] != TokenView::Period
            && tail[0] != TokenView::OpenParen)
}

pub proof fn lemma_sparse_select_item_sprint(item: (SExpr, Option<String>), tail: Seq<TokenView>, fuel: nat)
    requires
        printable_select_item(item),
        fuel >= select_item_depth(item),
        select_tail_ok(tail),
    ensures
        sparse_select_item(sprint_select_item(item) + tail, fuel) == (Some(item), tail),
{
    reveal(sparse_select_item);
    let e = item.0;
    match item.1 {
        None => {
            assert(sprint_select_item(item) =~= sprint(e));
            assert(sprint_select_item(item) + tail =~= sprint(e) + tail);
            lemma_sparse_sprint(e, tail, fuel);
            // r == tail, tail[0] != As so no alias
            assert(sparse_select_item(sprint_select_item(item) + tail, fuel) == (Some((e, None::<String>)), tail));
            assert((e, None::<String>) == item);
        },
        Some(a) => {
            let alias_tail = seq![TokenView::Keyword(Keyword::As), TokenView::Ident(a)] + tail;
            assert(sprint_select_item(item) + tail =~= sprint(e) + alias_tail);
            assert(alias_tail[0] == TokenView::Keyword(Keyword::As));
            assert(alias_tail[0] != TokenView::Period && alias_tail[0] != TokenView::OpenParen);
            lemma_sparse_sprint(e, alias_tail, fuel);
            assert(alias_tail[1] == TokenView::Ident(a));
            assert(alias_tail.drop_first().drop_first() =~= tail);
            assert(sparse_select_item(sprint_select_item(item) + tail, fuel) == (Some((e, Some(a))), tail));
            assert((e, Some(a)) == item);
        },
    }
}

#[verifier::opaque]
pub open spec fn sparse_select_list(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 {
        (None, input)
    } else {
        match sparse_select_item(input, fuel) {
            (Some(item), r) => {
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    match sparse_select_list(r.drop_first(), (fuel - 1) as nat) {
                        (Some(more), r2) => (Some(seq![item] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(seq![item]), r)
                }
            },
            (None, _) => (None, input),
        }
    }
}

#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_select_list_sprint(items: Seq<(SExpr, Option<String>)>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_select(items),
        items.len() >= 1,
        fuel >= select_list_depth(items),
        tail.len() == 0 || (tail[0] != TokenView::Comma
            && tail[0] != TokenView::Keyword(Keyword::As)
            && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen),
    ensures
        sparse_select_list(sprint_select_list(items) + tail, fuel) == (Some(items), tail),
    decreases items,
{
    reveal_with_fuel(sparse_select_list, 2);
    if items.len() == 1 {
        assert(select_tail_ok(tail));
        lemma_sparse_select_item_sprint(items[0], tail, fuel);
        assert(sprint_select_list(items) + tail =~= sprint_select_item(items[0]) + tail);
        assert(seq![items[0]] =~= items);
        assert(sparse_select_list(sprint_select_list(items) + tail, fuel) == (Some(items), tail));
    } else {
        let rest = items.drop_first();
        let item_tail = seq![TokenView::Comma] + (sprint_select_list(rest) + tail);
        assert(select_tail_ok(item_tail)) by {
            assert(item_tail[0] == TokenView::Comma);
        }
        lemma_sparse_select_item_sprint(items[0], item_tail, fuel);
        lemma_sparse_select_list_sprint(rest, tail, (fuel - 1) as nat);
        assert(sprint_select_list(items) + tail =~= sprint_select_item(items[0]) + item_tail);
        assert(item_tail[0] == TokenView::Comma);
        assert(item_tail.drop_first() =~= sprint_select_list(rest) + tail);
        assert(seq![items[0]] + rest =~= items);
        assert(sparse_select_list(sprint_select_list(items) + tail, fuel) == (Some(items), tail));
    }
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

// ---- S5: executable statement layer (list-free slice) ----------------------
//
// `print_stmt_exec` / `parse_stmt_exec` build and consume a real
// `ast::Statement`, refining `sprint_stmt` / `sparse_stmt` at the `view_stmt`
// level, delegating every embedded expression to `print_expr_exec` /
// `parse_expr_exec` from `verified_roundtrip`. This slice covers the list-free
// statements without the `Begin` number payload: Commit, Rollback, DropTable,
// Delete (optional WHERE), and Explain (recursively). Extending to the
// container statements is future work.

pub open spec fn exec_ok(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::DropTable { .. } => true,
        SStmt::Delete { .. } => true,
        SStmt::Explain(inner) => exec_ok(*inner),
        _ => false,
    }
}

#[verifier::rlimit(8000)]
pub fn print_stmt_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires
        printable_stmt(view_stmt(*s)),
        exec_ok(view_stmt(*s)),
    ensures
        verified_production::token_views(r@) == sprint_stmt(view_stmt(*s)),
    decreases s,
{
    reveal(printable_stmt);
    reveal(exec_ok);
    reveal_with_fuel(verified_production::token_views, 6);
    let mut r: Vec<super::Token> = Vec::new();
    match s {
        ast::Statement::Commit => {
            r.push(super::Token::Keyword(Keyword::Commit));
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
            r
        },
        ast::Statement::Rollback => {
            r.push(super::Token::Keyword(Keyword::Rollback));
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
            r
        },
        ast::Statement::DropTable { name, if_exists } => {
            r.push(super::Token::Keyword(Keyword::Drop));
            r.push(super::Token::Keyword(Keyword::Table));
            if *if_exists {
                r.push(super::Token::Keyword(Keyword::If));
                r.push(super::Token::Keyword(Keyword::Exists));
            }
            r.push(super::Token::Ident(name.clone()));
            proof {
                if *if_exists {
                    assert(r@.drop_first().drop_first().drop_first().drop_first().drop_first()
                        =~= Seq::<super::Token>::empty());
                } else {
                    assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                }
            }
            r
        },
        ast::Statement::Delete { table, where_clause } => {
            r.push(super::Token::Keyword(Keyword::Delete));
            r.push(super::Token::Keyword(Keyword::From));
            r.push(super::Token::Ident(table.clone()));
            match where_clause {
                Some(e) => {
                    r.push(super::Token::Keyword(Keyword::Where));
                    let ghost head = r@;
                    let mut body = print_expr_exec(e);
                    let ghost body_old = body@;
                    r.append(&mut body);
                    proof {
                        assert(r@ =~= head + body_old);
                        verified_production::token_views_concat(head, body_old);
                        assert(head.drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<super::Token>::empty());
                        assert(verified_production::token_views(head) =~= seq![
                            TokenView::Keyword(Keyword::Delete),
                            TokenView::Keyword(Keyword::From),
                            TokenView::Ident(*table),
                            TokenView::Keyword(Keyword::Where),
                        ]);
                    }
                    r
                },
                None => {
                    proof {
                        assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                    }
                    r
                },
            }
        },
        ast::Statement::Explain(inner) => {
            r.push(super::Token::Keyword(Keyword::Explain));
            let ghost head = r@;
            let mut body = print_stmt_exec(inner);
            let ghost body_old = body@;
            r.append(&mut body);
            proof {
                assert(r@ =~= head + body_old);
                verified_production::token_views_concat(head, body_old);
                assert(head.drop_first() =~= Seq::<super::Token>::empty());
                assert(verified_production::token_views(head)
                    =~= seq![TokenView::Keyword(Keyword::Explain)]);
            }
            r
        },
        _ => {
            proof { assert(false); }
            r
        },
    }
}

// -- Insert executable codec -------------------------------------------------

pub proof fn view_rows_step(rows: Seq<Vec<ast::Expression>>)
    requires rows.len() > 0,
    ensures
        view_rows(rows).len() == rows.len(),
        view_rows(rows)[0] == view_args(rows[0]@),
        view_rows(rows).drop_first() == view_rows(rows.drop_first()),
    decreases rows.len(),
{
    assert(view_rows(rows) =~= seq![view_args(rows[0]@)] + view_rows(rows.drop_first()));
    view_rows_len(rows);
}

pub proof fn view_rows_len(rows: Seq<Vec<ast::Expression>>)
    ensures view_rows(rows).len() == rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        view_rows_len(rows.drop_first());
    }
}

#[verifier::rlimit(4000)]
pub fn print_names_slice(names: &[String]) -> (r: Vec<super::Token>)
    ensures token_views(r@) == sprint_names(names@),
    decreases names.len(),
{
    reveal_with_fuel(token_views, 1);
    if names.len() == 0 {
        let r: Vec<super::Token> = Vec::new();
        proof {
            assert(names@ =~= Seq::<String>::empty());
            assert(sprint_names(names@) =~= Seq::<TokenView>::empty());
        }
        r
    } else if names.len() == 1 {
        let mut r: Vec<super::Token> = Vec::new();
        r.push(super::Token::Ident(names[0].clone()));
        proof {
            reveal_with_fuel(token_views, 2);
            assert(r@.drop_first() =~= Seq::<super::Token>::empty());
            assert(token_view(r@[0]) == TokenView::Ident(names@[0]));
            assert(token_views(r@) =~= seq![TokenView::Ident(names@[0])]);
            assert(sprint_names(names@) =~= seq![TokenView::Ident(names@[0])]);
        }
        r
    } else {
        let mut r: Vec<super::Token> = Vec::new();
        r.push(super::Token::Ident(names[0].clone()));
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(names, 1, names.len());
        proof { assert(rest@ =~= names@.drop_first()); }
        let mut more = print_names_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 3);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            assert(head.drop_first().drop_first() =~= Seq::<super::Token>::empty());
            assert(token_views(head) =~= seq![TokenView::Ident(names@[0]), TokenView::Comma]);
            assert(sprint_names(names@) =~= seq![TokenView::Ident(names@[0]), TokenView::Comma]
                + sprint_names(names@.drop_first()));
        }
        r
    }
}

pub fn print_row_exec(row: &[ast::Expression]) -> (r: Vec<super::Token>)
    requires all_printable_se(view_args(row@)),
    ensures token_views(r@) == sprint_row(view_args(row@)),
{
    reveal_with_fuel(token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(super::Token::OpenParen);
    let ghost open = r@;
    let mut body = print_args_slice(row);
    let ghost body_old = body@;
    r.append(&mut body);
    r.push(super::Token::CloseParen);
    proof {
        assert(open.drop_first() =~= Seq::<super::Token>::empty());
        assert(r@ =~= open + body_old + seq![super::Token::CloseParen]);
        token_views_concat(open + body_old, seq![super::Token::CloseParen]);
        token_views_concat(open, body_old);
        assert(token_views(open) =~= seq![TokenView::OpenParen]);
        assert(token_views(seq![super::Token::CloseParen]) =~= seq![TokenView::CloseParen]);
        assert(sprint_row(view_args(row@)) =~= seq![TokenView::OpenParen]
            + sprint_args(view_args(row@)) + seq![TokenView::CloseParen]);
    }
    r
}

#[verifier::rlimit(4000)]
pub fn print_rows_slice(rows: &[Vec<ast::Expression>]) -> (r: Vec<super::Token>)
    requires rows.len() >= 1, all_printable_rows(view_rows(rows@)),
    ensures token_views(r@) == sprint_rows(view_rows(rows@)),
    decreases rows.len(),
{
    reveal_with_fuel(token_views, 1);
    if rows.len() == 1 {
        proof {
            view_rows_step(rows@);
            assert(view_rows(rows@.drop_first()) =~= Seq::<Seq<SExpr>>::empty());
            assert(all_printable_se(view_args(rows@[0]@)));
            assert(sprint_rows(view_rows(rows@)) == sprint_row(view_rows(rows@)[0]));
        }
        print_row_exec(rows[0].as_slice())
    } else {
        proof {
            view_rows_step(rows@);
            assert(all_printable_se(view_args(rows@[0]@)));
            assert(all_printable_rows(view_rows(rows@.drop_first())));
        }
        let mut r = print_row_exec(rows[0].as_slice());
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(rows, 1, rows.len());
        proof { assert(rest@ =~= rows@.drop_first()); }
        let mut more = print_rows_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            token_views_concat(p0, seq![super::Token::Comma]);
            assert(token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            assert(sprint_rows(view_rows(rows@)) =~= sprint_row(view_rows(rows@)[0])
                + seq![TokenView::Comma] + sprint_rows(view_rows(rows@).drop_first()));
            view_rows_step(rows@);
        }
        r
    }
}

pub proof fn view_columns_len(cols: Seq<ast::Column>)
    ensures view_columns(cols).len() == cols.len(),
    decreases cols.len(),
{
    if cols.len() > 0 {
        view_columns_len(cols.drop_first());
    }
}

pub proof fn view_columns_step(cols: Seq<ast::Column>)
    requires cols.len() > 0,
    ensures
        view_columns(cols).len() == cols.len(),
        view_columns(cols)[0] == view_column(cols[0]),
        view_columns(cols).drop_first() == view_columns(cols.drop_first()),
{
    assert(view_columns(cols) =~= seq![view_column(cols[0])] + view_columns(cols.drop_first()));
    view_columns_len(cols);
}

#[verifier::rlimit(4000)]
pub fn print_columns_slice(cols: &[ast::Column]) -> (r: Vec<super::Token>)
    requires cols.len() >= 1, all_printable_columns(view_columns(cols@)),
    ensures token_views(r@) == sprint_columns(view_columns(cols@)),
    decreases cols.len(),
{
    reveal_with_fuel(token_views, 1);
    reveal(sprint_columns);
    reveal(sprint_column);
    if cols.len() == 1 {
        proof {
            view_columns_step(cols@);
            assert(view_columns(cols@.drop_first()) =~= Seq::<SColumn>::empty());
            assert(printable_column(view_column(cols@[0])));
            assert(sprint_columns(view_columns(cols@)) == sprint_column(view_columns(cols@)[0]));
        }
        print_column_exec(&cols[0])
    } else {
        proof {
            view_columns_step(cols@);
            assert(printable_column(view_column(cols@[0])));
            assert(all_printable_columns(view_columns(cols@.drop_first())));
        }
        let mut r = print_column_exec(&cols[0]);
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(cols, 1, cols.len());
        proof { assert(rest@ =~= cols@.drop_first()); }
        let mut more = print_columns_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            token_views_concat(p0, seq![super::Token::Comma]);
            assert(token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            view_columns_step(cols@);
            assert(sprint_columns(view_columns(cols@)) =~= sprint_column(view_columns(cols@)[0])
                + seq![TokenView::Comma] + sprint_columns(view_columns(cols@).drop_first()));
        }
        r
    }
}

pub open spec fn is_screate(s: SStmt) -> bool {
    match s {
        SStmt::CreateTable { .. } => true,
        _ => false,
    }
}

#[verifier::rlimit(8000)]
pub fn print_createtable_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires printable_stmt(view_stmt(*s)), is_screate(view_stmt(*s)),
    ensures token_views(r@) == sprint_stmt(view_stmt(*s)),
{
    reveal(printable_stmt);
    reveal_with_fuel(token_views, 5);
    match s {
        ast::Statement::CreateTable { name, columns } => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Create));
            r.push(super::Token::Keyword(Keyword::Table));
            r.push(super::Token::Ident(name.clone()));
            r.push(super::Token::OpenParen);
            let ghost head = r@;
            let mut body = print_columns_slice(columns.as_slice());
            let ghost body_old = body@;
            r.append(&mut body);
            r.push(super::Token::CloseParen);
            proof {
                view_columns_len(columns@);
                assert(r@ =~= head + body_old + seq![super::Token::CloseParen]);
                token_views_concat(head + body_old, seq![super::Token::CloseParen]);
                token_views_concat(head, body_old);
                assert(head.drop_first().drop_first().drop_first().drop_first()
                    =~= Seq::<super::Token>::empty());
                assert(token_views(head) =~= seq![
                    TokenView::Keyword(Keyword::Create),
                    TokenView::Keyword(Keyword::Table),
                    TokenView::Ident(*name),
                    TokenView::OpenParen,
                ]);
                assert(token_views(seq![super::Token::CloseParen]) =~= seq![TokenView::CloseParen]);
            }
            r
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

// -- Select FROM join-tree exec printer --------------------------------------

pub fn print_table_exec(f: &ast::From) -> (r: Vec<super::Token>)
    requires is_stable(view_from(*f)),
    ensures token_views(r@) == sprint_table(view_from(*f)),
{
    reveal_with_fuel(token_views, 4);
    let mut r: Vec<super::Token> = Vec::new();
    match f {
        ast::From::Table { name, alias } => {
            r.push(super::Token::Ident(name.clone()));
            match alias {
                Some(a) => {
                    r.push(super::Token::Keyword(Keyword::As));
                    r.push(super::Token::Ident(a.clone()));
                    proof {
                        assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                    }
                },
                None => {
                    proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
                },
            }
            r
        },
        _ => {
            proof { assert(false); }
            r
        },
    }
}

/// Append `join_type`'s two keywords.
pub fn print_join_kws(jt: ast::JoinType) -> (r: Vec<super::Token>)
    ensures token_views(r@) == join_kws(jt),
{
    reveal_with_fuel(token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    match jt {
        ast::JoinType::Cross => {
            r.push(super::Token::Keyword(Keyword::Cross));
            r.push(super::Token::Keyword(Keyword::Join));
        },
        ast::JoinType::Inner => {
            r.push(super::Token::Keyword(Keyword::Inner));
            r.push(super::Token::Keyword(Keyword::Join));
        },
        ast::JoinType::Left => {
            r.push(super::Token::Keyword(Keyword::Left));
            r.push(super::Token::Keyword(Keyword::Join));
        },
        ast::JoinType::Right => {
            r.push(super::Token::Keyword(Keyword::Right));
            r.push(super::Token::Keyword(Keyword::Join));
        },
    }
    proof { assert(r@.drop_first().drop_first() =~= Seq::<super::Token>::empty()); }
    r
}

#[verifier::rlimit(8000)]
pub fn print_from_exec(f: &ast::From) -> (r: Vec<super::Token>)
    requires printable_from(view_from(*f)),
    ensures token_views(r@) == sprint_from(view_from(*f)),
    decreases f,
{
    reveal(printable_from);
    reveal_with_fuel(token_views, 1);
    match f {
        ast::From::Table { .. } => print_table_exec(f),
        ast::From::Join { left, right, join_type, predicate } => {
            let mut r = print_from_exec(&**left);
            let ghost lv = r@;
            let mut jk = print_join_kws(*join_type);
            let ghost jkv = jk@;
            r.append(&mut jk);
            let ghost after_jk = r@;
            let mut rt = print_table_exec(&**right);
            let ghost rtv = rt@;
            r.append(&mut rt);
            let ghost after_rt = r@;
            match predicate {
                Some(e) => {
                    r.push(super::Token::Keyword(Keyword::On));
                    let ghost on = r@;
                    let mut body = print_expr_exec(e);
                    let ghost body_old = body@;
                    r.append(&mut body);
                    proof {
                        reveal_with_fuel(token_views, 2);
                        assert(r@ =~= after_rt + seq![super::Token::Keyword(Keyword::On)] + body_old);
                        token_views_concat(after_rt + seq![super::Token::Keyword(Keyword::On)], body_old);
                        token_views_concat(after_rt, seq![super::Token::Keyword(Keyword::On)]);
                        token_views_concat(lv + jkv, rtv);
                        token_views_concat(lv, jkv);
                        assert(token_views(seq![super::Token::Keyword(Keyword::On)])
                            =~= seq![TokenView::Keyword(Keyword::On)]);
                    }
                    r
                },
                None => {
                    proof {
                        token_views_concat(lv + jkv, rtv);
                        token_views_concat(lv, jkv);
                    }
                    r
                },
            }
        },
    }
}

pub proof fn view_froms_len(froms: Seq<ast::From>)
    ensures view_froms(froms).len() == froms.len(),
    decreases froms.len(),
{
    if froms.len() > 0 {
        view_froms_len(froms.drop_first());
    }
}

pub proof fn view_froms_step(froms: Seq<ast::From>)
    requires froms.len() > 0,
    ensures
        view_froms(froms).len() == froms.len(),
        view_froms(froms)[0] == view_from(froms[0]),
        view_froms(froms).drop_first() == view_froms(froms.drop_first()),
{
    assert(view_froms(froms) =~= seq![view_from(froms[0])] + view_froms(froms.drop_first()));
    view_froms_len(froms);
}

#[verifier::rlimit(4000)]
pub fn print_from_list_slice(froms: &[ast::From]) -> (r: Vec<super::Token>)
    requires froms.len() >= 1, all_printable_froms(view_froms(froms@)),
    ensures token_views(r@) == sprint_from_list(view_froms(froms@)),
    decreases froms.len(),
{
    reveal_with_fuel(token_views, 1);
    if froms.len() == 1 {
        proof {
            view_froms_step(froms@);
            assert(view_froms(froms@.drop_first()) =~= Seq::<SFrom>::empty());
            assert(printable_from(view_from(froms@[0])));
            assert(sprint_from_list(view_froms(froms@)) == sprint_from(view_froms(froms@)[0]));
        }
        print_from_exec(&froms[0])
    } else {
        proof {
            view_froms_step(froms@);
            assert(printable_from(view_from(froms@[0])));
            assert(all_printable_froms(view_froms(froms@.drop_first())));
        }
        let mut r = print_from_exec(&froms[0]);
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(froms, 1, froms.len());
        proof { assert(rest@ =~= froms@.drop_first()); }
        let mut more = print_from_list_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            token_views_concat(p0, seq![super::Token::Comma]);
            assert(token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            view_froms_step(froms@);
            assert(sprint_from_list(view_froms(froms@)) =~= sprint_from(view_froms(froms@)[0])
                + seq![TokenView::Comma] + sprint_from_list(view_froms(froms@).drop_first()));
        }
        r
    }
}

// -- select-list exec printer ------------------------------------------------

pub fn print_select_item_exec(item: &(ast::Expression, Option<String>)) -> (r: Vec<super::Token>)
    requires printable_select_item((view_expr(item.0), item.1)),
    ensures token_views(r@) == sprint_select_item((view_expr(item.0), item.1)),
{
    reveal_with_fuel(token_views, 2);
    let mut r = print_expr_exec(&item.0);
    let ghost e_toks = r@;
    match &item.1 {
        Some(a) => {
            r.push(super::Token::Keyword(Keyword::As));
            r.push(super::Token::Ident(a.clone()));
            proof {
                reveal_with_fuel(token_views, 3);
                assert(r@ =~= e_toks + seq![super::Token::Keyword(Keyword::As), super::Token::Ident(*a)]);
                token_views_concat(e_toks, seq![super::Token::Keyword(Keyword::As), super::Token::Ident(*a)]);
                assert(seq![super::Token::Keyword(Keyword::As), super::Token::Ident(*a)]
                    .drop_first().drop_first() =~= Seq::<super::Token>::empty());
            }
        },
        None => {
            proof { assert(r@ =~= e_toks); }
        },
    }
    r
}

pub proof fn view_select_list_len(items: Seq<(ast::Expression, Option<String>)>)
    ensures view_select_list(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        view_select_list_len(items.drop_first());
    }
}

pub proof fn view_select_list_step(items: Seq<(ast::Expression, Option<String>)>)
    requires items.len() > 0,
    ensures
        view_select_list(items).len() == items.len(),
        view_select_list(items)[0] == (view_expr(items[0].0), items[0].1),
        view_select_list(items).drop_first() == view_select_list(items.drop_first()),
{
    assert(view_select_list(items) =~= seq![(view_expr(items[0].0), items[0].1)]
        + view_select_list(items.drop_first()));
    view_select_list_len(items);
}

#[verifier::rlimit(4000)]
pub fn print_select_list_slice(items: &[(ast::Expression, Option<String>)]) -> (r: Vec<super::Token>)
    requires items.len() >= 1, all_printable_select(view_select_list(items@)),
    ensures token_views(r@) == sprint_select_list(view_select_list(items@)),
    decreases items.len(),
{
    reveal_with_fuel(token_views, 1);
    if items.len() == 1 {
        proof {
            view_select_list_step(items@);
            assert(view_select_list(items@.drop_first()) =~= Seq::<(SExpr, Option<String>)>::empty());
            assert(printable_select_item(view_select_list(items@)[0]));
            assert(sprint_select_list(view_select_list(items@)) == sprint_select_item(view_select_list(items@)[0]));
        }
        print_select_item_exec(&items[0])
    } else {
        proof {
            view_select_list_step(items@);
            assert(printable_select_item(view_select_list(items@)[0]));
            assert(all_printable_select(view_select_list(items@.drop_first())));
        }
        let mut r = print_select_item_exec(&items[0]);
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(items, 1, items.len());
        proof { assert(rest@ =~= items@.drop_first()); }
        let mut more = print_select_list_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            token_views_concat(p0, seq![super::Token::Comma]);
            assert(token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            view_select_list_step(items@);
            assert(sprint_select_list(view_select_list(items@)) =~= sprint_select_item(view_select_list(items@)[0])
                + seq![TokenView::Comma] + sprint_select_list(view_select_list(items@).drop_first()));
        }
        r
    }
}

// -- ORDER BY exec printer ---------------------------------------------------

pub fn print_order_item_exec(item: &(ast::Expression, ast::Direction)) -> (r: Vec<super::Token>)
    requires printable_se(view_expr(item.0)),
    ensures token_views(r@) == sprint_order_item((view_expr(item.0), item.1)),
{
    reveal_with_fuel(token_views, 2);
    let mut r = print_expr_exec(&item.0);
    let ghost e_toks = r@;
    match item.1 {
        ast::Direction::Ascending => {
            r.push(super::Token::Keyword(Keyword::Asc));
            proof {
                assert(r@ =~= e_toks + seq![super::Token::Keyword(Keyword::Asc)]);
                token_views_concat(e_toks, seq![super::Token::Keyword(Keyword::Asc)]);
                assert(token_views(seq![super::Token::Keyword(Keyword::Asc)])
                    =~= seq![TokenView::Keyword(Keyword::Asc)]);
            }
        },
        ast::Direction::Descending => {
            r.push(super::Token::Keyword(Keyword::Desc));
            proof {
                assert(r@ =~= e_toks + seq![super::Token::Keyword(Keyword::Desc)]);
                token_views_concat(e_toks, seq![super::Token::Keyword(Keyword::Desc)]);
                assert(token_views(seq![super::Token::Keyword(Keyword::Desc)])
                    =~= seq![TokenView::Keyword(Keyword::Desc)]);
            }
        },
    }
    r
}

pub proof fn view_order_list_len(items: Seq<(ast::Expression, ast::Direction)>)
    ensures view_order_list(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        view_order_list_len(items.drop_first());
    }
}

pub proof fn view_order_list_step(items: Seq<(ast::Expression, ast::Direction)>)
    requires items.len() > 0,
    ensures
        view_order_list(items).len() == items.len(),
        view_order_list(items)[0] == (view_expr(items[0].0), items[0].1),
        view_order_list(items).drop_first() == view_order_list(items.drop_first()),
{
    assert(view_order_list(items) =~= seq![(view_expr(items[0].0), items[0].1)]
        + view_order_list(items.drop_first()));
    view_order_list_len(items);
}

#[verifier::rlimit(4000)]
pub fn print_order_list_slice(items: &[(ast::Expression, ast::Direction)]) -> (r: Vec<super::Token>)
    requires items.len() >= 1, all_printable_order(view_order_list(items@)),
    ensures token_views(r@) == sprint_order_list(view_order_list(items@)),
    decreases items.len(),
{
    reveal_with_fuel(token_views, 1);
    if items.len() == 1 {
        proof {
            view_order_list_step(items@);
            assert(view_order_list(items@.drop_first())
                =~= Seq::<(SExpr, ast::Direction)>::empty());
            assert(printable_se(view_order_list(items@)[0].0));
            assert(sprint_order_list(view_order_list(items@))
                == sprint_order_item(view_order_list(items@)[0]));
        }
        print_order_item_exec(&items[0])
    } else {
        proof {
            view_order_list_step(items@);
            assert(printable_se(view_order_list(items@)[0].0));
            assert(all_printable_order(view_order_list(items@.drop_first())));
        }
        let mut r = print_order_item_exec(&items[0]);
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(items, 1, items.len());
        proof { assert(rest@ =~= items@.drop_first()); }
        let mut more = print_order_list_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            token_views_concat(head, more_old);
            token_views_concat(p0, seq![super::Token::Comma]);
            assert(token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            view_order_list_step(items@);
            assert(sprint_order_list(view_order_list(items@))
                =~= sprint_order_item(view_order_list(items@)[0])
                + seq![TokenView::Comma] + sprint_order_list(view_order_list(items@).drop_first()));
        }
        r
    }
}

pub open spec fn is_sselect(s: SStmt) -> bool {
    match s {
        SStmt::Select { .. } => true,
        _ => false,
    }
}

/// Executable printer for the leading `SELECT items [FROM ..] [WHERE e]
/// [GROUP BY ..] [HAVING e]` clauses, factored out of `print_select_exec` (with
/// `print_select_tail_exec`) so no single function assembles all clauses in one
/// SMT context — an 8-clause inline body crashes the solver with
/// "expected rlimit-count". `print_select_exec` then just concatenates head+tail.
#[verifier::rlimit(20000)]
pub fn print_select_head_exec(
    select: &Vec<(ast::Expression, Option<String>)>,
    from: &Vec<ast::From>,
    where_clause: &Option<ast::Expression>,
    group_by: &Vec<ast::Expression>,
    having: &Option<ast::Expression>,
) -> (r: Vec<super::Token>)
    requires
        select.len() >= 1,
        all_printable_select(view_select_list(select@)),
        all_printable_froms(view_froms(from@)),
        match where_clause { Some(e) => printable_se(view_expr(*e)), None => true },
        all_printable_se(view_args(group_by@)),
        match having { Some(e) => printable_se(view_expr(*e)), None => true },
    ensures
        token_views(r@) ==
            seq![TokenView::Keyword(Keyword::Select)]
            + sprint_select_list(view_select_list(select@))
            + (if view_froms(from@).len() > 0 {
                seq![TokenView::Keyword(Keyword::From)] + sprint_from_list(view_froms(from@))
              } else { Seq::<TokenView>::empty() })
            + (match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(view_expr(*e)),
                None => Seq::<TokenView>::empty() })
            + (if view_args(group_by@).len() > 0 {
                seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]
                    + sprint_args(view_args(group_by@))
              } else { Seq::<TokenView>::empty() })
            + (match having {
                Some(e) => seq![TokenView::Keyword(Keyword::Having)] + sprint(view_expr(*e)),
                None => Seq::<TokenView>::empty() }),
{
    reveal_with_fuel(token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(super::Token::Keyword(Keyword::Select));
    proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
    let ghost sel_head = r@;
    let mut sl = print_select_list_slice(select.as_slice());
    let ghost slo = sl@;
    r.append(&mut sl);
    proof {
        token_views_concat(sel_head, slo);
        assert(token_views(sel_head) =~= seq![TokenView::Keyword(Keyword::Select)]);
    }
    // FROM
    let ghost before_from = r@;
    if from.len() > 0 {
        r.push(super::Token::Keyword(Keyword::From));
        let ghost fk = r@;
        let mut fl = print_from_list_slice(from.as_slice());
        let ghost flo = fl@;
        r.append(&mut fl);
        proof {
            token_views_concat(fk, flo);
            token_views_concat(before_from, seq![super::Token::Keyword(Keyword::From)]);
            assert(fk =~= before_from + seq![super::Token::Keyword(Keyword::From)]);
        }
    }
    let ghost after_from = r@;
    proof {
        view_froms_len(from@);
        if from.len() == 0 { assert(after_from =~= before_from); }
    }
    // WHERE
    match where_clause {
        Some(e) => {
            r.push(super::Token::Keyword(Keyword::Where));
            let ghost wk = r@;
            let mut wb = print_expr_exec(e);
            let ghost wbo = wb@;
            r.append(&mut wb);
            proof {
                token_views_concat(wk, wbo);
                token_views_concat(after_from, seq![super::Token::Keyword(Keyword::Where)]);
                assert(wk =~= after_from + seq![super::Token::Keyword(Keyword::Where)]);
            }
        },
        None => {},
    }
    // GROUP BY
    let ghost after_where = r@;
    if group_by.len() > 0 {
        r.push(super::Token::Keyword(Keyword::Group));
        r.push(super::Token::Keyword(Keyword::By));
        let ghost gk = r@;
        let mut gb = print_args_slice(group_by.as_slice());
        let ghost gbo = gb@;
        r.append(&mut gb);
        proof {
            token_views_concat(gk, gbo);
            token_views_concat(after_where,
                seq![super::Token::Keyword(Keyword::Group), super::Token::Keyword(Keyword::By)]);
            assert(gk =~= after_where
                + seq![super::Token::Keyword(Keyword::Group), super::Token::Keyword(Keyword::By)]);
            assert(token_views(seq![super::Token::Keyword(Keyword::Group),
                super::Token::Keyword(Keyword::By)])
                =~= seq![TokenView::Keyword(Keyword::Group), TokenView::Keyword(Keyword::By)]) by {
                reveal_with_fuel(token_views, 3);
            }
        }
    }
    let ghost after_group = r@;
    proof {
        view_args_len(group_by@);
        if group_by.len() == 0 { assert(after_group =~= after_where); }
    }
    // HAVING
    match having {
        Some(e) => {
            r.push(super::Token::Keyword(Keyword::Having));
            let ghost hk = r@;
            let mut hb = print_expr_exec(e);
            let ghost hbo = hb@;
            r.append(&mut hb);
            proof {
                token_views_concat(hk, hbo);
                token_views_concat(after_group, seq![super::Token::Keyword(Keyword::Having)]);
                assert(hk =~= after_group + seq![super::Token::Keyword(Keyword::Having)]);
            }
        },
        None => {},
    }
    r
}

/// Executable printer for the trailing `[ORDER BY ..] [LIMIT e] [OFFSET e]`
/// clauses, factored out of `print_select_exec` so each function's `token_views`
/// assembly stays within one SMT context (the proven 3+2 split: an 8-clause
/// inline body crashes the solver with "expected rlimit-count").
#[verifier::rlimit(20000)]
pub fn print_select_tail_exec(
    order_by: &Vec<(ast::Expression, ast::Direction)>,
    limit: &Option<ast::Expression>,
    offset: &Option<ast::Expression>,
) -> (r: Vec<super::Token>)
    requires
        all_printable_order(view_order_list(order_by@)),
        match limit { Some(e) => printable_se(view_expr(*e)), None => true },
        match offset { Some(e) => printable_se(view_expr(*e)), None => true },
    ensures
        token_views(r@) == order_part(view_order_list(order_by@))
            + (match limit {
                Some(e) => seq![TokenView::Keyword(Keyword::Limit)] + sprint(view_expr(*e)),
                None => Seq::<TokenView>::empty(),
            })
            + (match offset {
                Some(e) => seq![TokenView::Keyword(Keyword::Offset)] + sprint(view_expr(*e)),
                None => Seq::<TokenView>::empty(),
            }),
{
    reveal_with_fuel(token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    proof { assert(token_views(r@) =~= Seq::<TokenView>::empty()); }
    // ORDER BY
    if order_by.len() > 0 {
        r.push(super::Token::Keyword(Keyword::Order));
        r.push(super::Token::Keyword(Keyword::By));
        let ghost obk = r@;
        let mut obl = print_order_list_slice(order_by.as_slice());
        let ghost oblo = obl@;
        r.append(&mut obl);
        proof {
            token_views_concat(obk, oblo);
            assert(obk =~= seq![super::Token::Keyword(Keyword::Order),
                super::Token::Keyword(Keyword::By)]);
            assert(token_views(seq![super::Token::Keyword(Keyword::Order),
                super::Token::Keyword(Keyword::By)])
                =~= seq![TokenView::Keyword(Keyword::Order), TokenView::Keyword(Keyword::By)]) by {
                reveal_with_fuel(token_views, 3);
            }
            view_order_list_len(order_by@);
            assert(order_part(view_order_list(order_by@))
                =~= seq![TokenView::Keyword(Keyword::Order), TokenView::Keyword(Keyword::By)]
                    + sprint_order_list(view_order_list(order_by@)));
        }
    } else {
        proof {
            view_order_list_len(order_by@);
            assert(order_part(view_order_list(order_by@)) =~= Seq::<TokenView>::empty());
        }
    }
    let ghost after_order = r@;
    proof { assert(token_views(after_order) =~= order_part(view_order_list(order_by@))); }
    // LIMIT
    match limit {
        Some(e) => {
            r.push(super::Token::Keyword(Keyword::Limit));
            let ghost lk = r@;
            let mut lb = print_expr_exec(e);
            let ghost lbo = lb@;
            r.append(&mut lb);
            proof {
                token_views_concat(lk, lbo);
                token_views_concat(after_order, seq![super::Token::Keyword(Keyword::Limit)]);
                assert(lk =~= after_order + seq![super::Token::Keyword(Keyword::Limit)]);
            }
        },
        None => {},
    }
    let ghost after_limit = r@;
    // OFFSET
    match offset {
        Some(e) => {
            r.push(super::Token::Keyword(Keyword::Offset));
            let ghost ok = r@;
            let mut ob = print_expr_exec(e);
            let ghost obo = ob@;
            r.append(&mut ob);
            proof {
                token_views_concat(ok, obo);
                token_views_concat(after_limit, seq![super::Token::Keyword(Keyword::Offset)]);
                assert(ok =~= after_limit + seq![super::Token::Keyword(Keyword::Offset)]);
            }
        },
        None => {},
    }
    r
}

#[verifier::rlimit(20000)]
pub fn print_select_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires printable_stmt(view_stmt(*s)), is_sselect(view_stmt(*s)),
    ensures token_views(r@) == sprint_stmt(view_stmt(*s)),
{
    reveal(printable_stmt);
    reveal(sprint_select_body);
    match s {
        ast::Statement::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } => {
            // Assemble in two halves so no single function builds all clauses in
            // one SMT context (the proven head/tail split).
            let mut r = print_select_head_exec(select, from, where_clause, group_by, having);
            let ghost head = r@;
            let mut tail = print_select_tail_exec(order_by, limit, offset);
            let ghost tailo = tail@;
            r.append(&mut tail);
            proof {
                token_views_concat(head, tailo);
                assert(token_views(r@) =~= sprint_stmt(view_stmt(*s)));
            }
            r
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

pub open spec fn is_sinsert(s: SStmt) -> bool {
    match s {
        SStmt::Insert { .. } => true,
        _ => false,
    }
}

/// Executable BEGIN parser, refining `sparse_begin` at the `view_stmt` level.
/// `sparse_begin` always succeeds (it is the BEGIN-keyword branch of the
/// dispatcher), so this never returns `None`.
#[verifier::rlimit(30000)]
pub fn parse_begin_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos < toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_begin(input);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    // read-only prefix: sparse_begin needs input.len() >= 3 && input[1]==Read && input[2]==Only
    let read_only: bool;
    let after_pos: usize;
    if pos + 1 < toks.len() && pos + 2 < toks.len()
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Read))
        && matches!(toks[pos + 2], super::Token::Keyword(Keyword::Only)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
            token_views_suffix(toks@, pos as int + 2);
        }
        read_only = true;
        after_pos = pos + 3;
    } else {
        proof {
            if pos < toks.len() {
                token_views_suffix(toks@, pos as int);
                if pos + 1 < toks.len() {
                    token_views_suffix(toks@, pos as int + 1);
                    if pos + 2 < toks.len() {
                        token_views_suffix(toks@, pos as int + 2);
                    } else {
                        token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int));
                    }
                } else {
                    token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int));
                }
            }
        }
        read_only = false;
        after_pos = if pos < toks.len() { pos + 1 } else { pos };
    }
    let ghost after = token_views(toks@.subrange(after_pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(after_pos as int, toks@.len() as int)); }
    // AS OF SYSTEM TIME <number>
    if after_pos < toks.len() && after_pos + 1 < toks.len() && after_pos + 2 < toks.len()
        && after_pos + 3 < toks.len() && after_pos + 4 < toks.len()
        && matches!(toks[after_pos], super::Token::Keyword(Keyword::As))
        && matches!(toks[after_pos + 1], super::Token::Keyword(Keyword::Of))
        && matches!(toks[after_pos + 2], super::Token::Keyword(Keyword::System))
        && matches!(toks[after_pos + 3], super::Token::Keyword(Keyword::Time)) {
        proof {
            token_views_suffix(toks@, after_pos as int);
            token_views_suffix(toks@, after_pos as int + 1);
            token_views_suffix(toks@, after_pos as int + 2);
            token_views_suffix(toks@, after_pos as int + 3);
            token_views_suffix(toks@, after_pos as int + 4);
        }
        match &toks[after_pos + 4] {
            super::Token::Number(bytes) => match super::verified_integer::parse_u64(bytes.as_slice()) {
                Some(version) => (
                    Some(ast::Statement::Begin { read_only, as_of: Some(version) }),
                    after_pos + 5,
                ),
                None => (Some(ast::Statement::Begin { read_only, as_of: None }), after_pos),
            },
            _ => (Some(ast::Statement::Begin { read_only, as_of: None }), after_pos),
        }
    } else {
        if after_pos < toks.len() {
            proof {
                token_views_suffix(toks@, after_pos as int);
                if after_pos + 1 < toks.len() {
                    token_views_suffix(toks@, after_pos as int + 1);
                    if after_pos + 2 < toks.len() {
                        token_views_suffix(toks@, after_pos as int + 2);
                        if after_pos + 3 < toks.len() {
                            token_views_suffix(toks@, after_pos as int + 3);
                            if after_pos + 4 < toks.len() {
                                token_views_suffix(toks@, after_pos as int + 4);
                            } else {
                                token_views_len(toks@.subrange(after_pos as int + 4, toks@.len() as int));
                            }
                        } else {
                            token_views_len(toks@.subrange(after_pos as int + 3, toks@.len() as int));
                        }
                    } else {
                        token_views_len(toks@.subrange(after_pos as int + 2, toks@.len() as int));
                    }
                } else {
                    token_views_len(toks@.subrange(after_pos as int + 1, toks@.len() as int));
                }
            }
        }
        (Some(ast::Statement::Begin { read_only, as_of: None }), after_pos)
    }
}

#[verifier::rlimit(20000)]
pub fn parse_columns_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<ast::Column>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_columns(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(vv) => sopt is Some && view_columns(vv@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_columns, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    let (copt, cpos) = parse_column_exec(toks, pos, fuel);
    match copt {
        Some(col) => {
            if cpos >= toks.len() {
                proof { token_views_len(toks@.subrange(cpos as int, toks@.len() as int)); }
                (None, pos)
            } else {
                proof { token_views_suffix(toks@, cpos as int); }
                match &toks[cpos] {
                    super::Token::CloseParen => {
                        let mut v: Vec<ast::Column> = Vec::new();
                        v.push(col);
                        proof {
                            view_columns_step(v@);
                            assert(v@.drop_first() =~= Seq::<ast::Column>::empty());
                        }
                        (Some(v), cpos)
                    },
                    super::Token::Comma => {
                        let (mopt, mpos) = parse_columns_exec(toks, cpos + 1, fuel - 1);
                        match mopt {
                            Some(mut more) => {
                                let mut v: Vec<ast::Column> = Vec::new();
                                v.push(col);
                                let ghost first = v@;
                                let ghost more_old = more@;
                                v.append(&mut more);
                                proof {
                                    assert(v@ =~= first + more_old);
                                    view_columns_step(v@);
                                    assert(v@.drop_first() =~= more_old);
                                }
                                (Some(v), mpos)
                            },
                            None => (None, pos),
                        }
                    },
                    _ => (None, pos),
                }
            }
        },
        None => (None, pos),
    }
}

#[verifier::rlimit(20000)]
pub fn parse_createtable_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_create(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len() && pos + 2 < toks.len() && pos + 3 < toks.len()
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Table))
        && matches!(toks[pos + 3], super::Token::OpenParen) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
            token_views_suffix(toks@, pos as int + 2);
            token_views_suffix(toks@, pos as int + 3);
        }
        match &toks[pos + 2] {
            super::Token::Ident(name) => {
                let (copt, cpos) = parse_columns_exec(toks, pos + 4, fuel);
                match copt {
                    Some(cols) => {
                        if cpos < toks.len() && matches!(toks[cpos], super::Token::CloseParen) {
                            proof { token_views_suffix(toks@, cpos as int); }
                            (
                                Some(ast::Statement::CreateTable { name: name.clone(), columns: cols }),
                                cpos + 1,
                            )
                        } else {
                            if cpos < toks.len() {
                                proof { token_views_suffix(toks@, cpos as int); }
                            } else {
                                proof { token_views_len(toks@.subrange(cpos as int, toks@.len() as int)); }
                            }
                            (None, pos)
                        }
                    },
                    None => (None, pos),
                }
            },
            _ => (None, pos),
        }
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
            if pos + 1 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 1); }
                if pos + 2 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 2); }
                    if pos + 3 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 3); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 3, toks@.len() as int)); }
                    }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                }
            } else {
                proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
            }
        }
        (None, pos)
    }
}

pub open spec fn is_sbegin(s: SStmt) -> bool {
    match s {
        SStmt::Begin { .. } => true,
        _ => false,
    }
}

// -- Update executable codec (single-assignment; trusted String cmp axiom) ----
//
// vstd does not prove `key_obeys_cmp_spec::<String>()`, which gates the
// `BTreeMap` `insert` view and `iter` spec. `String`'s `Ord` is a genuine total
// order that obeys the cmp laws, so we assume this one fact — a true statement,
// audited here, analogous to the three `float_trust` assumptions. It is the only
// new axiom the statement layer introduces.
#[verifier::external_body]
pub proof fn axiom_string_key_obeys_cmp()
    ensures vstd::std_specs::btree::key_obeys_cmp_spec::<String>(),
{
}

// -- Multi-assignment Update foundation: sorted-seq uniqueness ----------------
//
// `iter()` pins its remaining seq to be strictly key-increasing (`increasing_seq`)
// and to cover exactly `m@.kv_pairs()`. That makes the sorted entry seq a *pinned
// function of `m@`* even though no pure spec fn can compute the sort. The
// uniqueness lemma below is what turns "pinned" into a usable normal form: two
// strictly-key-increasing seqs with the same element set are equal.

/// `String`'s `Ord` obeys the full total-order cmp laws (antisymmetry,
/// transitivity, `Equal <==> ==`). Trusted like [[axiom_string_key_obeys_cmp]]
/// (same "String Ord is lawful" boundary); needed to interpret `increasing_seq`
/// over `String` keys, which uses `laws_cmp::obeys_cmp`, not `key_obeys_cmp_spec`.
#[verifier::external_body]
pub proof fn axiom_string_obeys_cmp()
    ensures vstd::laws_cmp::obeys_cmp::<String>(),
{
}

pub open spec fn kv_keys(s: Seq<(String, Option<SExpr>)>) -> Seq<String> {
    s.map_values(|kv: (String, Option<SExpr>)| kv.0)
}

pub proof fn kv_keys_index(s: Seq<(String, Option<SExpr>)>)
    ensures
        kv_keys(s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] kv_keys(s)[i] == s[i].0,
{
}

/// The `cmp_spec` order over `String` keys, unpacked from the trusted axiom:
/// `increasing_seq(kv_keys(s))` means every earlier key is strictly `Less` than
/// every later key.
pub proof fn increasing_keys_lt(s: Seq<(String, Option<SExpr>)>, i: int, j: int)
    requires
        vstd::std_specs::btree::increasing_seq(kv_keys(s)),
        0 <= i < j < s.len(),
    ensures s[i].0.cmp_spec(&s[j].0) == core::cmp::Ordering::Less,
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    kv_keys_index(s);
    assert(kv_keys(s)[i].cmp_spec(&kv_keys(s)[j]) == core::cmp::Ordering::Less);
}

/// Reflexivity and antisymmetry of `String::cmp_spec`, unpacked from the trusted
/// `obeys_cmp` axiom (via the `partial_cmp` order laws + the `partial_cmp ==
/// Some(cmp)` bridge). These are the only order facts the uniqueness proof needs.
pub proof fn string_cmp_laws(a: String, b: String)
    ensures
        a.cmp_spec(&a) == core::cmp::Ordering::Equal,
        (a.cmp_spec(&b) == core::cmp::Ordering::Less)
            == (b.cmp_spec(&a) == core::cmp::Ordering::Greater),
{
    axiom_string_obeys_cmp();
    reveal(vstd::laws_cmp::obeys_cmp);
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    assert(a.partial_cmp_spec(&b) == Some(a.cmp_spec(&b)));
    assert(b.partial_cmp_spec(&a) == Some(b.cmp_spec(&a)));
    assert(a.partial_cmp_spec(&a) == Some(a.cmp_spec(&a)));
}

/// A strictly-increasing key sequence has distinct entries. The print `iter()`
/// loop's uniqueness fact (its keys are `increasing_seq`, hence a no-duplicate-key
/// enumeration for `lemma_seq_to_map_enumerates`).
pub proof fn lemma_increasing_keys_distinct(keys: Seq<String>)
    requires
        vstd::std_specs::btree::increasing_seq(keys),
    ensures
        forall|i: int, j: int| 0 <= i < j < keys.len() ==> #[trigger] keys[i] != #[trigger] keys[j],
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    assert forall|i: int, j: int| 0 <= i < j < keys.len() implies
        #[trigger] keys[i] != #[trigger] keys[j] by {
        assert(keys[i].cmp_spec(&keys[j]) == core::cmp::Ordering::Less);
        string_cmp_laws(keys[i], keys[j]);
    }
}

/// A strictly-key-increasing sequence of `(key, value)` pairs is uniquely
/// determined by its element set. Foundation of the multi-assignment Update
/// bridge (piece 1 of 5 — see plan).
pub proof fn lemma_sorted_kv_unique(
    s1: Seq<(String, Option<SExpr>)>,
    s2: Seq<(String, Option<SExpr>)>,
)
    requires
        vstd::std_specs::btree::increasing_seq(kv_keys(s1)),
        vstd::std_specs::btree::increasing_seq(kv_keys(s2)),
        s1.to_set() == s2.to_set(),
    ensures s1 == s2,
    decreases s1.len(),
{
    axiom_string_obeys_cmp();
    broadcast use vstd::seq_lib::group_seq_lib_default;
    s1.to_set_ensures();
    s2.to_set_ensures();
    assert(vstd::laws_cmp::obeys_partial_cmp_spec_properties::<String>()) by {
        reveal(vstd::laws_cmp::obeys_cmp);
    }
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    if s1.len() == 0 {
        assert(s2.len() == 0) by {
            if s2.len() > 0 {
                assert(s2.to_set().contains(s2[0]));
                assert(s1.to_set().contains(s2[0]));
                assert(s1.contains(s2[0]));
            }
        }
        assert(s1 =~= s2);
    } else {
        // s1[0] and s2[0] are both the minimum-key element; show they are equal.
        assert(s1.to_set().contains(s1[0]));
        assert(s2.to_set().contains(s1[0]));
        assert(s1.contains(s2[0])) by { assert(s2.to_set().contains(s2[0])); }
        assert(s2.contains(s1[0]));
        let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[0];
        let i = choose|i: int| 0 <= i < s1.len() && s1[i] == s2[0];
        assert(s2[j] == s1[0]);
        assert(s1[i] == s2[0]);
        string_cmp_laws(s1[0].0, s2[0].0);
        string_cmp_laws(s2[0].0, s1[0].0);
        // s1[0] and s2[0] are both minimum-key: neither j nor i can exceed 0.
        assert(j == 0) by {
            if j > 0 {
                increasing_keys_lt(s2, 0, j);          // key(s2[0]) < key(s2[j]) == key(s1[0])
                if i == 0 {
                    // s2[0] == s1[0] ⟹ key(s2[0]) == key(s1[0]) ⟹ cmp is Equal, not Less.
                } else {
                    increasing_keys_lt(s1, 0, i);       // key(s1[0]) < key(s2[0])
                    string_cmp_laws(s1[0].0, s2[0].0);  // antisym ⟹ key(s2[0]) > key(s1[0])
                }
            }
        }
        assert(s1[0] == s2[0]);
        // Peel the shared head; the tails have equal element sets.
        let t1 = s1.drop_first();
        let t2 = s2.drop_first();
        assert(vstd::std_specs::btree::increasing_seq(kv_keys(t1))) by {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
            kv_keys_index(t1);
            kv_keys_index(s1);
            assert forall|p: int, q: int| 0 <= p < q < kv_keys(t1).len()
                implies #[trigger] kv_keys(t1)[p].cmp_spec(&kv_keys(t1)[q])
                    == core::cmp::Ordering::Less by {
                increasing_keys_lt(s1, p + 1, q + 1);
                assert(t1[p] == s1[p + 1]);
                assert(t1[q] == s1[q + 1]);
            }
        }
        assert(vstd::std_specs::btree::increasing_seq(kv_keys(t2))) by {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
            kv_keys_index(t2);
            kv_keys_index(s2);
            assert forall|p: int, q: int| 0 <= p < q < kv_keys(t2).len()
                implies #[trigger] kv_keys(t2)[p].cmp_spec(&kv_keys(t2)[q])
                    == core::cmp::Ordering::Less by {
                increasing_keys_lt(s2, p + 1, q + 1);
                assert(t2[p] == s2[p + 1]);
                assert(t2[q] == s2[q + 1]);
            }
        }
        t1.to_set_ensures();
        t2.to_set_ensures();
        assert(t1.to_set() =~= t2.to_set()) by {
            assert forall|x: (String, Option<SExpr>)| t1.to_set().contains(x)
                implies t2.to_set().contains(x) by {
                assert(t1.contains(x));
                assert(s1.to_set().contains(x));
                assert(s2.to_set().contains(x));
                assert(s2.contains(x));
                // x is in the tail of s1, so x != s1[0] == s2[0] (strict keys ⟹
                // the head key is strictly below every tail key).
                let n = choose|n: int| 0 <= n < t1.len() && t1[n] == x;
                assert(t1[n] == s1[n + 1]);
                increasing_keys_lt(s1, 0, n + 1);
                string_cmp_laws(s1[0].0, s1[0].0);
                assert(x != s2[0]);
                let k = choose|k: int| 0 <= k < s2.len() && s2[k] == x;
                assert(k != 0);
                assert(t2[k - 1] == s2[k]);
                assert(t2.contains(x));
            }
            assert forall|x: (String, Option<SExpr>)| t2.to_set().contains(x)
                implies t1.to_set().contains(x) by {
                assert(t2.contains(x));
                assert(s2.to_set().contains(x));
                assert(s1.to_set().contains(x));
                assert(s1.contains(x));
                let n = choose|n: int| 0 <= n < t2.len() && t2[n] == x;
                assert(t2[n] == s2[n + 1]);
                increasing_keys_lt(s2, 0, n + 1);
                string_cmp_laws(s2[0].0, s2[0].0);
                assert(x != s1[0]);
                let k = choose|k: int| 0 <= k < s1.len() && s1[k] == x;
                assert(k != 0);
                assert(t1[k - 1] == s1[k]);
                assert(t1.contains(x));
            }
        }
        lemma_sorted_kv_unique(t1, t2);
        assert(s1 =~= seq![s1[0]] + t1);
        assert(s2 =~= seq![s2[0]] + t2);
    }
}

// -- Multi-assignment Update: order-free Map-view headline foundation ---------
//
// The roundtrip headline is stated at the SExpr-view Map level (`view_map`), which
// is order-independent: it needs no sorted normal form (so no `total_ordering` /
// `find_unique_minimal`), and no Expression-level `==` (only value *views* match).
// `lemma_view_map_insert` is what the parse side folds over as it rebuilds the map.

pub open spec fn view_opt(v: Option<ast::Expression>) -> Option<SExpr> {
    match v {
        Some(e) => Some(view_expr(e)),
        None => None,
    }
}

pub open spec fn view_map(m: vstd::map::Map<String, Option<ast::Expression>>)
    -> vstd::map::Map<String, Option<SExpr>> {
    m.map_values(|v: Option<ast::Expression>| view_opt(v))
}

pub proof fn lemma_view_map_empty()
    ensures
        view_map(vstd::map::Map::empty())
            == vstd::map::Map::<String, Option<SExpr>>::empty(),
{
    assert(view_map(vstd::map::Map::empty())
        =~= vstd::map::Map::<String, Option<SExpr>>::empty());
}

pub proof fn lemma_view_map_insert(
    m: vstd::map::Map<String, Option<ast::Expression>>,
    k: String,
    v: Option<ast::Expression>,
)
    ensures
        view_map(m.insert(k, v)) == view_map(m).insert(k, view_opt(v)),
{
    assert(view_map(m.insert(k, v)) =~= view_map(m).insert(k, view_opt(v)));
}

/// The `Map` a sorted set-list denotes: the head is inserted last (wins on
/// duplicate keys), matching the recursive `parse_set_map_exec` (parse head,
/// build the rest, then `insert` the head).
pub open spec fn seq_to_map(s: Seq<(String, Option<SExpr>)>)
    -> vstd::map::Map<String, Option<SExpr>>
    decreases s.len(),
{
    if s.len() == 0 {
        vstd::map::Map::empty()
    } else {
        seq_to_map(s.drop_first()).insert(s[0].0, s[0].1)
    }
}

/// If a sequence enumerates a finite map's entries with unique keys, the map it
/// builds is exactly that map. The glue that will close the print roundtrip:
/// `parse(print(m))` yields `seq_to_map(S)` for `S` = the (sorted, unique-key,
/// covering) `iter()` enumeration of `m`, and this lemma equates that with `m`.
pub proof fn lemma_seq_to_map_enumerates(
    s: Seq<(String, Option<SExpr>)>,
    m: vstd::map::Map<String, Option<SExpr>>,
)
    requires
        m.dom().finite(),
        forall|i: int| 0 <= i < s.len()
            ==> #[trigger] m.dom().contains(s[i].0) && m[s[i].0] == s[i].1,
        forall|k: String| m.dom().contains(k)
            ==> exists|i: int| 0 <= i < s.len() && (#[trigger] s[i]).0 == k,
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i].0 != s[j].0,
    ensures
        seq_to_map(s) == m,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(m.dom() =~= vstd::set::Set::<String>::empty()) by {
            assert forall|k: String| !m.dom().contains(k) by {
                if m.dom().contains(k) {
                    let i = choose|i: int| 0 <= i < s.len() && s[i].0 == k;
                }
            }
        }
        assert(seq_to_map(s) =~= m);
    } else {
        let head = s[0];
        let rest = s.drop_first();
        let m2 = m.remove(head.0);
        assert(m.dom().contains(head.0) && m[head.0] == head.1);
        assert forall|i: int| 0 <= i < rest.len()
            implies #[trigger] m2.dom().contains(rest[i].0) && m2[rest[i].0] == rest[i].1 by {
            assert(rest[i] == s[i + 1]);
            assert(s[0].0 != s[i + 1].0);
        }
        assert forall|k: String| m2.dom().contains(k)
            implies exists|i: int| 0 <= i < rest.len() && (#[trigger] rest[i]).0 == k by {
            assert(m.dom().contains(k));
            let j = choose|j: int| 0 <= j < s.len() && s[j].0 == k;
            assert(j != 0);
            assert(rest[j - 1] == s[j]);
        }
        assert forall|i: int, j: int| 0 <= i < j < rest.len()
            implies rest[i].0 != rest[j].0 by {
            assert(rest[i] == s[i + 1]);
            assert(rest[j] == s[j + 1]);
        }
        lemma_seq_to_map_enumerates(rest, m2);
        assert(m2.insert(head.0, head.1) =~= m);
        assert(seq_to_map(s) == seq_to_map(rest).insert(head.0, head.1));
    }
}

/// Build a one-entry `BTreeMap` with a known view.
pub fn build_one_entry_map(k: String, v: Option<ast::Expression>)
    -> (m: std::collections::BTreeMap<String, Option<ast::Expression>>)
    ensures
        m@ == vstd::map::Map::<String, Option<ast::Expression>>::empty().insert(k, v),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    proof { axiom_string_key_obeys_cmp(); }
    let mut m: std::collections::BTreeMap<String, Option<ast::Expression>> =
        std::collections::BTreeMap::new();
    m.insert(k, v);
    m
}

/// Extract the sole `(key, value)` of a one-entry `BTreeMap`. `iter().next()`
/// pops `remaining()[0]`, and for a single-entry map the `iter` spec pins that
/// pair to the map's contents. The key is cloned (`String::clone` is value-exact);
/// the value is borrowed, so no fragile `Option<Expression>` clone is needed.
pub fn extract_one_entry<'a>(
    m: &'a std::collections::BTreeMap<String, Option<ast::Expression>>,
) -> (r: (String, &'a Option<ast::Expression>))
    requires
        m@.dom().len() == 1,
    ensures
        m@.contains_key(r.0) && m@[r.0] == *r.1,
        m@ =~= vstd::map::Map::<String, Option<ast::Expression>>::empty().insert(r.0, *r.1),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    proof { axiom_string_key_obeys_cmp(); }
    let mut it = m.iter();
    let ghost rem = vstd::std_specs::iter::IteratorSpec::remaining(&it);
    proof {
        // iter() ensures (gated on key_obeys_cmp_spec::<String>(), now axiomatic).
        assert(rem.len() == m@.dom().len());
        assert(rem.len() == 1);
    }
    let first = it.next();
    match first {
        Some((k, v)) => {
            let rk = k.clone();
            proof {
                // next() popped the head: first == Some(rem[0]).
                assert(first == Some(rem[0]));
                assert(k == rem[0].0 && v == rem[0].1);
                // iter() forall at i == 0 pins this pair to the map.
                assert(m@.contains_key(*rem[0].0));
                assert(m@[*rem[0].0] == *rem[0].1);
                assert(rk == *rem[0].0);
                assert(*v == *rem[0].1);
                assert(m@.contains_key(rk));
                assert(m@[rk] == *v);
                assert(m@.dom() =~= set![rk]);
                assert(m@ =~= vstd::map::Map::<String, Option<ast::Expression>>::empty()
                    .insert(rk, *v));
            }
            (rk, v)
        },
        None => {
            proof {
                // rem.len() == 1 > 0, so next() returns Some — this arm is dead.
                assert(false);
            }
            vstd::pervasive::unreached()
        },
    }
}

// -- Select FROM join-tree exec parser ---------------------------------------

pub fn parse_table_exec(toks: &Vec<super::Token>, pos: usize) -> (r: (Option<ast::From>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_table(input);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(t) => sopt is Some && view_from(t) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    match &toks[pos] {
        super::Token::Ident(name) => {
            if pos + 1 < toks.len() && pos + 2 < toks.len()
                && matches!(toks[pos + 1], super::Token::Keyword(Keyword::As)) {
                proof {
                    token_views_suffix(toks@, pos as int + 1);
                    token_views_suffix(toks@, pos as int + 2);
                }
                match &toks[pos + 2] {
                    super::Token::Ident(alias) => (
                        Some(ast::From::Table { name: name.clone(), alias: Some(alias.clone()) }),
                        pos + 3,
                    ),
                    _ => (None, pos),
                }
            } else {
                if pos + 1 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 1); }
                    if pos + 2 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 2); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                    }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                }
                (Some(ast::From::Table { name: name.clone(), alias: None }), pos + 1)
            }
        },
        _ => (None, pos),
    }
}

#[verifier::rlimit(15000)]
pub fn parse_step_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<(ast::JoinType, ast::From, Option<ast::Expression>)>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_step(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some((jt, right, pred)) => sopt is Some
                    && sopt.unwrap() == (SJoinStep {
                        join_type: jt,
                        right: view_from(right),
                        predicate: match pred { Some(e) => Some(view_expr(e)), None => None },
                    })
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len()
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Join)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
        }
        let jt = match &toks[pos] {
            super::Token::Keyword(Keyword::Cross) => Some(ast::JoinType::Cross),
            super::Token::Keyword(Keyword::Inner) => Some(ast::JoinType::Inner),
            super::Token::Keyword(Keyword::Left) => Some(ast::JoinType::Left),
            super::Token::Keyword(Keyword::Right) => Some(ast::JoinType::Right),
            _ => None,
        };
        match jt {
            Some(jt) => {
                let (ropt, rpos) = parse_table_exec(toks, pos + 2);
                match ropt {
                    Some(right) => match jt {
                        ast::JoinType::Cross => (Some((jt, right, None)), rpos),
                        _ => {
                            if rpos < toks.len() && matches!(toks[rpos], super::Token::Keyword(Keyword::On)) {
                                proof { token_views_suffix(toks@, rpos as int); }
                                let (eopt, epos) = parse_expr_exec(toks, rpos + 1, fuel);
                                match eopt {
                                    Some(e) => (Some((jt, right, Some(e))), epos),
                                    None => (None, pos),
                                }
                            } else {
                                if rpos < toks.len() {
                                    proof { token_views_suffix(toks@, rpos as int); }
                                } else {
                                    proof { token_views_len(toks@.subrange(rpos as int, toks@.len() as int)); }
                                }
                                (None, pos)
                            }
                        },
                    },
                    None => (None, pos),
                }
            },
            None => (None, pos),
        }
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
            if pos + 1 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 1); }
            } else {
                proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
            }
        }
        (None, pos)
    }
}

#[verifier::rlimit(20000)]
pub fn parse_steps_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize, acc: ast::From)
    -> (r: (Option<ast::From>, usize))
    requires pos <= toks.len(),
    ensures ({
        let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_steps(rem, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(built) => sopt is Some
                    && view_from(built) == fold_joins(view_from(acc), sopt.unwrap())
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_steps, 1);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    let is_join = pos < toks.len() && matches!(&toks[pos],
        super::Token::Keyword(Keyword::Cross) | super::Token::Keyword(Keyword::Inner)
        | super::Token::Keyword(Keyword::Left) | super::Token::Keyword(Keyword::Right));
    if pos < toks.len() {
        proof { token_views_suffix(toks@, pos as int); }
    }
    if is_join {
        if fuel == 0 {
            (None, pos)
        } else {
            let (stepopt, spos) = parse_step_exec(toks, pos, fuel);
            match stepopt {
                Some((jt, right, pred)) => {
                    let acc2 = ast::From::Join {
                        left: Box::new(acc),
                        right: Box::new(right),
                        join_type: jt,
                        predicate: pred,
                    };
                    let (moreopt, mpos) = parse_steps_exec(toks, spos, fuel - 1, acc2);
                    match moreopt {
                        Some(built) => {
                            proof {
                                reveal_with_fuel(fold_joins, 1);
                                let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
                                let step_m = sparse_step(rem, fuel as nat).0.unwrap();
                                let more_m = sparse_steps(
                                    token_views(toks@.subrange(spos as int, toks@.len() as int)),
                                    (fuel - 1) as nat).0.unwrap();
                                assert(view_from(acc2) == apply_step(view_from(acc), step_m));
                                assert(sparse_steps(rem, fuel as nat).0.unwrap() =~= seq![step_m] + more_m);
                                assert((seq![step_m] + more_m)[0] == step_m);
                                assert((seq![step_m] + more_m).drop_first() =~= more_m);
                            }
                            (Some(built), mpos)
                        },
                        None => (None, pos),
                    }
                },
                None => (None, pos),
            }
        }
    } else {
        (Some(acc), pos)
    }
}

#[verifier::rlimit(15000)]
pub fn parse_from_item_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::From>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_from(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(f) => sopt is Some && view_from(f) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_from);
    let (hopt, hpos) = parse_table_exec(toks, pos);
    match hopt {
        Some(head) => {
            let (fopt, fpos) = parse_steps_exec(toks, hpos, fuel, head);
            match fopt {
                Some(folded) => (Some(folded), fpos),
                None => (None, pos),
            }
        },
        None => (None, pos),
    }
}

#[verifier::rlimit(20000)]
pub fn parse_from_list_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<ast::From>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_from_list(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(vv) => sopt is Some && view_froms(vv@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_from_list, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    let (fopt, fpos) = parse_from_item_exec(toks, pos, fuel);
    match fopt {
        Some(f) => {
            if fpos < toks.len() && matches!(toks[fpos], super::Token::Comma) {
                proof { token_views_suffix(toks@, fpos as int); }
                let (mopt, mpos) = parse_from_list_exec(toks, fpos + 1, fuel - 1);
                match mopt {
                    Some(mut more) => {
                        let mut v: Vec<ast::From> = Vec::new();
                        v.push(f);
                        let ghost first = v@;
                        let ghost more_old = more@;
                        v.append(&mut more);
                        proof {
                            assert(v@ =~= first + more_old);
                            view_froms_step(v@);
                            assert(v@.drop_first() =~= more_old);
                        }
                        (Some(v), mpos)
                    },
                    None => (None, pos),
                }
            } else {
                if fpos < toks.len() {
                    proof { token_views_suffix(toks@, fpos as int); }
                } else {
                    proof { token_views_len(toks@.subrange(fpos as int, toks@.len() as int)); }
                }
                let mut v: Vec<ast::From> = Vec::new();
                v.push(f);
                proof {
                    view_froms_step(v@);
                    assert(v@.drop_first() =~= Seq::<ast::From>::empty());
                }
                (Some(v), fpos)
            }
        },
        None => (None, pos),
    }
}

#[verifier::rlimit(15000)]
pub fn parse_select_item_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<(ast::Expression, Option<String>)>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_select_item(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some((e, alias)) => sopt is Some && sopt.unwrap() == (view_expr(e), alias)
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_select_item);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    let (eopt, epos) = parse_expr_exec(toks, pos, fuel);
    match eopt {
        Some(e) => {
            proof { token_views_len(toks@.subrange(epos as int, toks@.len() as int)); }
            if epos < toks.len() && epos + 1 < toks.len()
                && matches!(toks[epos], super::Token::Keyword(Keyword::As)) {
                proof {
                    token_views_suffix(toks@, epos as int);
                    token_views_suffix(toks@, epos as int + 1);
                }
                match &toks[epos + 1] {
                    super::Token::Ident(a) => (Some((e, Some(a.clone()))), epos + 2),
                    _ => (None, pos),
                }
            } else {
                if epos < toks.len() {
                    proof { token_views_suffix(toks@, epos as int); }
                    if epos + 1 < toks.len() {
                        proof { token_views_suffix(toks@, epos as int + 1); }
                    } else {
                        proof { token_views_len(toks@.subrange(epos as int + 1, toks@.len() as int)); }
                    }
                } else {
                    proof { token_views_len(toks@.subrange(epos as int, toks@.len() as int)); }
                }
                (Some((e, None)), epos)
            }
        },
        None => (None, pos),
    }
}

#[verifier::rlimit(20000)]
pub fn parse_select_list_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<(ast::Expression, Option<String>)>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_select_list(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(vv) => sopt is Some && view_select_list(vv@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_select_list, 1);
    if fuel == 0 {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    let (iopt, ipos) = parse_select_item_exec(toks, pos, fuel);
    match iopt {
        Some(item) => {
            proof { token_views_len(toks@.subrange(ipos as int, toks@.len() as int)); }
            if ipos < toks.len() && matches!(toks[ipos], super::Token::Comma) {
                proof { token_views_suffix(toks@, ipos as int); }
                let (mopt, mpos) = parse_select_list_exec(toks, ipos + 1, fuel - 1);
                match mopt {
                    Some(mut more) => {
                        let mut v: Vec<(ast::Expression, Option<String>)> = Vec::new();
                        v.push(item);
                        let ghost first = v@;
                        let ghost more_old = more@;
                        v.append(&mut more);
                        proof {
                            assert(v@ =~= first + more_old);
                            view_select_list_step(v@);
                            assert(v@.drop_first() =~= more_old);
                        }
                        (Some(v), mpos)
                    },
                    None => (None, pos),
                }
            } else {
                if ipos < toks.len() {
                    proof { token_views_suffix(toks@, ipos as int); }
                }
                let mut v: Vec<(ast::Expression, Option<String>)> = Vec::new();
                v.push(item);
                proof {
                    view_select_list_step(v@);
                    assert(v@.drop_first() =~= Seq::<(ast::Expression, Option<String>)>::empty());
                }
                (Some(v), ipos)
            }
        },
        None => (None, pos),
    }
}

/// Executable parser for a boundary-terminated bare-expr comma-list, refining
/// the opaque `sparse_expr_list` (the GROUP BY item list).
pub fn parse_expr_list_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<ast::Expression>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_expr_list(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(v) => sopt is Some && view_args(v@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal(sparse_expr_list);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if fuel == 0 {
        return (None, pos);
    }
    let (eopt, epos) = parse_expr_exec(toks, pos, fuel);
    match eopt {
        Some(e) => {
            proof { token_views_len(toks@.subrange(epos as int, toks@.len() as int)); }
            if epos < toks.len() && matches!(toks[epos], super::Token::Comma) {
                proof { token_views_suffix(toks@, epos as int); }
                let (more_opt, mpos) = parse_expr_list_exec(toks, epos + 1, fuel - 1);
                match more_opt {
                    Some(mut more) => {
                        let ghost more_snap = more@;
                        let mut v: Vec<ast::Expression> = Vec::new();
                        v.push(e);
                        v.append(&mut more);
                        proof {
                            assert(v@ =~= seq![e] + more_snap);
                            assert(v@.drop_first() =~= more_snap);
                            assert(view_args(v@) =~= seq![view_expr(e)] + view_args(more_snap));
                        }
                        (Some(v), mpos)
                    },
                    None => (None, pos),
                }
            } else {
                if epos < toks.len() {
                    proof { token_views_suffix(toks@, epos as int); }
                }
                let mut v: Vec<ast::Expression> = Vec::new();
                v.push(e);
                proof {
                    assert(v@ =~= seq![e]);
                    assert(v@.len() == 1);
                    assert(v@[0] == e);
                    assert(v@.drop_first() =~= Seq::<ast::Expression>::empty());
                    assert(view_args(v@.drop_first()) =~= Seq::<SExpr>::empty());
                    assert(view_args(v@) =~= seq![view_expr(v@[0])] + view_args(v@.drop_first()));
                    assert(view_args(v@) =~= seq![view_expr(e)]);
                }
                (Some(v), epos)
            }
        },
        None => (None, pos),
    }
}

/// Executable parser for the `[WHERE e] [GROUP BY exprs] [HAVING e]` tail,
/// refining the opaque `sparse_where_group`.
#[verifier::rlimit(30000)]
pub fn parse_where_group_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<(Option<ast::Expression>, Vec<ast::Expression>, Option<ast::Expression>)>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_where_group(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some((wc, gb, hv)) => sopt is Some
                    && (match wc { Some(e) => Some(view_expr(e)), None => None::<SExpr> },
                        view_args(gb@),
                        match hv { Some(e) => Some(view_expr(e)), None => None::<SExpr> })
                        == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_where_group);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    let where_clause: Option<ast::Expression>;
    let rwpos: usize;
    if pos < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::Where)) {
        proof { token_views_suffix(toks@, pos as int); }
        let (eopt, epos) = parse_expr_exec(toks, pos + 1, fuel);
        match eopt {
            Some(e) => { where_clause = Some(e); rwpos = epos; },
            None => { return (None, pos); },
        }
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
        }
        where_clause = None;
        rwpos = pos;
    }
    // GROUP BY -> (group_by, rgpos)
    let group_by: Vec<ast::Expression>;
    let rgpos: usize;
    proof { token_views_len(toks@.subrange(rwpos as int, toks@.len() as int)); }
    if rwpos < toks.len() && rwpos + 1 < toks.len()
        && matches!(toks[rwpos], super::Token::Keyword(Keyword::Group))
        && matches!(toks[rwpos + 1], super::Token::Keyword(Keyword::By)) {
        proof {
            token_views_suffix(toks@, rwpos as int);
            token_views_suffix(toks@, rwpos as int + 1);
            token_views_len(toks@.subrange(rwpos as int + 2, toks@.len() as int));
        }
        let (gopt, gpos) = parse_expr_list_exec(toks, rwpos + 2, fuel);
        match gopt {
            Some(gb) => { group_by = gb; rgpos = gpos; },
            None => { return (None, pos); },
        }
    } else {
        proof {
            if rwpos < toks.len() { token_views_suffix(toks@, rwpos as int); }
            if (rwpos as int) + 1 < toks@.len() { token_views_suffix(toks@, rwpos as int + 1); }
        }
        group_by = Vec::new();
        proof { assert(view_args(group_by@) =~= Seq::<SExpr>::empty()); }
        rgpos = rwpos;
    }
    // HAVING
    proof { token_views_len(toks@.subrange(rgpos as int, toks@.len() as int)); }
    if rgpos < toks.len() && matches!(toks[rgpos], super::Token::Keyword(Keyword::Having)) {
        proof { token_views_suffix(toks@, rgpos as int); }
        let (hopt, hpos) = parse_expr_exec(toks, rgpos + 1, fuel);
        match hopt {
            Some(he) => (Some((where_clause, group_by, Some(he))), hpos),
            None => (None, pos),
        }
    } else {
        if rgpos < toks.len() {
            proof { token_views_suffix(toks@, rgpos as int); }
        }
        (Some((where_clause, group_by, None)), rgpos)
    }
}

/// Executable parser for the `[LIMIT e] [OFFSET e]` tail, refining the opaque
/// `sparse_limit_offset` (kept 2-clause so its `reveal` stays tractable).
pub fn parse_limit_offset_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<(Option<ast::Expression>, Option<ast::Expression>)>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_limit_offset(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some((lm, of)) => sopt is Some
                    && (match lm { Some(e) => Some(view_expr(e)), None => None::<SExpr> },
                        match of { Some(e) => Some(view_expr(e)), None => None::<SExpr> })
                        == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_limit_offset);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    let limit: Option<ast::Expression>;
    let rlpos: usize;
    if pos < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::Limit)) {
        proof { token_views_suffix(toks@, pos as int); }
        let (lopt, lpos) = parse_expr_exec(toks, pos + 1, fuel);
        match lopt {
            Some(le) => { limit = Some(le); rlpos = lpos; },
            None => { return (None, pos); },
        }
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
        }
        limit = None;
        rlpos = pos;
    }
    proof { token_views_len(toks@.subrange(rlpos as int, toks@.len() as int)); }
    if rlpos < toks.len() && matches!(toks[rlpos], super::Token::Keyword(Keyword::Offset)) {
        proof { token_views_suffix(toks@, rlpos as int); }
        let (oopt, opos) = parse_expr_exec(toks, rlpos + 1, fuel);
        match oopt {
            Some(oe) => (Some((limit, Some(oe))), opos),
            None => (None, pos),
        }
    } else {
        if rlpos < toks.len() {
            proof { token_views_suffix(toks@, rlpos as int); }
        }
        (Some((limit, None)), rlpos)
    }
}

/// Executable parser for the ORDER BY item list (expr + mandatory ASC/DESC),
/// refining the opaque `sparse_order_list`.
pub fn parse_order_list_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<(ast::Expression, ast::Direction)>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_order_list(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(v) => sopt is Some && view_order_list(v@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal(sparse_order_list);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if fuel == 0 {
        return (None, pos);
    }
    let (eopt, epos) = parse_expr_exec(toks, pos, fuel);
    match eopt {
        Some(e) => {
            proof { token_views_len(toks@.subrange(epos as int, toks@.len() as int)); }
            if epos < toks.len() && (matches!(toks[epos], super::Token::Keyword(Keyword::Asc))
                || matches!(toks[epos], super::Token::Keyword(Keyword::Desc))) {
                let dir: ast::Direction =
                    if matches!(toks[epos], super::Token::Keyword(Keyword::Asc)) {
                        ast::Direction::Ascending
                    } else {
                        ast::Direction::Descending
                    };
                proof { token_views_suffix(toks@, epos as int); }
                let dpos = epos + 1;
                proof { token_views_len(toks@.subrange(dpos as int, toks@.len() as int)); }
                if dpos < toks.len() && matches!(toks[dpos], super::Token::Comma) {
                    proof { token_views_suffix(toks@, dpos as int); }
                    let (more_opt, mpos) = parse_order_list_exec(toks, dpos + 1, fuel - 1);
                    match more_opt {
                        Some(mut more) => {
                            let ghost more_snap = more@;
                            let mut v: Vec<(ast::Expression, ast::Direction)> = Vec::new();
                            v.push((e, dir));
                            v.append(&mut more);
                            proof {
                                assert(v@ =~= seq![(e, dir)] + more_snap);
                                assert(v@[0].0 == e);
                                assert(v@[0].1 == dir);
                                assert(v@.drop_first() =~= more_snap);
                                assert(view_order_list(v@)
                                    =~= seq![(view_expr(e), dir)] + view_order_list(more_snap));
                            }
                            (Some(v), mpos)
                        },
                        None => (None, pos),
                    }
                } else {
                    if dpos < toks.len() {
                        proof { token_views_suffix(toks@, dpos as int); }
                    }
                    let mut v: Vec<(ast::Expression, ast::Direction)> = Vec::new();
                    v.push((e, dir));
                    proof {
                        assert(v@ =~= seq![(e, dir)]);
                        assert(v@[0].0 == e);
                        assert(v@[0].1 == dir);
                        assert(v@.drop_first() =~= Seq::<(ast::Expression, ast::Direction)>::empty());
                        assert(view_order_list(v@.drop_first())
                            =~= Seq::<(SExpr, ast::Direction)>::empty());
                        assert(view_order_list(v@) =~= seq![(view_expr(e), dir)]);
                    }
                    (Some(v), dpos)
                }
            } else {
                if epos < toks.len() {
                    proof { token_views_suffix(toks@, epos as int); }
                }
                (None, pos)
            }
        },
        None => (None, pos),
    }
}

/// Executable parser for the optional `ORDER BY <items>` clause, refining the
/// opaque `sparse_order_clause`.
pub fn parse_order_clause_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<(ast::Expression, ast::Direction)>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_order_clause(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(v) => sopt is Some && view_order_list(v@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_order_clause);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len()
        && matches!(toks[pos], super::Token::Keyword(Keyword::Order))
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::By)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
            token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int));
        }
        let (vopt, vpos) = parse_order_list_exec(toks, pos + 2, fuel);
        match vopt {
            Some(v) => (Some(v), vpos),
            None => (None, pos),
        }
    } else {
        proof {
            if pos < toks.len() { token_views_suffix(toks@, pos as int); }
            if (pos as int) + 1 < toks@.len() { token_views_suffix(toks@, pos as int + 1); }
        }
        let v: Vec<(ast::Expression, ast::Direction)> = Vec::new();
        proof { assert(view_order_list(v@) =~= Seq::<(SExpr, ast::Direction)>::empty()); }
        (Some(v), pos)
    }
}

#[verifier::rlimit(30000)]
pub fn parse_select_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos < toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_select(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof {
        token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        token_views_suffix(toks@, pos as int);
    }
    let (slopt, r1pos) = parse_select_list_exec(toks, pos + 1, fuel);
    match slopt {
        Some(select) => {
            proof { token_views_len(toks@.subrange(r1pos as int, toks@.len() as int)); }
            let from: Vec<ast::From>;
            let r2pos: usize;
            if r1pos < toks.len() && matches!(toks[r1pos], super::Token::Keyword(Keyword::From)) {
                proof { token_views_suffix(toks@, r1pos as int); }
                let (fopt, fpos) = parse_from_list_exec(toks, r1pos + 1, fuel);
                match fopt {
                    Some(fv) => { from = fv; r2pos = fpos; },
                    None => { return (None, pos); },
                }
            } else {
                if r1pos < toks.len() {
                    proof { token_views_suffix(toks@, r1pos as int); }
                }
                from = Vec::new();
                proof { assert(view_froms(from@) =~= Seq::<SFrom>::empty()); }
                r2pos = r1pos;
            }
            proof { token_views_len(toks@.subrange(r2pos as int, toks@.len() as int)); }
            let (wgopt, wgpos) = parse_where_group_exec(toks, r2pos, fuel);
            match wgopt {
                Some((wc, gb, hv)) => {
                    proof { token_views_len(toks@.subrange(wgpos as int, toks@.len() as int)); }
                    let (ordopt, ordpos) = parse_order_clause_exec(toks, wgpos, fuel);
                    match ordopt {
                        Some(order_by) => {
                            proof { token_views_len(toks@.subrange(ordpos as int, toks@.len() as int)); }
                            let (loopt, lopos) = parse_limit_offset_exec(toks, ordpos, fuel);
                            match loopt {
                                Some((lm, of)) => (
                                    Some(ast::Statement::Select {
                                        select, from, where_clause: wc,
                                        group_by: gb, having: hv,
                                        order_by, limit: lm, offset: of,
                                    }),
                                    lopos,
                                ),
                                None => (None, pos),
                            }
                        },
                        None => (None, pos),
                    }
                },
                None => (None, pos),
            }
        },
        None => (None, pos),
    }
}

// ==== Update executable layer (S5, 10th kind; single-assignment) ============
//
// `view_stmt` only bridges single-assignment `Update`s (a `BTreeMap` whose spec
// view is an unordered `Map` cannot be sorted by a pure `spec fn`). The executable
// layer therefore covers exactly that case, using the trusted `String` cmp axiom
// to build/read the one-entry map (`build_one_entry_map` / `extract_one_entry`).

pub open spec fn is_supdate(s: SStmt) -> bool {
    match s {
        SStmt::Update { .. } => true,
        _ => false,
    }
}

/// `sprint_assign` re-expressed by matching the value `o` directly (rather than
/// through `view_opt`), so an exec printer that matches `&Option` and the spec use
/// the same binding. Bridges `print_assign_exec`'s ensures to the `sprint_assign`
/// / `sprint_set_list` world.
pub proof fn lemma_sprint_assign_view(k: String, o: Option<ast::Expression>)
    ensures
        sprint_assign((k, view_opt(o))) == seq![TokenView::Ident(k), TokenView::Equal]
            + (match o {
                Some(e) => sprint(view_expr(e)),
                None => seq![TokenView::Keyword(Keyword::Default)],
            }),
{
    match o {
        Some(e) => {
            assert(view_opt(o) == Some(view_expr(e)));
            assert(sprint_assign((k, view_opt(o)))
                =~= seq![TokenView::Ident(k), TokenView::Equal] + sprint(view_expr(e)));
        },
        None => {
            assert(view_opt(o) == None::<SExpr>);
            assert(sprint_assign((k, view_opt(o)))
                =~= seq![TokenView::Ident(k), TokenView::Equal]
                    + seq![TokenView::Keyword(Keyword::Default)]);
        },
    }
}

/// Print one `k = v` assignment, borrowing the value (no clone). The ensures is
/// phrased with the `match v` binding — like `print_select_head_exec`'s WHERE arm —
/// so the exec and spec matches align with no reference-payload relating needed;
/// `lemma_sprint_assign_view` bridges it to `sprint_assign`. Body of the print loop.
pub fn print_assign_exec(k: &String, v: &Option<ast::Expression>) -> (r: Vec<super::Token>)
    requires
        match v { Some(e) => printable_se(view_expr(*e)), None => true },
    ensures
        token_views(r@) == seq![TokenView::Ident(*k), TokenView::Equal]
            + (match v {
                Some(e) => sprint(view_expr(*e)),
                None => seq![TokenView::Keyword(Keyword::Default)],
            }),
{
    reveal_with_fuel(token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(super::Token::Ident(k.clone()));
    r.push(super::Token::Equal);
    let ghost head = r@;
    proof {
        assert(token_views(head) =~= seq![TokenView::Ident(*k), TokenView::Equal]);
    }
    match v {
        Some(e) => {
            let mut eb = print_expr_exec(e);
            let ghost ebo = eb@;
            r.append(&mut eb);
            proof {
                token_views_concat(head, ebo);
                assert(token_views(r@)
                    =~= seq![TokenView::Ident(*k), TokenView::Equal] + sprint(view_expr(*e)));
            }
        },
        None => {
            r.push(super::Token::Keyword(Keyword::Default));
            proof {
                assert(r@ =~= head + seq![super::Token::Keyword(Keyword::Default)]);
                token_views_concat(head, seq![super::Token::Keyword(Keyword::Default)]);
                assert(token_views(seq![super::Token::Keyword(Keyword::Default)])
                    =~= seq![TokenView::Keyword(Keyword::Default)]);
                assert(token_views(head) =~= seq![TokenView::Ident(*k), TokenView::Equal]);
                assert(token_views(r@)
                    =~= seq![TokenView::Ident(*k), TokenView::Equal]
                        + seq![TokenView::Keyword(Keyword::Default)]);
            }
        },
    }
    r
}

/// Executable printer for a single-assignment `UPDATE`. Mirrors `print_select_exec`:
/// build the token vector incrementally, discharging `token_views` by concatenation.
pub fn print_update_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires printable_stmt(view_stmt(*s)), is_supdate(view_stmt(*s)),
    ensures token_views(r@) == sprint_stmt(view_stmt(*s)),
{
    reveal(printable_stmt);
    reveal_with_fuel(token_views, 4);
    match s {
        ast::Statement::Update { table, set, where_clause } => {
            proof {
                // is_supdate(view_stmt(s)) rules out the multi/empty branch.
                assert(set@.dom().len() == 1);
            }
            let ghost m = view_stmt(*s);
            let ghost k0 = set@.dom().choose();
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Update));
            r.push(super::Token::Ident(table.clone()));
            r.push(super::Token::Keyword(Keyword::Set));
            proof {
                assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                assert(token_views(r@) =~= seq![
                    TokenView::Keyword(Keyword::Update),
                    TokenView::Ident(*table),
                    TokenView::Keyword(Keyword::Set),
                ]);
            }
            let ghost head = r@;
            let (rk, rv) = extract_one_entry(set);
            proof {
                // singleton domain: the chosen key is rk.
                assert(set@.dom() =~= set![rk]);
                assert(k0 == rk);
            }
            r.push(super::Token::Ident(rk));
            r.push(super::Token::Equal);
            proof {
                assert(r@ =~= head + seq![super::Token::Ident(rk), super::Token::Equal]);
                token_views_concat(head, seq![super::Token::Ident(rk), super::Token::Equal]);
                assert(token_views(seq![super::Token::Ident(rk), super::Token::Equal])
                    =~= seq![TokenView::Ident(rk), TokenView::Equal]) by {
                    reveal_with_fuel(token_views, 3);
                }
                assert(k0 == rk);
                assert(set@[rk] == *rv);
            }
            let ghost kv_head = r@;
            let ghost head_set = seq![
                TokenView::Keyword(Keyword::Update),
                TokenView::Ident(*table),
                TokenView::Keyword(Keyword::Set),
            ] + sprint_set_list(m->Update_set);
            proof {
                // token_views(kv_head) == head_views ++ [Ident(rk), Equal]
                assert(token_views(kv_head) =~= seq![
                    TokenView::Keyword(Keyword::Update),
                    TokenView::Ident(*table),
                    TokenView::Keyword(Keyword::Set),
                    TokenView::Ident(rk),
                    TokenView::Equal,
                ]);
            }
            // value: expression, tried first in the mirror, else DEFAULT keyword.
            match rv {
                Some(e) => {
                    let mut vb = print_expr_exec(e);
                    let ghost vbo = vb@;
                    r.append(&mut vb);
                    proof {
                        token_views_concat(kv_head, vbo);
                        // set@[rk] == Some(*e); m.set == seq![(rk, Some(view_expr(*e)))]
                        assert(m->Update_set =~= seq![(rk, Some(view_expr(*e)))]);
                        assert(sprint_set_list(m->Update_set)
                            =~= seq![TokenView::Ident(rk), TokenView::Equal] + sprint(view_expr(*e)));
                        assert(token_views(r@) =~= head_set);
                    }
                },
                None => {
                    r.push(super::Token::Keyword(Keyword::Default));
                    proof {
                        assert(r@ =~= kv_head + seq![super::Token::Keyword(Keyword::Default)]);
                        token_views_concat(kv_head, seq![super::Token::Keyword(Keyword::Default)]);
                        assert(token_views(seq![super::Token::Keyword(Keyword::Default)])
                            =~= seq![TokenView::Keyword(Keyword::Default)]);
                        assert(m->Update_set =~= seq![(rk, None::<SExpr>)]);
                        assert(sprint_set_list(m->Update_set) =~= seq![
                            TokenView::Ident(rk),
                            TokenView::Equal,
                            TokenView::Keyword(Keyword::Default),
                        ]);
                        assert(token_views(r@) =~= head_set);
                    }
                },
            }
            let ghost after_val = r@;
            proof { assert(token_views(after_val) =~= head_set); }
            match where_clause {
                Some(e) => {
                    r.push(super::Token::Keyword(Keyword::Where));
                    let ghost wk = r@;
                    let mut wb = print_expr_exec(e);
                    let ghost wbo = wb@;
                    r.append(&mut wb);
                    proof {
                        token_views_concat(wk, wbo);
                        token_views_concat(after_val, seq![super::Token::Keyword(Keyword::Where)]);
                        assert(wk =~= after_val + seq![super::Token::Keyword(Keyword::Where)]);
                        assert(token_views(r@)
                            =~= head_set + (seq![TokenView::Keyword(Keyword::Where)] + sprint(view_expr(*e))));
                        assert(token_views(r@) =~= sprint_stmt(m));
                    }
                },
                None => {
                    proof { assert(token_views(r@) =~= sprint_stmt(m)); }
                },
            }
            r
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

/// Executable parser for `k = expr` or `k = DEFAULT`, refining `sparse_assign`.
pub fn parse_assign_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<(String, Option<ast::Expression>)>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_assign(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some((k, ve)) => sopt is Some
                    && (k, match ve { Some(e) => Some(view_expr(e)), None => None::<SExpr> })
                        == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    reveal(sparse_assign);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        // input is empty (pos == toks.len()); sparse_assign needs len >= 2.
        return (None, pos);
    }
    if pos + 1 < toks.len() && matches!(toks[pos + 1], super::Token::Equal) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
        }
        match &toks[pos] {
            super::Token::Ident(k) => {
                // rest = input.drop_first().drop_first() == subrange(pos+2)
                let ghost rest = token_views(toks@.subrange(pos as int + 2, toks@.len() as int));
                proof {
                    token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int));
                    assert(input.len() >= 2);
                    assert(input[0] == TokenView::Ident(*k));
                    assert(input[1] == TokenView::Equal);
                    assert(input.drop_first().drop_first() =~= rest);
                }
                let (eopt, epos) = parse_expr_exec(toks, pos + 2, fuel);
                match eopt {
                    Some(e) => {
                        proof { assert(sparse(rest, fuel as nat).0 is Some); }
                        (Some((k.clone(), Some(e))), epos)
                    },
                    None => {
                        proof { assert(sparse(rest, fuel as nat).0 is None); }
                        if pos + 2 < toks.len()
                            && matches!(toks[pos + 2], super::Token::Keyword(Keyword::Default)) {
                            proof {
                                token_views_suffix(toks@, pos as int + 2);
                                assert(rest.len() >= 1 && rest[0] == TokenView::Keyword(Keyword::Default));
                                assert(rest.drop_first()
                                    =~= token_views(toks@.subrange(pos as int + 3, toks@.len() as int)));
                            }
                            (Some((k.clone(), None)), pos + 3)
                        } else {
                            proof {
                                if (pos as int) + 2 < toks@.len() {
                                    token_views_suffix(toks@, pos as int + 2);
                                }
                                assert(rest.len() == 0
                                    || rest[0] != TokenView::Keyword(Keyword::Default));
                            }
                            (None, pos)
                        }
                    },
                }
            },
            _ => {
                // input[0] is not an Ident, so sparse_assign's inner match fails.
                proof { token_views_suffix(toks@, pos as int); }
                (None, pos)
            },
        }
    } else {
        // Either input.len() < 2 or input[1] != Equal.
        proof {
            if (pos as int) + 1 < toks@.len() {
                token_views_suffix(toks@, pos as int);
                token_views_suffix(toks@, pos as int + 1);
            }
        }
        (None, pos)
    }
}

/// A successful `sparse_set_list` parse yields at least one assignment.
pub proof fn lemma_sparse_set_list_len(input: Seq<TokenView>, fuel: nat)
    ensures
        sparse_set_list(input, fuel).0 is Some ==> sparse_set_list(input, fuel).0.unwrap().len() >= 1,
    decreases fuel,
{
    reveal_with_fuel(sparse_set_list, 1);
    if fuel == 0 {
    } else {
        match sparse_assign(input, fuel) {
            (Some(a), r) => {
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    lemma_sparse_set_list_len(r.drop_first(), (fuel - 1) as nat);
                } else {
                    assert(sparse_set_list(input, fuel) == (Some(seq![a]), r));
                }
            },
            (None, _) => {},
        }
    }
}

/// Multi-assignment set-list parser that builds the `BTreeMap` directly, refining
/// `sparse_set_list` at the order-free `view_map` level (piece 4 of the multi-Update
/// plan). Parses `k = v, k = v, ...` and folds `insert`, moving each parsed value
/// (never cloning — `Option<Expression>::clone` is not value-exact). The head is
/// parsed first and inserted last, matching `seq_to_map`.
#[verifier::rlimit(40000)]
pub fn parse_set_map_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<std::collections::BTreeMap<String, Option<ast::Expression>>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_set_list(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(m) => sopt is Some && view_map(m@) == seq_to_map(sopt.unwrap())
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    proof { axiom_string_key_obeys_cmp(); }
    reveal(sparse_set_list);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if fuel == 0 {
        return (None, pos);
    }
    let (aopt, apos) = parse_assign_exec(toks, pos, fuel);
    match aopt {
        Some((k, ve)) => {
            let ghost gk = k;
            let ghost gve = ve;
            let ghost a = (gk, view_opt(gve));
            proof { token_views_len(toks@.subrange(apos as int, toks@.len() as int)); }
            if apos < toks.len() && matches!(toks[apos], super::Token::Comma) {
                proof { token_views_suffix(toks@, apos as int); }
                let (mopt, mpos) = parse_set_map_exec(toks, apos + 1, fuel - 1);
                match mopt {
                    Some(mut m) => {
                        let ghost old_m = m@;
                        m.insert(k, ve);
                        proof {
                            let more = sparse_set_list(
                                token_views(toks@.subrange(apos as int + 1, toks@.len() as int)),
                                (fuel - 1) as nat,
                            ).0.unwrap();
                            // recursion ensures: view_map(old_m) == seq_to_map(more)
                            assert(view_map(old_m) == seq_to_map(more));
                            // BTreeMap insert view + view_map distribution
                            assert(m@ == old_m.insert(gk, gve));
                            lemma_view_map_insert(old_m, gk, gve);
                            assert(view_map(m@) == seq_to_map(more).insert(gk, view_opt(gve)));
                            // seq_to_map unfolds on the head a == (gk, view_opt(gve))
                            assert((seq![a] + more)[0] == a);
                            assert((seq![a] + more).drop_first() =~= more);
                            assert(seq_to_map(seq![a] + more)
                                == seq_to_map(more).insert(a.0, a.1));
                            assert(view_map(m@) == seq_to_map(seq![a] + more));
                        }
                        (Some(m), mpos)
                    },
                    None => (None, pos),
                }
            } else {
                if apos < toks.len() {
                    proof { token_views_suffix(toks@, apos as int); }
                }
                let mut m: std::collections::BTreeMap<String, Option<ast::Expression>> =
                    std::collections::BTreeMap::new();
                let ghost old_m = m@;
                m.insert(k, ve);
                proof {
                    assert(old_m == vstd::map::Map::<String, Option<ast::Expression>>::empty());
                    assert(m@ == old_m.insert(gk, gve));
                    lemma_view_map_empty();
                    lemma_view_map_insert(old_m, gk, gve);
                    assert(view_map(m@) == view_map(old_m).insert(gk, view_opt(gve)));
                    assert(seq![a][0] == a);
                    assert(seq![a].drop_first() =~= Seq::<(String, Option<SExpr>)>::empty());
                    assert(seq_to_map(seq![a]) == seq_to_map(seq![a].drop_first()).insert(a.0, a.1));
                    assert(view_map(m@) == seq_to_map(seq![a]));
                }
                (Some(m), apos)
            }
        },
        None => (None, pos),
    }
}

/// Executable parser for a single-assignment `UPDATE`, refining `sparse_update`.
/// A trailing comma (multi-assignment) is outside `view_stmt`'s domain, so this
/// returns `None` there (the relaxed `None` disjunct).
#[verifier::rlimit(30000)]
pub fn parse_update_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos < toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_update(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && is_supdate(sopt.unwrap())
                    && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None || !is_supdate(sopt.unwrap())
                    || sopt.unwrap()->Update_set.len() != 1,
            }
    }),
{
    reveal_with_fuel(sparse_set_list, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if fuel == 0 {
        // sparse_set_list(_, 0) is None, so sparse_update yields None.
        proof { assert(sparse_update(input, 0nat).0 is None); }
        return (None, pos);
    }
    // sparse_update: input.len()>=3 && input[2]==Set, input[1]==Ident(table)
    if pos + 1 < toks.len() && pos + 2 < toks.len()
        && matches!(toks[pos + 2], super::Token::Keyword(Keyword::Set)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
            token_views_suffix(toks@, pos as int + 2);
        }
        match &toks[pos + 1] {
            super::Token::Ident(table) => {
                let ghost after_set = token_views(toks@.subrange(pos as int + 3, toks@.len() as int));
                proof { token_views_len(toks@.subrange(pos as int + 3, toks@.len() as int)); }
                let (aopt, apos) = parse_assign_exec(toks, pos + 3, fuel);
                match aopt {
                    Some((k, ve)) => {
                        let ghost gk = k;
                        let ghost gve = ve;
                        let ghost a_m = (gk, match gve {
                            Some(e) => Some(view_expr(e)),
                            None => None::<SExpr>,
                        });
                        let ghost r_m = token_views(toks@.subrange(apos as int, toks@.len() as int));
                        proof {
                            token_views_len(toks@.subrange(apos as int, toks@.len() as int));
                            // sparse_update dispatches into sparse_set_list(after_set).
                            assert(input.len() >= 3);
                            assert(input[1] == TokenView::Ident(*table));
                            assert(input[2] == TokenView::Keyword(Keyword::Set));
                            assert(input.drop_first().drop_first().drop_first() =~= after_set);
                            assert(sparse_assign(after_set, fuel as nat) == (Some(a_m), r_m));
                        }
                        // Reject multi-assignment: a comma means sparse_set_list continues.
                        if apos < toks.len()
                            && matches!(toks[apos], super::Token::Comma) {
                            proof {
                                token_views_suffix(toks@, apos as int);
                                assert(r_m.len() >= 1 && r_m[0] == TokenView::Comma);
                                lemma_sparse_set_list_len(r_m.drop_first(), (fuel - 1) as nat);
                                let (sopt, srest) = sparse_update(input, fuel as nat);
                                assert(sopt is None || sopt.unwrap()->Update_set.len() != 1);
                            }
                            (None, pos)
                        } else {
                            proof {
                                if apos < toks.len() {
                                    token_views_suffix(toks@, apos as int);
                                }
                                // no comma ⟹ sparse_set_list == (Some(seq![a_m]), r_m)
                                assert(r_m.len() == 0 || r_m[0] != TokenView::Comma);
                                assert(sparse_assign(after_set, fuel as nat).0.unwrap() == a_m);
                                assert(sparse_assign(after_set, fuel as nat) == (Some(a_m), r_m));
                                reveal_with_fuel(sparse_set_list, 1);
                                assert(sparse_set_list(after_set, fuel as nat) == (Some(seq![a_m]), r_m));
                            }
                            let mut m = build_one_entry_map(k, ve);
                            proof {
                                // view_stmt(Update{table, m, ..}).set == seq![a_m]
                                assert(m@.dom() =~= set![k]);
                                assert(m@.dom().len() == 1);
                                assert(m@.dom().contains(m@.dom().choose()));
                                assert(m@.dom().choose() == k);
                                assert(m@[k] == ve);
                            }
                            // where clause?
                            if apos < toks.len()
                                && matches!(toks[apos], super::Token::Keyword(Keyword::Where)) {
                                proof {
                                    token_views_suffix(toks@, apos as int);
                                    assert(r_m[0] == TokenView::Keyword(Keyword::Where));
                                    assert(r_m.drop_first()
                                        =~= token_views(toks@.subrange(apos as int + 1, toks@.len() as int)));
                                }
                                let (eopt, epos) = parse_expr_exec(toks, apos + 1, fuel);
                                match eopt {
                                    Some(e) => {
                                        let st = ast::Statement::Update {
                                            table: table.clone(),
                                            set: m,
                                            where_clause: Some(e),
                                        };
                                        proof {
                                            let (sopt, srest) = sparse_update(input, fuel as nat);
                                            assert(a_m == (k, match ve {
                                                Some(e2) => Some(view_expr(e2)),
                                                None => None::<SExpr>,
                                            }));
                                            assert(view_stmt(st) == SStmt::Update {
                                                table: *table,
                                                set: seq![a_m],
                                                where_clause: Some(view_expr(e)),
                                            });
                                            assert(sopt == Some(view_stmt(st)));
                                            assert(srest
                                                == token_views(toks@.subrange(epos as int, toks@.len() as int)));
                                        }
                                        (Some(st), epos)
                                    },
                                    None => {
                                        proof {
                                            let (sopt, srest) = sparse_update(input, fuel as nat);
                                            assert(sopt is None);
                                        }
                                        (None, pos)
                                    },
                                }
                            } else {
                                proof {
                                    if apos < toks.len() {
                                        token_views_suffix(toks@, apos as int);
                                    }
                                    assert(r_m.len() == 0 || r_m[0] != TokenView::Keyword(Keyword::Where));
                                }
                                let st = ast::Statement::Update {
                                    table: table.clone(),
                                    set: m,
                                    where_clause: None,
                                };
                                proof {
                                    let (sopt, srest) = sparse_update(input, fuel as nat);
                                    assert(a_m == (k, match ve {
                                        Some(e2) => Some(view_expr(e2)),
                                        None => None::<SExpr>,
                                    }));
                                    assert(view_stmt(st) == SStmt::Update {
                                        table: *table,
                                        set: seq![a_m],
                                        where_clause: None,
                                    });
                                    assert(sopt == Some(view_stmt(st)));
                                    assert(srest
                                        == token_views(toks@.subrange(apos as int, toks@.len() as int)));
                                }
                                (Some(st), apos)
                            }
                        }
                    },
                    None => {
                        // parse_assign failed ⟹ sparse_set_list None ⟹ sparse_update None.
                        proof { assert(sparse_update(input, fuel as nat).0 is None); }
                        (None, pos)
                    },
                }
            },
            _ => {
                // input[1] is not an Ident, so sparse_update's inner match fails.
                proof { assert(sparse_update(input, fuel as nat).0 is None); }
                (None, pos)
            },
        }
    } else {
        proof {
            // sparse_update fails: either input.len() < 3 (from token_views_len at
            // top: input.len() == toks.len() - pos) or input[2] != Set.
            if (pos as int) + 2 < toks@.len() {
                token_views_suffix(toks@, pos as int);
                token_views_suffix(toks@, pos as int + 1);
                token_views_suffix(toks@, pos as int + 2);
                assert(input.len() >= 3);
                assert(input[2] != TokenView::Keyword(Keyword::Set));
            } else {
                assert(input.len() < 3);
            }
            assert(sparse_update(input, fuel as nat).0 is None);
        }
        (None, pos)
    }
}

/// `sparse_update` roundtrip for a single-assignment `Update` (the `sparse_update`
/// slice of `lemma_sparse_stmt_sprint`, exposed for the executable headline).
pub proof fn lemma_sparse_update_sprint(s: SStmt, fuel: nat)
    requires
        is_supdate(s),
        printable_stmt(s),
        fuel >= sdepth_stmt(s),
    ensures
        sparse_update(sprint_stmt(s), fuel) == (Some(s), Seq::<TokenView>::empty()),
{
    reveal(printable_stmt);
    let tokens = sprint_stmt(s);
    match s {
        SStmt::Update { table, set, where_clause } => {
            let wherepart = match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
                None => Seq::<TokenView>::empty(),
            };
            let head = seq![
                TokenView::Keyword(Keyword::Update),
                TokenView::Ident(table),
                TokenView::Keyword(Keyword::Set),
            ];
            assert(tokens =~= head + sprint_set_list(set) + wherepart);
            assert(tokens[0] == TokenView::Keyword(Keyword::Update));
            assert(tokens[1] == TokenView::Ident(table));
            assert(tokens[2] == TokenView::Keyword(Keyword::Set));
            assert(tokens.drop_first().drop_first().drop_first() =~= sprint_set_list(set) + wherepart);
            assert(wherepart.len() == 0
                || (wherepart[0] != TokenView::Comma
                    && wherepart[0] != TokenView::Period
                    && wherepart[0] != TokenView::OpenParen)) by {
                match where_clause {
                    Some(e) => { assert(wherepart[0] == TokenView::Keyword(Keyword::Where)); },
                    None => { assert(wherepart =~= Seq::<TokenView>::empty()); },
                }
            }
            lemma_sparse_set_list_sprint(set, wherepart, fuel);
            match where_clause {
                Some(e) => {
                    assert(wherepart =~= seq![TokenView::Keyword(Keyword::Where)] + sprint(e));
                    assert(wherepart[0] == TokenView::Keyword(Keyword::Where));
                    assert(wherepart.drop_first() =~= sprint(e));
                    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
                    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel);
                },
                None => {
                    assert(wherepart =~= Seq::<TokenView>::empty());
                },
            }
            assert(sparse_update(tokens, fuel) == (Some(s), Seq::<TokenView>::empty()));
        },
        _ => { assert(false); },
    }
}

/// `sdepth_stmt(Update) <= sprint_stmt(Update).len()` for a single-assignment
/// Update — the fuel bound for the headline (the `full_exec_ok`-domain
/// `full_sdepth_le_len` excludes Update). The `+3` head and `[Ident,Equal]`
/// prefix give slack over the single set-list level.
pub proof fn update_sdepth_le_len(s: SStmt)
    requires
        is_supdate(s),
        printable_stmt(s),
        s->Update_set.len() == 1,
    ensures
        sdepth_stmt(s) <= sprint_stmt(s).len(),
{
    reveal(printable_stmt);
    match s {
        SStmt::Update { table, set, where_clause } => {
            let a = set[0];
            let wherepart = match where_clause {
                Some(e) => seq![TokenView::Keyword(Keyword::Where)] + sprint(e),
                None => Seq::<TokenView>::empty(),
            };
            assert(sprint_stmt(s) =~= seq![
                TokenView::Keyword(Keyword::Update),
                TokenView::Ident(table),
                TokenView::Keyword(Keyword::Set),
            ] + sprint_set_list(set) + wherepart);
            assert(set.drop_first().len() == 0);
            assert(set_list_depth(set.drop_first()) == 1);
            assert(sprint_set_list(set) =~= sprint_assign(a));
            match a.1 {
                Some(e) => {
                    sdepth_le_len(e);
                    assert(sprint_assign(a) =~= seq![TokenView::Ident(a.0), TokenView::Equal]
                        + sprint(e));
                },
                None => {
                    assert(sprint_assign(a) =~= seq![
                        TokenView::Ident(a.0),
                        TokenView::Equal,
                        TokenView::Keyword(Keyword::Default),
                    ]);
                },
            }
            match where_clause {
                Some(e) => { sdepth_le_len(e); },
                None => {},
            }
        },
        _ => { assert(false); },
    }
}

/// End-to-end executable roundtrip for a single-assignment `UPDATE`: printing a
/// printable single-assignment Update and parsing the result recovers it up to
/// `view_stmt`. This closes the 10th (and last) statement kind.
pub fn print_parse_roundtrip_update(s: &ast::Statement) -> (out: ast::Statement)
    requires
        printable_stmt(view_stmt(*s)),
        is_supdate(view_stmt(*s)),
    ensures
        view_stmt(out) == view_stmt(*s),
{
    let ghost sm = view_stmt(*s);
    let toks = print_update_exec(s);
    let fuel = toks.len();
    proof {
        assert(sm->Update_set.len() == 1);
        update_sdepth_le_len(sm);
        token_views_len(toks@);
        lemma_sparse_update_sprint(sm, fuel as nat);
        assert(toks@.subrange(0int, toks@.len() as int) =~= toks@);
    }
    let (res, consumed) = parse_update_exec(&toks, 0, fuel);
    match res {
        Some(out) => out,
        None => {
            proof { assert(false); }
            ast::Statement::Commit
        },
    }
}

/// End-to-end executable statement roundtrip for the full_exec_ok domain
/// (8 of 10 statement kinds plus Explain): printing a printable statement with
/// the executable printer and parsing the result with the executable parser
/// recovers it up to `view_stmt`. Self-contained; the parser's fuel is the token
/// count, which `full_sdepth_le_len` bounds against `sdepth_stmt`.
pub fn print_parse_roundtrip_stmt_full(s: &ast::Statement) -> (out: ast::Statement)
    requires
        printable_stmt(view_stmt(*s)),
        full_exec_ok(view_stmt(*s)),
    ensures
        view_stmt(out) == view_stmt(*s),
{
    let ghost sm = view_stmt(*s);
    let toks = print_stmt_full_exec(s);
    let fuel = toks.len();
    proof {
        full_sdepth_le_len(sm);
        token_views_len(toks@);
        lemma_sparse_stmt_sprint(sm, fuel as nat);
        assert(toks@.subrange(0int, toks@.len() as int) =~= toks@);
    }
    let (res, consumed) = parse_stmt_full_exec(&toks, 0, fuel);
    match res {
        Some(out) => out,
        None => {
            proof { assert(false); }
            ast::Statement::Commit
        },
    }
}

// -- fuel bound for the unified headline -------------------------------------

pub proof fn sdepth_column_le_len(c: SColumn)
    requires printable_column(c),
    ensures sdepth_column(c) <= sprint_column(c).len(),
{
    reveal(printable_column);
    reveal(sprint_column);
    let base = seq![TokenView::Ident(c.name), datatype_kw(c.datatype)];
    assert(sprint_column(c) =~= base + col_pk_toks(c) + col_null_toks(c) + col_unique_toks(c)
        + col_index_toks(c) + col_ref_toks(c) + col_default_toks(c));
    match c.default {
        Some(e) => {
            sdepth_le_len(e);
            assert(col_default_toks(c) =~= seq![TokenView::Keyword(Keyword::Default)] + sprint(e));
        },
        None => {},
    }
}

#[verifier::rlimit(40000)]
pub proof fn slist_depth_columns_le_len(cols: Seq<SColumn>)
    requires all_printable_columns(cols),
    ensures slist_depth_columns(cols) <= sprint_columns(cols).len() + 1,
    decreases cols,
{
    reveal_with_fuel(slist_depth_columns, 2);
    reveal_with_fuel(sprint_columns, 2);
    if cols.len() == 0 {
    } else if cols.len() == 1 {
        sdepth_column_le_len(cols[0]);
    } else {
        sdepth_column_le_len(cols[0]);
        slist_depth_columns_le_len(cols.drop_first());
    }
}

pub proof fn slist_depth_rows_le_len(rows: Seq<Seq<SExpr>>)
    requires all_printable_rows(rows),
    ensures slist_depth_rows(rows) <= sprint_rows(rows).len() + 1,
    decreases rows,
{
    if rows.len() == 0 {
    } else if rows.len() == 1 {
        assert(all_printable_se(rows[0]));
        super::verified_roundtrip::slist_depth_le_len(rows[0]);
        assert(slist_depth(rows[0]) >= 1);
        assert(slist_depth_rows(rows.drop_first()) == 1) by {
            assert(rows.drop_first().len() == 0);
        }
        assert(sprint_row(rows[0]) =~= seq![TokenView::OpenParen] + sprint_args(rows[0])
            + seq![TokenView::CloseParen]);
        assert(sprint_rows(rows) =~= sprint_row(rows[0]));
    } else {
        assert(all_printable_se(rows[0]));
        assert(all_printable_rows(rows.drop_first()));
        super::verified_roundtrip::slist_depth_le_len(rows[0]);
        slist_depth_rows_le_len(rows.drop_first());
        assert(sprint_row(rows[0]) =~= seq![TokenView::OpenParen] + sprint_args(rows[0])
            + seq![TokenView::CloseParen]);
        assert(sprint_rows(rows) =~= sprint_row(rows[0]) + seq![TokenView::Comma]
            + sprint_rows(rows.drop_first()));
    }
}

pub proof fn sprint_names_len_ge(names: Seq<String>)
    ensures names.len() <= sprint_names(names).len(),
    decreases names,
{
    if names.len() <= 1 {
    } else {
        sprint_names_len_ge(names.drop_first());
    }
}

#[verifier::rlimit(8000)]
pub proof fn full_sdepth_le_len(s: SStmt)
    requires printable_stmt(s), full_exec_ok(s),
    ensures sdepth_stmt(s) <= sprint_stmt(s).len(),
    decreases s,
{
    reveal(printable_stmt);
    reveal(full_exec_ok);
    match s {
        SStmt::Begin { .. } => {},
        SStmt::Commit => {},
        SStmt::Rollback => {},
        SStmt::CreateTable { name, columns } => {
            slist_depth_columns_le_len(columns);
            assert(sprint_stmt(s) =~= seq![
                TokenView::Keyword(Keyword::Create),
                TokenView::Keyword(Keyword::Table),
                TokenView::Ident(name),
                TokenView::OpenParen,
            ] + sprint_columns(columns) + seq![TokenView::CloseParen]);
        },
        SStmt::DropTable { .. } => {},
        SStmt::Delete { table, where_clause } => {
            match where_clause {
                Some(e) => {
                    sdepth_le_len(e);
                    assert(sprint_stmt(s) =~= seq![
                        TokenView::Keyword(Keyword::Delete),
                        TokenView::Keyword(Keyword::From),
                        TokenView::Ident(table),
                        TokenView::Keyword(Keyword::Where),
                    ] + sprint(e));
                },
                None => {},
            }
        },
        SStmt::Insert { table, columns, values } => {
            slist_depth_rows_le_len(values);
            match columns {
                Some(names) => { sprint_names_len_ge(names); },
                None => {},
            }
        },
        SStmt::Explain(inner) => {
            full_sdepth_le_len(*inner);
            assert(sprint_stmt(s) =~= seq![TokenView::Keyword(Keyword::Explain)] + sprint_stmt(*inner));
        },
        _ => {},
    }
}

#[verifier::rlimit(8000)]
pub fn print_stmt_full_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires printable_stmt(view_stmt(*s)), full_exec_ok(view_stmt(*s)),
    ensures token_views(r@) == sprint_stmt(view_stmt(*s)),
    decreases s,
{
    reveal(printable_stmt);
    reveal(full_exec_ok);
    reveal_with_fuel(token_views, 6);
    match s {
        ast::Statement::Commit => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Commit));
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
            r
        },
        ast::Statement::Rollback => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Rollback));
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
            r
        },
        ast::Statement::Begin { .. } => print_begin_exec(s),
        ast::Statement::CreateTable { .. } => print_createtable_exec(s),
        ast::Statement::Insert { .. } => print_insert_exec(s),
        ast::Statement::DropTable { name, if_exists } => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Drop));
            r.push(super::Token::Keyword(Keyword::Table));
            if *if_exists {
                r.push(super::Token::Keyword(Keyword::If));
                r.push(super::Token::Keyword(Keyword::Exists));
            }
            r.push(super::Token::Ident(name.clone()));
            proof {
                if *if_exists {
                    assert(r@.drop_first().drop_first().drop_first().drop_first().drop_first()
                        =~= Seq::<super::Token>::empty());
                } else {
                    assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                }
            }
            r
        },
        ast::Statement::Delete { table, where_clause } => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Delete));
            r.push(super::Token::Keyword(Keyword::From));
            r.push(super::Token::Ident(table.clone()));
            match where_clause {
                Some(e) => {
                    r.push(super::Token::Keyword(Keyword::Where));
                    let ghost head = r@;
                    let mut body = print_expr_exec(e);
                    let ghost body_old = body@;
                    r.append(&mut body);
                    proof {
                        assert(r@ =~= head + body_old);
                        token_views_concat(head, body_old);
                        assert(head.drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<super::Token>::empty());
                        assert(token_views(head) =~= seq![
                            TokenView::Keyword(Keyword::Delete),
                            TokenView::Keyword(Keyword::From),
                            TokenView::Ident(*table),
                            TokenView::Keyword(Keyword::Where),
                        ]);
                    }
                    r
                },
                None => {
                    proof {
                        assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                    }
                    r
                },
            }
        },
        ast::Statement::Explain(inner) => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Explain));
            let ghost head = r@;
            let mut body = print_stmt_full_exec(inner);
            let ghost body_old = body@;
            r.append(&mut body);
            proof {
                assert(r@ =~= head + body_old);
                token_views_concat(head, body_old);
                assert(head.drop_first() =~= Seq::<super::Token>::empty());
                assert(token_views(head) =~= seq![TokenView::Keyword(Keyword::Explain)]);
            }
            r
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

/// Statement kinds the unified executable parser recovers: everything except
/// Select and Update (whose exec parsers are not built yet), Explain recursively.
pub open spec fn full_exec_ok(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Begin { .. } => true,
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::CreateTable { .. } => true,
        SStmt::DropTable { .. } => true,
        SStmt::Delete { .. } => true,
        SStmt::Insert { .. } => true,
        SStmt::Explain(inner) => full_exec_ok(*inner),
        _ => false,
    }
}

/// Unified executable statement parser, refining `sparse_stmt` at `view_stmt`.
/// Sound always; complete on the `full_exec_ok` domain (returns `None` only when
/// `sparse_stmt` yields nothing in that domain).
#[verifier::rlimit(30000)]
pub fn parse_stmt_full_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_stmt(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && full_exec_ok(sopt.unwrap())
                    && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None || !full_exec_ok(sopt.unwrap()),
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_stmt, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 || pos >= toks.len() {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    match &toks[pos] {
        super::Token::Keyword(Keyword::Commit) => (Some(ast::Statement::Commit), pos + 1),
        super::Token::Keyword(Keyword::Rollback) => (Some(ast::Statement::Rollback), pos + 1),
        super::Token::Keyword(Keyword::Begin) => parse_begin_exec(toks, pos, fuel),
        super::Token::Keyword(Keyword::Create) => parse_createtable_exec(toks, pos, fuel),
        super::Token::Keyword(Keyword::Insert) => parse_insert_exec(toks, pos, fuel),
        super::Token::Keyword(Keyword::Drop) => {
            if pos + 1 < toks.len() && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Table)) {
                proof { token_views_suffix(toks@, pos as int + 1); }
                if pos + 2 < toks.len() && pos + 3 < toks.len()
                    && matches!(toks[pos + 2], super::Token::Keyword(Keyword::If))
                    && matches!(toks[pos + 3], super::Token::Keyword(Keyword::Exists)) {
                    proof {
                        token_views_suffix(toks@, pos as int + 2);
                        token_views_suffix(toks@, pos as int + 3);
                    }
                    if pos + 4 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 4); }
                        match &toks[pos + 4] {
                            super::Token::Ident(name) => (
                                Some(ast::Statement::DropTable { name: name.clone(), if_exists: true }),
                                pos + 5,
                            ),
                            _ => (None, pos),
                        }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 4, toks@.len() as int)); }
                        (None, pos)
                    }
                } else {
                    if pos + 2 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 2); }
                        match &toks[pos + 2] {
                            super::Token::Ident(name) => (
                                Some(ast::Statement::DropTable { name: name.clone(), if_exists: false }),
                                pos + 3,
                            ),
                            _ => (None, pos),
                        }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                        (None, pos)
                    }
                }
            } else {
                if pos + 1 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 1); }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                }
                (None, pos)
            }
        },
        super::Token::Keyword(Keyword::Delete) => {
            if pos + 1 < toks.len() && pos + 2 < toks.len()
                && matches!(toks[pos + 1], super::Token::Keyword(Keyword::From)) {
                proof {
                    token_views_suffix(toks@, pos as int + 1);
                    token_views_suffix(toks@, pos as int + 2);
                }
                match &toks[pos + 2] {
                    super::Token::Ident(table) => {
                        if pos + 3 < toks.len()
                            && matches!(toks[pos + 3], super::Token::Keyword(Keyword::Where)) {
                            proof { token_views_suffix(toks@, pos as int + 3); }
                            let (eopt, epos) = parse_expr_exec(toks, pos + 4, fuel);
                            match eopt {
                                Some(e) => (
                                    Some(ast::Statement::Delete { table: table.clone(), where_clause: Some(e) }),
                                    epos,
                                ),
                                None => (None, pos),
                            }
                        } else {
                            if pos + 3 < toks.len() {
                                proof { token_views_suffix(toks@, pos as int + 3); }
                            } else {
                                proof { token_views_len(toks@.subrange(pos as int + 3, toks@.len() as int)); }
                            }
                            (Some(ast::Statement::Delete { table: table.clone(), where_clause: None }), pos + 3)
                        }
                    },
                    _ => (None, pos),
                }
            } else {
                if pos + 1 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 1); }
                    if pos + 2 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 2); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                    }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                }
                (None, pos)
            }
        },
        super::Token::Keyword(Keyword::Explain) => {
            let (iopt, ipos) = parse_stmt_full_exec(toks, pos + 1, fuel - 1);
            match iopt {
                Some(inner) => {
                    if matches!(inner, ast::Statement::Explain(_)) {
                        (None, pos)
                    } else {
                        (Some(ast::Statement::Explain(Box::new(inner))), ipos)
                    }
                },
                None => (None, pos),
            }
        },
        _ => {
            reveal_with_fuel(sparse_update, 1);
            reveal_with_fuel(sparse_select, 1);
            (None, pos)
        },
    }
}

// -- CreateTable column exec parser ------------------------------------------
//
// Refines `sparse_column`. Its optional-clause helpers (`col_parse_pk`,
// `col_parse_null`, `opt_flag`, `col_parse_ref`) are opaque, so the cursor is
// advanced by dedicated exec helpers that each carry a matching fact, keeping
// the token-view bookkeeping local.

/// Advance past `PRIMARY KEY` if present. Returns the flag and new position;
/// the ghost fact matches `col_parse_pk` on the remaining view.
pub fn exec_col_pk(toks: &Vec<super::Token>, pos: usize) -> (r: (bool, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks@.len(),
        ({
            let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
            col_parse_pk(rem) == (r.0, token_views(toks@.subrange(r.1 as int, toks@.len() as int)))
        }),
{
    reveal(col_parse_pk);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len()
        && matches!(toks[pos], super::Token::Keyword(Keyword::Primary))
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Key)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
        }
        (true, pos + 2)
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
            if pos + 1 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 1); }
            }
        }
        (false, pos)
    }
}

pub fn exec_col_null(toks: &Vec<super::Token>, pos: usize) -> (r: (Option<bool>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks@.len(),
        ({
            let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
            col_parse_null(rem) == (r.0, token_views(toks@.subrange(r.1 as int, toks@.len() as int)))
        }),
{
    reveal(col_parse_null);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len()
        && matches!(toks[pos], super::Token::Keyword(Keyword::Not))
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Null)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
        }
        (Some(false), pos + 2)
    } else if pos < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::Null)) {
        proof { token_views_suffix(toks@, pos as int); }
        (Some(true), pos + 1)
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
            if pos + 1 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 1); }
            }
        }
        (None, pos)
    }
}

pub fn exec_col_unique(toks: &Vec<super::Token>, pos: usize) -> (r: (bool, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks@.len(),
        ({
            let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
            opt_flag(rem, Keyword::Unique) == (r.0, token_views(toks@.subrange(r.1 as int, toks@.len() as int)))
        }),
{
    reveal(opt_flag);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::Unique)) {
        proof { token_views_suffix(toks@, pos as int); }
        (true, pos + 1)
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
        }
        (false, pos)
    }
}

pub fn exec_col_index(toks: &Vec<super::Token>, pos: usize) -> (r: (bool, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks@.len(),
        ({
            let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
            opt_flag(rem, Keyword::Index) == (r.0, token_views(toks@.subrange(r.1 as int, toks@.len() as int)))
        }),
{
    reveal(opt_flag);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::Index)) {
        proof { token_views_suffix(toks@, pos as int); }
        (true, pos + 1)
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
        }
        (false, pos)
    }
}

pub fn exec_col_ref(toks: &Vec<super::Token>, pos: usize) -> (r: (Option<String>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks@.len(),
        ({
            let rem = token_views(toks@.subrange(pos as int, toks@.len() as int));
            col_parse_ref(rem) == (r.0, token_views(toks@.subrange(r.1 as int, toks@.len() as int)))
        }),
{
    reveal(col_parse_ref);
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() && pos + 1 < toks.len() && matches!(toks[pos], super::Token::Keyword(Keyword::References)) {
        proof {
            token_views_suffix(toks@, pos as int);
            token_views_suffix(toks@, pos as int + 1);
        }
        match &toks[pos + 1] {
            super::Token::Ident(t) => (Some(t.clone()), pos + 2),
            _ => (None, pos),
        }
    } else {
        if pos < toks.len() {
            proof { token_views_suffix(toks@, pos as int); }
            if pos + 1 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 1); }
            }
        }
        (None, pos)
    }
}

#[verifier::rlimit(15000)]
pub fn parse_column_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Column>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_column(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(col) => sopt is Some && view_column(col) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos);
    }
    if pos + 1 >= toks.len() {
        return (None, pos);
    }
    proof {
        token_views_suffix(toks@, pos as int);
        token_views_suffix(toks@, pos as int + 1);
    }
    let datatype = match &toks[pos + 1] {
        super::Token::Keyword(Keyword::Boolean) => DataType::Boolean,
        super::Token::Keyword(Keyword::Integer) => DataType::Integer,
        super::Token::Keyword(Keyword::Float) => DataType::Float,
        super::Token::Keyword(Keyword::String) => DataType::String,
        _ => return (None, pos),
    };
    let name = match &toks[pos] {
        super::Token::Ident(n) => n.clone(),
        _ => return (None, pos),
    };
    let (primary_key, c1) = exec_col_pk(toks, pos + 2);
    let (nullable, c2) = exec_col_null(toks, c1);
    let (unique, c3) = exec_col_unique(toks, c2);
    let (index, c4) = exec_col_index(toks, c3);
    let (references, c5) = exec_col_ref(toks, c4);
    if c5 < toks.len() && matches!(toks[c5], super::Token::Keyword(Keyword::Default)) {
        proof { token_views_suffix(toks@, c5 as int); }
        let (eopt, epos) = parse_expr_exec(toks, c5 + 1, fuel);
        match eopt {
            Some(e) => (
                Some(ast::Column {
                    name, datatype, primary_key, nullable, default: Some(e),
                    unique, index, references,
                }),
                epos,
            ),
            None => (None, pos),
        }
    } else {
        if c5 < toks.len() {
            proof { token_views_suffix(toks@, c5 as int); }
        }
        (
            Some(ast::Column {
                name, datatype, primary_key, nullable, default: None,
                unique, index, references,
            }),
            c5,
        )
    }
}

// -- CreateTable column exec printer (per-segment helpers avoid a solver blowup)

pub fn print_col_pk(c: &ast::Column) -> (r: Vec<super::Token>)
    ensures token_views(r@) == col_pk_toks(view_column(*c)),
{
    reveal_with_fuel(token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    if c.primary_key {
        r.push(super::Token::Keyword(Keyword::Primary));
        r.push(super::Token::Keyword(Keyword::Key));
        proof { assert(r@.drop_first().drop_first() =~= Seq::<super::Token>::empty()); }
    } else {
        proof { assert(r@ =~= Seq::<super::Token>::empty()); }
    }
    r
}

pub fn print_col_null(c: &ast::Column) -> (r: Vec<super::Token>)
    ensures token_views(r@) == col_null_toks(view_column(*c)),
{
    reveal_with_fuel(token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    match c.nullable {
        Some(true) => {
            r.push(super::Token::Keyword(Keyword::Null));
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
        },
        Some(false) => {
            r.push(super::Token::Keyword(Keyword::Not));
            r.push(super::Token::Keyword(Keyword::Null));
            proof { assert(r@.drop_first().drop_first() =~= Seq::<super::Token>::empty()); }
        },
        None => {
            proof { assert(r@ =~= Seq::<super::Token>::empty()); }
        },
    }
    r
}

pub fn print_col_flag(present: bool, kw: Keyword, ghost_toks: Ghost<Seq<TokenView>>) -> (r: Vec<super::Token>)
    requires ghost_toks@ == (if present { seq![TokenView::Keyword(kw)] } else { Seq::<TokenView>::empty() }),
    ensures token_views(r@) == ghost_toks@,
{
    reveal_with_fuel(token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    if present {
        r.push(super::Token::Keyword(kw));
        proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
    } else {
        proof { assert(r@ =~= Seq::<super::Token>::empty()); }
    }
    r
}

pub fn print_col_ref(c: &ast::Column) -> (r: Vec<super::Token>)
    ensures token_views(r@) == col_ref_toks(view_column(*c)),
{
    reveal_with_fuel(token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    match &c.references {
        Some(t) => {
            r.push(super::Token::Keyword(Keyword::References));
            r.push(super::Token::Ident(t.clone()));
            proof { assert(r@.drop_first().drop_first() =~= Seq::<super::Token>::empty()); }
        },
        None => {
            proof { assert(r@ =~= Seq::<super::Token>::empty()); }
        },
    }
    r
}

pub fn print_col_default(c: &ast::Column) -> (r: Vec<super::Token>)
    requires printable_column(view_column(*c)),
    ensures token_views(r@) == col_default_toks(view_column(*c)),
{
    reveal(printable_column);
    reveal_with_fuel(token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    match &c.default {
        Some(e) => {
            r.push(super::Token::Keyword(Keyword::Default));
            let ghost dk = r@;
            let mut body = print_expr_exec(e);
            let ghost body_old = body@;
            r.append(&mut body);
            proof {
                assert(r@ =~= dk + body_old);
                token_views_concat(dk, body_old);
                assert(dk.drop_first() =~= Seq::<super::Token>::empty());
                assert(token_views(dk) =~= seq![TokenView::Keyword(Keyword::Default)]);
            }
        },
        None => {
            proof { assert(r@ =~= Seq::<super::Token>::empty()); }
        },
    }
    r
}

#[verifier::rlimit(8000)]
pub fn print_column_exec(c: &ast::Column) -> (r: Vec<super::Token>)
    requires printable_column(view_column(*c)),
    ensures token_views(r@) == sprint_column(view_column(*c)),
{
    reveal_with_fuel(token_views, 3);
    reveal(sprint_column);
    let ghost vc = view_column(*c);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(super::Token::Ident(c.name.clone()));
    match c.datatype {
        DataType::Boolean => r.push(super::Token::Keyword(Keyword::Boolean)),
        DataType::Integer => r.push(super::Token::Keyword(Keyword::Integer)),
        DataType::Float => r.push(super::Token::Keyword(Keyword::Float)),
        DataType::String => r.push(super::Token::Keyword(Keyword::String)),
    }
    proof {
        assert(r@.drop_first().drop_first() =~= Seq::<super::Token>::empty());
        assert(token_views(r@) =~= seq![TokenView::Ident(vc.name), datatype_kw(vc.datatype)]);
    }
    let ghost p0 = r@;
    let mut s1 = print_col_pk(c);
    let ghost s1o = s1@;
    r.append(&mut s1);
    proof { token_views_concat(p0, s1o); }
    let ghost p1 = r@;
    let mut s2 = print_col_null(c);
    let ghost s2o = s2@;
    r.append(&mut s2);
    proof { token_views_concat(p1, s2o); }
    let ghost p2 = r@;
    let mut s3 = print_col_flag(c.unique, Keyword::Unique, Ghost(col_unique_toks(vc)));
    let ghost s3o = s3@;
    r.append(&mut s3);
    proof { token_views_concat(p2, s3o); }
    let ghost p3 = r@;
    let mut s4 = print_col_flag(c.index, Keyword::Index, Ghost(col_index_toks(vc)));
    let ghost s4o = s4@;
    r.append(&mut s4);
    proof { token_views_concat(p3, s4o); }
    let ghost p4 = r@;
    let mut s5 = print_col_ref(c);
    let ghost s5o = s5@;
    r.append(&mut s5);
    proof { token_views_concat(p4, s5o); }
    let ghost p5 = r@;
    let mut s6 = print_col_default(c);
    let ghost s6o = s6@;
    r.append(&mut s6);
    proof {
        token_views_concat(p5, s6o);
        assert(sprint_column(vc) =~= seq![TokenView::Ident(vc.name), datatype_kw(vc.datatype)]
            + col_pk_toks(vc) + col_null_toks(vc) + col_unique_toks(vc) + col_index_toks(vc)
            + col_ref_toks(vc) + col_default_toks(vc));
    }
    r
}

/// Executable BEGIN printer. Only two optional clauses (READ ONLY prefix,
/// AS OF SYSTEM TIME suffix), so no per-segment helper is needed.
#[verifier::rlimit(8000)]
pub fn print_begin_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires
        printable_stmt(view_stmt(*s)),
        is_sbegin(view_stmt(*s)),
    ensures
        token_views(r@) == sprint_stmt(view_stmt(*s)),
{
    reveal_with_fuel(token_views, 3);
    match s {
        ast::Statement::Begin { read_only, as_of } => {
            let mut r: Vec<super::Token> = Vec::new();
            r.push(super::Token::Keyword(Keyword::Begin));
            if *read_only {
                r.push(super::Token::Keyword(Keyword::Read));
                r.push(super::Token::Keyword(Keyword::Only));
            }
            let ghost prefix = r@;
            proof {
                reveal_with_fuel(token_views, 4);
                if *read_only {
                    assert(prefix.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                    assert(token_views(prefix) =~= seq![
                        TokenView::Keyword(Keyword::Begin),
                        TokenView::Keyword(Keyword::Read),
                        TokenView::Keyword(Keyword::Only),
                    ]);
                } else {
                    assert(prefix.drop_first() =~= Seq::<super::Token>::empty());
                    assert(token_views(prefix) =~= seq![TokenView::Keyword(Keyword::Begin)]);
                }
            }
            match as_of {
                Some(v) => {
                    r.push(super::Token::Keyword(Keyword::As));
                    r.push(super::Token::Keyword(Keyword::Of));
                    r.push(super::Token::Keyword(Keyword::System));
                    r.push(super::Token::Keyword(Keyword::Time));
                    r.push(super::Token::Number(super::verified_integer::print_u64(*v)));
                    proof {
                        reveal_with_fuel(token_views, 6);
                        let seg = r@.subrange(prefix.len() as int, r@.len() as int);
                        assert(r@ =~= prefix + seg);
                        token_views_concat(prefix, seg);
                        assert(seg.drop_first().drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<super::Token>::empty());
                        assert(token_views(seg) =~= seq![
                            TokenView::Keyword(Keyword::As),
                            TokenView::Keyword(Keyword::Of),
                            TokenView::Keyword(Keyword::System),
                            TokenView::Keyword(Keyword::Time),
                            TokenView::Number(verified_integer::decimal_digits(*v)),
                        ]);
                    }
                },
                None => {
                    proof { assert(r@ =~= prefix); }
                },
            }
            r
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

#[verifier::rlimit(8000)]
pub fn print_insert_exec(s: &ast::Statement) -> (r: Vec<super::Token>)
    requires
        printable_stmt(view_stmt(*s)),
        is_sinsert(view_stmt(*s)),
    ensures
        token_views(r@) == sprint_stmt(view_stmt(*s)),
{
    reveal(printable_stmt);
    reveal_with_fuel(token_views, 5);
    match s {
        ast::Statement::Insert { table, columns, values } => match columns {
            None => {
                let mut r: Vec<super::Token> = Vec::new();
                r.push(super::Token::Keyword(Keyword::Insert));
                r.push(super::Token::Keyword(Keyword::Into));
                r.push(super::Token::Ident(table.clone()));
                r.push(super::Token::Keyword(Keyword::Values));
                let ghost head = r@;
                let mut rows = print_rows_slice(values.as_slice());
                let ghost rows_old = rows@;
                r.append(&mut rows);
                proof {
                    view_rows_len(values@);
                    assert(r@ =~= head + rows_old);
                    token_views_concat(head, rows_old);
                    assert(head.drop_first().drop_first().drop_first().drop_first()
                        =~= Seq::<super::Token>::empty());
                    assert(token_views(head) =~= seq![
                        TokenView::Keyword(Keyword::Insert),
                        TokenView::Keyword(Keyword::Into),
                        TokenView::Ident(*table),
                        TokenView::Keyword(Keyword::Values),
                    ]);
                }
                r
            },
            Some(cols) => {
                let mut r: Vec<super::Token> = Vec::new();
                r.push(super::Token::Keyword(Keyword::Insert));
                r.push(super::Token::Keyword(Keyword::Into));
                r.push(super::Token::Ident(table.clone()));
                r.push(super::Token::OpenParen);
                let ghost head = r@;
                let mut names = print_names_slice(cols.as_slice());
                let ghost names_old = names@;
                r.append(&mut names);
                r.push(super::Token::CloseParen);
                r.push(super::Token::Keyword(Keyword::Values));
                let ghost mid = r@;
                let mut rows = print_rows_slice(values.as_slice());
                let ghost rows_old = rows@;
                r.append(&mut rows);
                proof {
                    view_rows_len(values@);
                    assert(r@ =~= mid + rows_old);
                    token_views_concat(mid, rows_old);
                    assert(mid =~= head + names_old
                        + seq![super::Token::CloseParen, super::Token::Keyword(Keyword::Values)]);
                    token_views_concat(head + names_old,
                        seq![super::Token::CloseParen, super::Token::Keyword(Keyword::Values)]);
                    token_views_concat(head, names_old);
                    assert(head.drop_first().drop_first().drop_first().drop_first()
                        =~= Seq::<super::Token>::empty());
                    assert(token_views(head) =~= seq![
                        TokenView::Keyword(Keyword::Insert),
                        TokenView::Keyword(Keyword::Into),
                        TokenView::Ident(*table),
                        TokenView::OpenParen,
                    ]);
                    assert(seq![super::Token::CloseParen, super::Token::Keyword(Keyword::Values)]
                        .drop_first().drop_first() =~= Seq::<super::Token>::empty());
                    assert(token_views(seq![super::Token::CloseParen,
                        super::Token::Keyword(Keyword::Values)])
                        =~= seq![TokenView::CloseParen, TokenView::Keyword(Keyword::Values)]);
                }
                r
            },
        },
        _ => {
            proof { assert(false); }
            Vec::new()
        },
    }
}

#[verifier::rlimit(8000)]
pub fn parse_names_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<String>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_names(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(v) => sopt is Some && v@ == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_names, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 || pos >= toks.len() {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    match &toks[pos] {
        super::Token::Ident(name) => {
            if pos + 1 >= toks.len() {
                proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                (None, pos)
            } else {
                proof { token_views_suffix(toks@, pos as int + 1); }
                match &toks[pos + 1] {
                    super::Token::CloseParen => {
                        let mut v: Vec<String> = Vec::new();
                        v.push(name.clone());
                        proof { assert(v@.drop_first() =~= Seq::<String>::empty()); }
                        (Some(v), pos + 1)
                    },
                    super::Token::Comma => {
                        let (mopt, mpos) = parse_names_exec(toks, pos + 2, fuel - 1);
                        match mopt {
                            Some(mut more) => {
                                let mut v: Vec<String> = Vec::new();
                                v.push(name.clone());
                                let ghost first = v@;
                                let ghost more_old = more@;
                                v.append(&mut more);
                                proof {
                                    assert(v@ =~= first + more_old);
                                    assert(first.drop_first() =~= Seq::<String>::empty());
                                }
                                (Some(v), mpos)
                            },
                            None => (None, pos),
                        }
                    },
                    _ => (None, pos),
                }
            }
        },
        _ => (None, pos),
    }
}

#[verifier::rlimit(20000)]
pub fn parse_rows_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<Vec<ast::Expression>>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_rows(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(vv) => sopt is Some && view_rows(vv@) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_rows, 1);
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 || pos >= toks.len() {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], super::Token::OpenParen) {
        return (None, pos);
    }
    let (ropt, rpos) = parse_args_exec(toks, pos + 1, fuel);
    match ropt {
        Some(row) => {
            if rpos < toks.len() && matches!(toks[rpos], super::Token::CloseParen) {
                proof { token_views_suffix(toks@, rpos as int); }
                if rpos + 1 < toks.len() && matches!(toks[rpos + 1], super::Token::Comma) {
                    proof { token_views_suffix(toks@, rpos as int + 1); }
                    let (mopt, mpos) = parse_rows_exec(toks, rpos + 2, fuel - 1);
                    match mopt {
                        Some(mut more) => {
                            let mut v: Vec<Vec<ast::Expression>> = Vec::new();
                            v.push(row);
                            let ghost first = v@;
                            let ghost more_old = more@;
                            v.append(&mut more);
                            proof {
                                assert(v@ =~= first + more_old);
                                view_rows_step(v@);
                                assert(v@.drop_first() =~= more_old);
                                assert(view_rows(more_old) == sparse_rows(
                                    token_views(toks@.subrange(rpos as int + 2, toks@.len() as int)),
                                    (fuel - 1) as nat).0.unwrap());
                            }
                            (Some(v), mpos)
                        },
                        None => (None, pos),
                    }
                } else {
                    if rpos + 1 < toks.len() {
                        proof { token_views_suffix(toks@, rpos as int + 1); }
                    } else {
                        proof { token_views_len(toks@.subrange(rpos as int + 1, toks@.len() as int)); }
                    }
                    let mut v: Vec<Vec<ast::Expression>> = Vec::new();
                    v.push(row);
                    proof {
                        view_rows_step(v@);
                        assert(v@.drop_first() =~= Seq::<Vec<ast::Expression>>::empty());
                    }
                    (Some(v), rpos + 1)
                }
            } else {
                if rpos < toks.len() {
                    proof { token_views_suffix(toks@, rpos as int); }
                } else {
                    proof { token_views_len(toks@.subrange(rpos as int, toks@.len() as int)); }
                }
                (None, pos)
            }
        },
        None => (None, pos),
    }
}

/// Executable INSERT parser, refining `sparse_insert` at the `view_stmt` level.
#[verifier::rlimit(20000)]
pub fn parse_insert_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_insert(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && view_stmt(st) == sopt.unwrap()
                    && srest == token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
    }),
{
    let ghost input = token_views(toks@.subrange(pos as int, toks@.len() as int));
    if pos >= toks.len() {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    if pos + 1 < toks.len() && pos + 2 < toks.len()
        && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Into)) {
        proof {
            token_views_suffix(toks@, pos as int + 1);
            token_views_suffix(toks@, pos as int + 2);
        }
        match &toks[pos + 2] {
            super::Token::Ident(table) => {
                if pos + 3 < toks.len() && matches!(toks[pos + 3], super::Token::OpenParen) {
                    proof { token_views_suffix(toks@, pos as int + 3); }
                    let (nopt, npos) = parse_names_exec(toks, pos + 4, fuel);
                    match nopt {
                        Some(names) => {
                            if npos < toks.len() && matches!(toks[npos], super::Token::CloseParen) {
                                proof { token_views_suffix(toks@, npos as int); }
                                if npos + 1 < toks.len()
                                    && matches!(toks[npos + 1], super::Token::Keyword(Keyword::Values)) {
                                    proof { token_views_suffix(toks@, npos as int + 1); }
                                    let (vopt, vpos) = parse_rows_exec(toks, npos + 2, fuel);
                                    match vopt {
                                        Some(values) => (
                                            Some(ast::Statement::Insert {
                                                table: table.clone(),
                                                columns: Some(names),
                                                values,
                                            }),
                                            vpos,
                                        ),
                                        None => (None, pos),
                                    }
                                } else {
                                    if npos + 1 < toks.len() {
                                        proof { token_views_suffix(toks@, npos as int + 1); }
                                    } else {
                                        proof { token_views_len(toks@.subrange(npos as int + 1, toks@.len() as int)); }
                                    }
                                    (None, pos)
                                }
                            } else {
                                if npos < toks.len() {
                                    proof { token_views_suffix(toks@, npos as int); }
                                } else {
                                    proof { token_views_len(toks@.subrange(npos as int, toks@.len() as int)); }
                                }
                                (None, pos)
                            }
                        },
                        None => (None, pos),
                    }
                } else if pos + 3 < toks.len()
                    && matches!(toks[pos + 3], super::Token::Keyword(Keyword::Values)) {
                    proof { token_views_suffix(toks@, pos as int + 3); }
                    let (vopt, vpos) = parse_rows_exec(toks, pos + 4, fuel);
                    match vopt {
                        Some(values) => (
                            Some(ast::Statement::Insert {
                                table: table.clone(),
                                columns: None,
                                values,
                            }),
                            vpos,
                        ),
                        None => (None, pos),
                    }
                } else {
                    if pos + 3 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 3); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 3, toks@.len() as int)); }
                    }
                    (None, pos)
                }
            },
            _ => (None, pos),
        }
    } else {
        if pos + 1 < toks.len() {
            proof { token_views_suffix(toks@, pos as int + 1); }
            if pos + 2 < toks.len() {
                proof { token_views_suffix(toks@, pos as int + 2); }
            } else {
                proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
            }
        } else {
            proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
        }
        (None, pos)
    }
}

/// The non-recursive list-free statements the executable parser recovers
/// (Explain is excluded to keep the parser recursion-free).
pub open spec fn flat_exec_ok(s: SStmt) -> bool {
    match s {
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::DropTable { .. } => true,
        SStmt::Delete { .. } => true,
        _ => false,
    }
}

pub proof fn flat_implies_exec_ok(s: SStmt)
    requires flat_exec_ok(s),
    ensures exec_ok(s),
{
    reveal(exec_ok);
}

/// For a printable flat statement, the fuel `sprint_stmt(s).len()` bounds
/// `sdepth_stmt(s)` (so the headline can fuel the parser from the token count).
pub proof fn flat_sdepth_le_len(s: SStmt)
    requires printable_stmt(s), flat_exec_ok(s),
    ensures sdepth_stmt(s) <= sprint_stmt(s).len(),
{
    reveal(printable_stmt);
    match s {
        SStmt::Commit => {},
        SStmt::Rollback => {},
        SStmt::DropTable { name, if_exists } => {},
        SStmt::Delete { table, where_clause } => {
            match where_clause {
                Some(e) => { sdepth_le_len(e); },
                None => {},
            }
        },
        _ => {},
    }
}

/// Executable parser for the flat list-free statements, refining `sparse_stmt`
/// at the `view_stmt` level. Sound (never wrong) and complete on the flat
/// domain: it returns `None` exactly when `sparse_stmt` yields nothing flat.
#[verifier::rlimit(20000)]
pub fn parse_stmt_exec(toks: &Vec<super::Token>, pos: usize, fuel: usize)
    -> (r: (Option<ast::Statement>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
        let (sopt, srest) = sparse_stmt(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(st) => sopt is Some && flat_exec_ok(sopt.unwrap())
                    && view_stmt(st) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None || !flat_exec_ok(sopt.unwrap()),
            }
    }),
{
    reveal_with_fuel(sparse_stmt, 1);
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    if fuel == 0 || pos >= toks.len() {
        proof { token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos);
    }
    proof { token_views_suffix(toks@, pos as int); }
    match &toks[pos] {
        super::Token::Keyword(Keyword::Commit) => {
            proof { token_views_suffix(toks@, pos as int); }
            (Some(ast::Statement::Commit), pos + 1)
        },
        super::Token::Keyword(Keyword::Rollback) => {
            proof { token_views_suffix(toks@, pos as int); }
            (Some(ast::Statement::Rollback), pos + 1)
        },
        super::Token::Keyword(Keyword::Drop) => {
            if pos + 1 < toks.len() && matches!(toks[pos + 1], super::Token::Keyword(Keyword::Table)) {
                proof { token_views_suffix(toks@, pos as int + 1); }
                if pos + 2 < toks.len() && pos + 3 < toks.len()
                    && matches!(toks[pos + 2], super::Token::Keyword(Keyword::If))
                    && matches!(toks[pos + 3], super::Token::Keyword(Keyword::Exists)) {
                    proof {
                        token_views_suffix(toks@, pos as int + 2);
                        token_views_suffix(toks@, pos as int + 3);
                    }
                    if pos + 4 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 4); }
                        match &toks[pos + 4] {
                            super::Token::Ident(name) => (
                                Some(ast::Statement::DropTable { name: name.clone(), if_exists: true }),
                                pos + 5,
                            ),
                            _ => (None, pos),
                        }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 4, toks@.len() as int)); }
                        (None, pos)
                    }
                } else {
                    if pos + 2 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 2); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                    }
                    if pos + 2 < toks.len() {
                        match &toks[pos + 2] {
                            super::Token::Ident(name) => (
                                Some(ast::Statement::DropTable { name: name.clone(), if_exists: false }),
                                pos + 3,
                            ),
                            _ => (None, pos),
                        }
                    } else {
                        (None, pos)
                    }
                }
            } else {
                if pos + 1 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 1); }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                }
                (None, pos)
            }
        },
        super::Token::Keyword(Keyword::Delete) => {
            if pos + 1 < toks.len() && pos + 2 < toks.len()
                && matches!(toks[pos + 1], super::Token::Keyword(Keyword::From)) {
                proof {
                    token_views_suffix(toks@, pos as int + 1);
                    token_views_suffix(toks@, pos as int + 2);
                }
                match &toks[pos + 2] {
                    super::Token::Ident(table) => {
                        if pos + 3 < toks.len()
                            && matches!(toks[pos + 3], super::Token::Keyword(Keyword::Where)) {
                            proof { token_views_suffix(toks@, pos as int + 3); }
                            let (eopt, epos) = parse_expr_exec(toks, pos + 4, fuel);
                            match eopt {
                                Some(e) => (
                                    Some(ast::Statement::Delete {
                                        table: table.clone(),
                                        where_clause: Some(e),
                                    }),
                                    epos,
                                ),
                                None => (None, pos),
                            }
                        } else {
                            if pos + 3 < toks.len() {
                                proof { token_views_suffix(toks@, pos as int + 3); }
                            } else {
                                proof { token_views_len(toks@.subrange(pos as int + 3, toks@.len() as int)); }
                            }
                            (
                                Some(ast::Statement::Delete {
                                    table: table.clone(),
                                    where_clause: None,
                                }),
                                pos + 3,
                            )
                        }
                    },
                    _ => (None, pos),
                }
            } else {
                if pos + 1 < toks.len() {
                    proof { token_views_suffix(toks@, pos as int + 1); }
                    if pos + 2 < toks.len() {
                        proof { token_views_suffix(toks@, pos as int + 2); }
                    } else {
                        proof { token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int)); }
                    }
                } else {
                    proof { token_views_len(toks@.subrange(pos as int + 1, toks@.len() as int)); }
                }
                (None, pos)
            }
        },
        _ => {
            reveal_with_fuel(sparse_begin, 1);
            reveal_with_fuel(sparse_create, 1);
            reveal_with_fuel(sparse_insert, 1);
            reveal_with_fuel(sparse_update, 1);
            reveal_with_fuel(sparse_select, 1);
            (None, pos)
        },
    }
}

/// End-to-end executable statement roundtrip for the flat list-free statements:
/// printing then parsing recovers the statement up to `view_stmt`.
pub fn print_parse_roundtrip_stmt(s: &ast::Statement) -> (out: ast::Statement)
    requires
        printable_stmt(view_stmt(*s)),
        flat_exec_ok(view_stmt(*s)),
    ensures
        view_stmt(out) == view_stmt(*s),
{
    let ghost sm = view_stmt(*s);
    proof { flat_implies_exec_ok(sm); }
    let toks = print_stmt_exec(s);
    let fuel = toks.len();
    proof {
        flat_sdepth_le_len(sm);
        token_views_len(toks@);
        lemma_sparse_stmt_sprint(sm, fuel as nat);
        assert(toks@.subrange(0int, toks@.len() as int) =~= toks@);
    }
    let (res, consumed) = parse_stmt_exec(&toks, 0, fuel);
    match res {
        Some(out) => out,
        None => {
            proof { assert(false); }
            ast::Statement::Commit
        },
    }
}

} // verus!
