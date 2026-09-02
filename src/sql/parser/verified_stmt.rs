//!
//!
//!

// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::SExpr;
// Ghost (spec/proof) helpers: stripped under a plain `cargo build`, so gate the
// imports behind `verus_keep_ghost` to keep the non-Verus build resolving.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::{sparse, sparse_args, view_args, view_expr};
#[allow(unused_imports)]
use super::{Keyword, ast, verified_integer};
#[allow(unused_imports)]
use crate::sql::types::DataType;
#[allow(unused_imports)]
use core::cmp::Ordering;
// `std_specs` is gated behind `verus_keep_ghost`; these trait imports are only
// needed for the `cmp_spec`/`eq_spec` proof helpers below, so gate them too or a
// plain `cargo build`/`cargo test` fails to resolve them.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};

verus! {


/// Mirror of `ast::Statement`. Expression children are `SExpr` (via `view_expr`)
/// and containers become `Seq`s. `Unsupported` is the placeholder for statement
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
        ast::Statement::Update { table, set, order, where_clause } =>
            view_update_arm(table, set@, order@, where_clause),
        ast::Statement::Explain(inner) => SStmt::Explain(Box::new(view_stmt(*inner))),
        _ => SStmt::Unsupported,
    }
}

/// Well-formedness of an UPDATE's ghost `order` against its `set` map: the
/// order lists each assigned column exactly once (`no_dups`) and lists all of
/// them and only them (`order.to_set() == set.dom()`). Together with the value
/// map this is a bijection `Seq<(String, Option<SExpr>)> <-> Map<...>` on the
/// UPDATE assignment set (see `lemma_update_bijection`).
pub open spec fn wf_update(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
) -> bool {
    &&& order.no_duplicates()
    &&& order.to_set() == set.dom()
}

/// Build the mirror assignment sequence from the ghost `order`: read the keys in
/// `order` and pair each with its value from `set`. Total (no `dom().choose()`,
/// no `len == 1` special case) when `wf_update(set, order)` holds.
pub open spec fn view_update_assigns(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
) -> Seq<(String, Option<SExpr>)> {
    order.map_values(|k: String| (k, view_opt(set[k])))
}

pub open spec fn view_update_arm(
    table: String,
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
    where_clause: Option<ast::Expression>,
) -> SStmt {
    if wf_update(set, order) {
        SStmt::Update {
            table,
            set: view_update_assigns(set, order),
            where_clause: view_opt(where_clause),
        }
    } else {
        SStmt::Unsupported
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

/// Consume an optional single-keyword flag. Returns whether it was present and
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

//
// A `From` item is a left-deep join tree whose right child is always a table.

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

pub open spec fn is_cross(jt: ast::JoinType) -> bool {
    match jt {
        ast::JoinType::Cross => true,
        _ => false,
    }
}

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

/// Parse `k = expr` or `k = DEFAULT`. The expr is tried first; `DEFAULT` is a
/// keyword that never starts an expression, so `sparse` fails on it and the
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

#[verifier::external_body]
pub proof fn axiom_string_obeys_cmp()
    ensures vstd::laws_cmp::obeys_cmp::<String>(),
{
}

/// Trusted: `String`'s `PartialEq` is by-value, so `eq_spec` coincides with `==`
/// (`obeys_concrete_eq`). Needed to turn `cmp_spec(x, y) is Equal` into `x == y`
/// when proving the key order is a *total ordering* (antisymmetry).
#[verifier::external_body]
pub proof fn axiom_string_concrete_eq()
    ensures vstd::laws_eq::obeys_concrete_eq::<String>(),
{
}

/// Non-strict key order on `String`, derived from the `Ord` model: `a <= b` iff
/// `a.cmp_spec(&b)` is `Less` or `Equal`. This is the total order the sorted
/// canonical UPDATE-assignment form is sorted by; it matches vstd's BTreeMap
/// `increasing_seq` (which uses the *strict* `is Less`) on distinct keys.
pub open spec fn str_leq(a: String, b: String) -> bool {
    a.cmp_spec(&b) is Less
        || a.cmp_spec(&b) is Equal
}

/// `str_leq` is a total ordering (reflexive, antisymmetric, transitive,
/// strongly-connected) — the precondition of `Seq::sort_by` / `lemma_sorted_unique`.
pub proof fn lemma_str_leq_total_ordering()
    ensures vstd::relations::total_ordering(|a: String, b: String| str_leq(a, b)),
{
    axiom_string_obeys_cmp();
    axiom_string_concrete_eq();
    let leq = |a: String, b: String| str_leq(a, b);
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    reveal(vstd::laws_eq::obeys_concrete_eq);
    // partial_cmp_spec(x, y) == Some(cmp_spec(x, y)) for all x, y.
    assert forall|x: String, y: String|
        x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y)) by {}
    // reflexive: cmp_spec(x, x) is Equal (via eq_spec reflexivity).
    assert(vstd::relations::reflexive(leq)) by {
        assert forall|x: String| #[trigger] leq(x, x) by {
            assert(x.eq_spec(&x));
            assert(x.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Equal));
        }
    }
    // strongly_connected: for all x, y, leq(x, y) || leq(y, x).
    assert(vstd::relations::strongly_connected(leq)) by {
        assert forall|x: String, y: String| #[trigger] leq(x, y) || #[trigger] leq(y, x) by {
            match x.cmp_spec(&y) {
                core::cmp::Ordering::Less => {},
                core::cmp::Ordering::Equal => {},
                core::cmp::Ordering::Greater => {
                    assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Greater));
                    assert(y.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                    assert(y.cmp_spec(&x) is Less);
                },
            }
        }
    }
    // antisymmetric: leq(x, y) && leq(y, x) ==> x == y (both non-Greater forces Equal).
    assert(vstd::relations::antisymmetric(leq)) by {
        assert forall|x: String, y: String| #[trigger] leq(x, y) && #[trigger] leq(y, x)
            implies x == y by {
            // Neither can be Less (Less on one side forces Greater on the other,
            // contradicting the other leq), so both are Equal.
            if x.cmp_spec(&y) is Less {
                assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                assert(y.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Greater));
                assert(y.cmp_spec(&x) is Greater);
                assert(false);
            }
            assert(x.cmp_spec(&y) is Equal);
            assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Equal));
            assert(x.eq_spec(&y));
            assert(x == y);
        }
    }
    // transitive: leq(x, y) && leq(y, z) ==> leq(x, z).
    assert(vstd::relations::transitive(leq)) by {
        assert forall|x: String, y: String, z: String| #[trigger] leq(x, y) && #[trigger] leq(y, z)
            implies leq(x, z) by {
            // Reduce to partial_cmp_spec facts. leq(a, b) <==> !(b < a).
            if x.cmp_spec(&z) is Greater {
                assert(x.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Greater));
                assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                // z < x with x <= y and y <= z contradicts transitivity of <.
                if x.cmp_spec(&y) is Equal {
                    assert(x.eq_spec(&y));
                    // x == y, so z < x means z < y, but y <= z.
                    assert(x == y);
                    if y.cmp_spec(&z) is Equal {
                        assert(y.eq_spec(&z));
                        assert(y == z);
                        assert(false);
                    } else {
                        assert(y.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        // y < z and z < x=y ==> y < y, contradiction with reflexive Equal.
                        assert(z.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                        assert(y.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                        assert(y.eq_spec(&y));
                        assert(false);
                    }
                } else {
                    assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                    if y.cmp_spec(&z) is Equal {
                        assert(y.eq_spec(&z));
                        assert(y == z);
                        // x < y=z and z < x ==> x < x.
                        assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        assert(x.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        assert(x.eq_spec(&x));
                        assert(false);
                    } else {
                        assert(y.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        // x < y and y < z ==> x < z, contradicting z < x.
                        assert(x.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        assert(false);
                    }
                }
            }
        }
    }
}

/// Sort a key list into ascending `str_leq` order. Used to canonicalise an
/// UPDATE's assignment order so it matches the sorted `BTreeMap::iter()` walk of
/// the executable printer, independent of parse order.
pub open spec fn sorted_keys(keys: Seq<String>) -> Seq<String> {
    keys.sort_by(|a: String, b: String| str_leq(a, b))
}

/// A key sequence that is already sorted (distinct + `increasing_seq`) is a fixed
/// point of `sorted_keys`: sorting it is the identity. This is the "sort is
/// identity on already-sorted keys" idempotence used by the UPDATE roundtrip.
pub proof fn lemma_sorted_keys_idempotent(keys: Seq<String>)
    requires
        keys.no_duplicates(),
        vstd::std_specs::btree::increasing_seq(keys),
    ensures
        sorted_keys(keys) == keys,
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    lemma_str_leq_total_ordering();
    let leq = |a: String, b: String| str_leq(a, b);
    // `keys` is already `sorted_by(leq)`: increasing_seq gives strict Less on i<j.
    assert(vstd::relations::sorted_by(keys, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < keys.len()
            implies #[trigger] leq(keys[i], keys[j]) by {
            assert(keys[i].cmp_spec(&keys[j]) is Less);
        }
    }
    // `sorted_keys(keys)` is sorted and a permutation of `keys` (same multiset).
    keys.lemma_sort_by_ensures(leq);
    assert(vstd::relations::sorted_by(keys.sort_by(leq), leq));
    assert(keys.to_multiset() =~= keys.sort_by(leq).to_multiset());
    // Two sorted sequences with the same multiset are equal.
    vstd::seq_lib::lemma_sorted_unique(keys, keys.sort_by(leq), leq);
}

/// Sorting a distinct key sequence yields a permutation that is still distinct,
/// covers the same set of keys, has the same length, and is `increasing_seq`
/// (strictly ascending, since distinct). These are the facts needed to prove
/// `wf_update(set, sorted_keys(order))` and to feed `printable_stmt`.
pub proof fn lemma_sorted_keys_props(keys: Seq<String>)
    requires
        keys.no_duplicates(),
    ensures
        sorted_keys(keys).len() == keys.len(),
        sorted_keys(keys).to_multiset() == keys.to_multiset(),
        sorted_keys(keys).to_set() == keys.to_set(),
        sorted_keys(keys).no_duplicates(),
        vstd::std_specs::btree::increasing_seq(sorted_keys(keys)),
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    lemma_str_leq_total_ordering();
    let leq = |a: String, b: String| str_leq(a, b);
    let s = sorted_keys(keys);
    keys.lemma_sort_by_ensures(leq);
    // Same multiset (permutation) => same length and same element set.
    assert(s.to_multiset() =~= keys.to_multiset());
    s.to_multiset_ensures();
    keys.to_multiset_ensures();
    assert(s.len() == s.to_multiset().len());
    assert(keys.len() == keys.to_multiset().len());
    assert(s.len() == keys.len());
    assert(s.to_set() =~= keys.to_set()) by {
        assert forall|k: String| s.to_set().contains(k) <==> keys.to_set().contains(k) by {
            if s.to_set().contains(k) {
                assert(s.contains(k));
                assert(s.to_multiset().count(k) > 0);
                assert(keys.to_multiset().count(k) > 0);
                assert(keys.contains(k));
            }
            if keys.to_set().contains(k) {
                assert(keys.contains(k));
                assert(keys.to_multiset().count(k) > 0);
                assert(s.to_multiset().count(k) > 0);
                assert(s.contains(k));
            }
        }
    }
    // Distinctness is preserved through the shared multiset.
    keys.lemma_multiset_has_no_duplicates();
    assert(s.no_duplicates()) by {
        s.lemma_multiset_has_no_duplicates_conv();
    }
    // sorted_by + distinct => strict Less on i<j => increasing_seq.
    assert(vstd::relations::sorted_by(s, leq));
    assert(vstd::std_specs::btree::increasing_seq(s)) by {
        assert forall|i: int, j: int| 0 <= i < j < s.len()
            implies #[trigger] s[i].cmp_spec(&s[j]) is Less by {
            assert(leq(s[i], s[j]));
            assert(s[i] != s[j]) by {
                s.lemma_multiset_has_no_duplicates();
            }
            // leq && distinct => strict Less (Equal would force eq_spec, hence ==).
            if s[i].cmp_spec(&s[j]) is Equal {
                axiom_string_concrete_eq();
                reveal(vstd::laws_cmp::obeys_cmp_ord);
                reveal(vstd::laws_eq::obeys_concrete_eq);
                assert(s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Equal));
                reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
                assert(s[i].eq_spec(&s[j]));
                assert(s[i] == s[j]);
                assert(false);
            }
        }
    }
}

/// Two strictly-ascending (`increasing_seq`), distinct key sequences over the
/// same element set are equal. Used to identify the parser's sorted `order@` with
/// the sorted key projection of the executable printer's `BTreeMap::iter()` walk.
pub proof fn lemma_increasing_seq_eq(a: Seq<String>, b: Seq<String>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        vstd::std_specs::btree::increasing_seq(a),
        vstd::std_specs::btree::increasing_seq(b),
        a.to_set() == b.to_set(),
    ensures
        a == b,
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    lemma_str_leq_total_ordering();
    let leq = |a1: String, b1: String| str_leq(a1, b1);
    // Both are `sorted_by(leq)` (strict Less implies leq).
    assert(vstd::relations::sorted_by(a, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < a.len() implies #[trigger] leq(a[i], a[j]) by {
            assert(a[i].cmp_spec(&a[j]) is Less);
        }
    }
    assert(vstd::relations::sorted_by(b, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < b.len() implies #[trigger] leq(b[i], b[j]) by {
            assert(b[i].cmp_spec(&b[j]) is Less);
        }
    }
    // Same set + distinct => same multiset.
    a.lemma_multiset_has_no_duplicates();
    b.lemma_multiset_has_no_duplicates();
    assert(a.to_multiset() =~= b.to_multiset()) by {
        assert forall|x: String| a.to_multiset().count(x) == b.to_multiset().count(x) by {
            a.to_multiset_ensures();
            b.to_multiset_ensures();
            if a.to_set().contains(x) {
                assert(a.contains(x));
                assert(b.contains(x));
            } else {
                assert(!a.contains(x));
                assert(!b.to_set().contains(x));
                assert(!b.contains(x));
            }
        }
    }
    vstd::seq_lib::lemma_sorted_unique(a, b, leq);
}

pub open spec fn view_opt(v: Option<ast::Expression>) -> Option<SExpr> {
    match v {
        Some(e) => Some(view_expr(e)),
        None => None,
    }
}

pub open spec fn view_assign_pairs(items: Seq<(String, Option<ast::Expression>)>)
    -> Seq<(String, Option<SExpr>)> {
    items.map_values(|kv: (String, Option<ast::Expression>)| (kv.0, view_opt(kv.1)))
}

pub proof fn view_assign_pairs_index(items: Seq<(String, Option<ast::Expression>)>)
    ensures
        view_assign_pairs(items).len() == items.len(),
        forall|i: int| 0 <= i < items.len() ==> #[trigger] view_assign_pairs(items)[i]
            == (items[i].0, view_opt(items[i].1)),
{
}

pub proof fn lemma_assign_dom_len(
    m: vstd::map::Map<String, Option<ast::Expression>>,
    items: Seq<(String, Option<ast::Expression>)>,
)
    requires
        m.dom().finite(),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0,
        forall|i: int| 0 <= i < items.len() ==> #[trigger] m.dom().contains(items[i].0),
        forall|k: String| m.dom().contains(k)
            ==> exists|i: int| 0 <= i < items.len() && (#[trigger] items[i]).0 == k,
    ensures
        m.dom().len() == items.len(),
    decreases items.len(),
{
    if items.len() == 0 {
        assert(m.dom() =~= vstd::set::Set::<String>::empty()) by {
            assert forall|k: String| !m.dom().contains(k) by {
                if m.dom().contains(k) {
                    let i = choose|i: int| 0 <= i < items.len() && items[i].0 == k;
                }
            }
        }
    } else {
        let head = items[0];
        let rest = items.drop_first();
        let m2 = m.remove(head.0);
        assert(m.dom().contains(head.0));
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] m2.dom().contains(rest[i].0) by {
            assert(rest[i] == items[i + 1]);
            assert(items[0].0 != items[i + 1].0);
            assert(m.dom().contains(items[i + 1].0));
        }
        assert forall|k: String| m2.dom().contains(k) implies
            exists|i: int| 0 <= i < rest.len() && (#[trigger] rest[i]).0 == k by {
            assert(m.dom().contains(k));
            let i = choose|i: int| 0 <= i < items.len() && items[i].0 == k;
            assert(k != head.0);
            assert(i != 0);
            assert(rest[i - 1] == items[i]);
        }
        lemma_assign_dom_len(m2, rest);
        assert(m.dom().len() == m2.dom().len() + 1) by {
            assert(m.dom().contains(head.0));
            assert(m2.dom() =~= m.dom().remove(head.0));
            assert(m.dom().remove(head.0).len() + 1 == m.dom().len());
        }
    }
}

/// The keys of the parser's ghost `done` sequence.
pub open spec fn done_keys(items: Seq<(String, Option<ast::Expression>)>) -> Seq<String> {
    items.map_values(|kv: (String, Option<ast::Expression>)| kv.0)
}

/// Bijection lemma: under the parser's assignment invariants (distinct keys +
/// key set == map domain), the ghost `order = done_keys(items)` is well-formed
/// (`wf_update`) and reading the map back through `order` reproduces exactly the
/// ordered assignment sequence `view_assign_pairs(items)`.
///
/// This is the Seq <-> Map bijection on the UPDATE assignment set:
///   * soundness    — `order.no_duplicates()` and every listed key is a real
///                    assignment (`order.to_set() subset set.dom()`);
///   * completeness — every assignment is listed (`set.dom() subset
///                    order.to_set()`);
/// together giving `order.to_set() == set.dom()` and, with the value map,
/// `view_update_assigns(set, order) == view_assign_pairs(items)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60000)]
pub proof fn lemma_update_bijection(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    items: Seq<(String, Option<ast::Expression>)>,
)
    requires
        set.dom().finite(),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0,
        forall|i: int| 0 <= i < items.len() ==> #[trigger] set.dom().contains(items[i].0)
            && set[items[i].0] == items[i].1,
        forall|k: String| set.dom().contains(k)
            ==> exists|i: int| 0 <= i < items.len() && (#[trigger] items[i]).0 == k,
    ensures
        wf_update(set, done_keys(items)),
        view_update_assigns(set, done_keys(items)) == view_assign_pairs(items),
{
    let order = done_keys(items);
    assert(order.len() == items.len());
    assert forall|i: int| 0 <= i < order.len() implies #[trigger] order[i] == items[i].0 by {}
    // soundness: no_duplicates.
    assert(order.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len()
            && i != j implies order[i] != order[j] by {
            if i < j {
                assert(items[i].0 != items[j].0);
            } else {
                assert(items[j].0 != items[i].0);
            }
        }
    }
    // order.to_set() == set.dom(), both directions.
    assert(order.to_set() =~= set.dom()) by {
        assert forall|k: String| order.to_set().contains(k) implies set.dom().contains(k) by {
            let i = choose|i: int| 0 <= i < order.len() && order[i] == k;
            assert(order[i] == items[i].0);
            assert(set.dom().contains(items[i].0));
        }
        assert forall|k: String| set.dom().contains(k) implies order.to_set().contains(k) by {
            let i = choose|i: int| 0 <= i < items.len() && items[i].0 == k;
            assert(order[i] == k);
        }
    }
    // value agreement: view_update_assigns(set, order) == view_assign_pairs(items).
    view_assign_pairs_index(items);
    assert(view_update_assigns(set, order) =~= view_assign_pairs(items)) by {
        assert(view_update_assigns(set, order).len() == items.len());
        assert(view_assign_pairs(items).len() == items.len());
        assert forall|i: int| 0 <= i < items.len() implies
            #[trigger] view_update_assigns(set, order)[i] == view_assign_pairs(items)[i] by {
            assert(view_update_assigns(set, order)[i] == (order[i], view_opt(set[order[i]])));
            assert(order[i] == items[i].0);
            assert(set.dom().contains(items[i].0) && set[items[i].0] == items[i].1);
            assert(view_assign_pairs(items)[i] == (items[i].0, view_opt(items[i].1)));
        }
    }
}

/// Boundary lemma used by the verified parser: with `order = done_keys(items)`,
/// the total `view_update_arm` equals the mirror `Update` built from the ordered
/// assignment list. No `len == 1` special case — this now covers multi-assign.
#[verifier::spinoff_prover]
#[verifier::rlimit(60000)]
pub proof fn lemma_update_view_boundary(
    table: String,
    set: vstd::map::Map<String, Option<ast::Expression>>,
    items: Seq<(String, Option<ast::Expression>)>,
    where_clause: Option<ast::Expression>,
)
    requires
        set.dom().finite(),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0,
        forall|i: int| 0 <= i < items.len() ==> #[trigger] set.dom().contains(items[i].0)
            && set[items[i].0] == items[i].1,
        forall|k: String| set.dom().contains(k)
            ==> exists|i: int| 0 <= i < items.len() && (#[trigger] items[i]).0 == k,
    ensures
        view_update_arm(table, set, done_keys(items), where_clause)
            == (SStmt::Update {
                table,
                set: view_assign_pairs(items),
                where_clause: view_opt(where_clause),
            }),
{
    lemma_update_bijection(set, items);
    let order = done_keys(items);
    assert(wf_update(set, order));
    assert(view_update_arm(table, set, order, where_clause)
        == SStmt::Update {
            table,
            set: view_update_assigns(set, order),
            where_clause: view_opt(where_clause),
        });
}

} // verus!
