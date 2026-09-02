//! Minimal-parenthesisation *statement* printer and its roundtrip
//! (Phase 6 of the parser cutover, tasks 3-4).
//!
//! Phase 3 proved the minimal-parenthesisation roundtrip for expressions
//! (`verified_minparen::min_roundtrip` / `min_roundtrip_live`); this module
//! lifts it to whole statements. `sprint_min_stmt` prints a mirror statement
//! (`verified_stmt::SStmt`) as a keyword skeleton whose expression positions
//! are `verified_minparen::sprint_min(e, 0)` — bare precedence syntax, no
//! redundant parentheses — and whose clause lists are per-clause spec printers
//! (select items, FROM join trees, GROUP BY / ORDER BY lists, INSERT rows,
//! CREATE TABLE columns, the UPDATE assignment). The exec twin
//! `print_min_stmt` produces a real `Vec<Token>` whose token view refines it.
//!
//! The headline theorems:
//!
//! - `stmt_min_roundtrip` (spec): for every `printable_stmt` mirror statement,
//!   `sparse_control(sprint_min_stmt(s)) == (Some(s), empty)` — the statement
//!   dispatch twin recovers the statement exactly and consumes every token.
//! - `stmt_min_roundtrip_live` (exec): the production `parse_control_at`
//!   recovers a printable `ast::Statement` from `print_min_stmt(s)` up to
//!   `view_stmt`, consuming every token — lifted through phase 6 task 2's
//!   refinement of the dispatch.
//!
//! Printable domain (`printable_stmt`): every embedded expression is
//! `printable_se`; grammar-mandated one-or-more lists are non-empty (the
//! select list, INSERT rows and row expressions, an INSERT column list when
//! present, CREATE TABLE columns); a `SELECT` alias is never on `*`; a join's
//! right side is a base table and its predicate presence matches the join
//! type (CROSS has none, the others require one); an UPDATE has exactly one
//! assignment (`view_stmt` collapses multi-assignment maps to `Unsupported`);
//! `EXPLAIN` wraps a non-`EXPLAIN` printable statement.

// Proof/verification scaffolding, not idiomatic library code.
#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_expression::{BinaryTag, UnaryTag};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_production::TokenView;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_roundtrip::SExpr;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_stmt::{SColumn, SFrom, SJoinStep, SStmt};
// Ghost (spec/proof) imports, stripped from non-Verus builds.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_minparen::{inert, lemma_min, neutral_head, sprint_min, sprint_min_len};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_precedence::sparse_prec;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::printable_se;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::{apply_step, fold_joins, from_head, from_steps, is_cross};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt_prec::expr_fuel;
#[allow(unused_imports)]
use super::parse_error::ParseError;
#[allow(unused_imports)]
use super::{
    Keyword, Token, ast, verified_control, verified_integer, verified_minparen,
    verified_precedence, verified_production, verified_roundtrip, verified_stmt,
    verified_stmt_prec,
};
#[allow(unused_imports)]
use crate::sql::types::DataType;
#[allow(unused_imports)]
use std::collections::BTreeMap;

verus! {

// ===========================================================================
// Printable domain.
// ===========================================================================

/// An optional expression position is printable when the expression (if any) is.
pub open spec fn printable_opt_se(o: Option<SExpr>) -> bool {
    match o {
        Some(e) => printable_se(e),
        None => true,
    }
}

/// Structural all-printable over a plain expression list (GROUP BY, a VALUES row).
pub open spec fn printable_exprs(items: Seq<SExpr>) -> bool
    decreases items.len(),
{
    if items.len() == 0 {
        true
    } else {
        printable_se(items[0]) && printable_exprs(items.drop_first())
    }
}

/// Select-list items: printable expressions, and no alias on `*` (the parser
/// rejects `SELECT * AS x`).
pub open spec fn printable_select_items(items: Seq<(SExpr, Option<String>)>) -> bool
    decreases items.len(),
{
    if items.len() == 0 {
        true
    } else {
        printable_se(items[0].0)
        && (items[0].1 is Some ==> !(items[0].0 is All))
        && printable_select_items(items.drop_first())
    }
}

/// ORDER BY items: printable expressions (any direction prints).
pub open spec fn printable_order_items(items: Seq<(SExpr, ast::Direction)>) -> bool
    decreases items.len(),
{
    if items.len() == 0 {
        true
    } else {
        printable_se(items[0].0) && printable_order_items(items.drop_first())
    }
}

/// INSERT rows: each row is a non-empty printable expression list.
pub open spec fn printable_rows(rows: Seq<Seq<SExpr>>) -> bool
    decreases rows.len(),
{
    if rows.len() == 0 {
        true
    } else {
        rows[0].len() >= 1 && printable_exprs(rows[0]) && printable_rows(rows.drop_first())
    }
}

/// A CREATE TABLE column: only the DEFAULT expression constrains printability.
pub open spec fn printable_column(c: SColumn) -> bool {
    printable_opt_se(c.default)
}

pub open spec fn printable_columns(cols: Seq<SColumn>) -> bool
    decreases cols.len(),
{
    if cols.len() == 0 {
        true
    } else {
        printable_column(cols[0]) && printable_columns(cols.drop_first())
    }
}

/// One join step: the right side is a base table, and the predicate presence
/// matches the join type (CROSS has none; the others require one).
pub open spec fn printable_step(st: SJoinStep) -> bool {
    (st.right is Table)
    && (if is_cross(st.join_type) {
        st.predicate is None
    } else {
        st.predicate is Some && printable_se(st.predicate->Some_0)
    })
}

pub open spec fn printable_steps(steps: Seq<SJoinStep>) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        printable_step(steps[0]) && printable_steps(steps.drop_first())
    }
}

/// A FROM item: a left-deep join tree whose right children are base tables.
pub open spec fn printable_sfrom(f: SFrom) -> bool
    decreases f,
{
    match f {
        SFrom::Table { .. } => true,
        SFrom::Join { left, right, join_type, predicate } => {
            printable_sfrom(*left)
            && printable_step(SJoinStep { join_type, right: *right, predicate })
        },
    }
}

pub open spec fn printable_froms(fs: Seq<SFrom>) -> bool
    decreases fs.len(),
{
    if fs.len() == 0 {
        true
    } else {
        printable_sfrom(fs[0]) && printable_froms(fs.drop_first())
    }
}

/// The domain of the min-parens statement printer.
pub open spec fn printable_stmt(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Begin { .. } => true,
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::CreateTable { name, columns } => columns.len() >= 1 && printable_columns(columns),
        SStmt::DropTable { .. } => true,
        SStmt::Delete { table, where_clause } => printable_opt_se(where_clause),
        SStmt::Insert { table, columns, values } => {
            (match columns {
                Some(cols) => cols.len() >= 1,
                None => true,
            })
            && values.len() >= 1 && printable_rows(values)
        },
        SStmt::Update { table, set, where_clause } => {
            set.len() == 1 && printable_opt_se(set[0].1) && printable_opt_se(where_clause)
        },
        SStmt::Select { select, from, where_clause, group_by, having, order_by, limit, offset } => {
            select.len() >= 1 && printable_select_items(select)
            && printable_froms(from)
            && printable_opt_se(where_clause)
            && printable_exprs(group_by)
            && printable_opt_se(having)
            && printable_order_items(order_by)
            && printable_opt_se(limit)
            && printable_opt_se(offset)
        },
        SStmt::Explain(inner) => !(*inner is Explain) && printable_stmt(*inner),
        SStmt::Unsupported => false,
    }
}

// ===========================================================================
// The spec printer.
// ===========================================================================

/// Shorthand: a keyword token view.
pub open spec fn kwv(k: Keyword) -> TokenView {
    TokenView::Keyword(k)
}

/// `[AS <ident>]` — the printer always spells an alias with `AS`.
pub open spec fn sprint_alias(alias: Option<String>) -> Seq<TokenView> {
    match alias {
        Some(a) => seq![kwv(Keyword::As), TokenView::Ident(a)],
        None => Seq::empty(),
    }
}

/// Comma-separated `<expr> [AS <ident>]` select items.
pub open spec fn sprint_select_items(items: Seq<(SExpr, Option<String>)>) -> Seq<TokenView>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_min(items[0].0, 0) + sprint_alias(items[0].1)
    } else {
        sprint_min(items[0].0, 0) + sprint_alias(items[0].1) + seq![TokenView::Comma]
            + sprint_select_items(items.drop_first())
    }
}

/// Comma-separated bare expressions (GROUP BY body, a VALUES row body).
pub open spec fn sprint_exprs(items: Seq<SExpr>) -> Seq<TokenView>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_min(items[0], 0)
    } else {
        sprint_min(items[0], 0) + seq![TokenView::Comma] + sprint_exprs(items.drop_first())
    }
}

/// The direction keyword — always printed, so the parse recovers it exactly.
pub open spec fn dir_tok(d: ast::Direction) -> TokenView {
    match d {
        ast::Direction::Ascending => kwv(Keyword::Asc),
        ast::Direction::Descending => kwv(Keyword::Desc),
    }
}

/// Comma-separated `<expr> ASC|DESC` order items.
pub open spec fn sprint_order_items(items: Seq<(SExpr, ast::Direction)>) -> Seq<TokenView>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else if items.len() == 1 {
        sprint_min(items[0].0, 0) + seq![dir_tok(items[0].1)]
    } else {
        sprint_min(items[0].0, 0) + seq![dir_tok(items[0].1)] + seq![TokenView::Comma]
            + sprint_order_items(items.drop_first())
    }
}

/// Optional `KW <expr>` clause (WHERE / HAVING / LIMIT / OFFSET).
pub open spec fn sprint_kw_expr(k: Keyword, o: Option<SExpr>) -> Seq<TokenView> {
    match o {
        Some(e) => seq![kwv(k)] + sprint_min(e, 0),
        None => Seq::empty(),
    }
}

/// Optional `GROUP BY <exprs>` clause (nothing when the list is empty).
pub open spec fn sprint_group_by(items: Seq<SExpr>) -> Seq<TokenView> {
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![kwv(Keyword::Group), kwv(Keyword::By)] + sprint_exprs(items)
    }
}

/// Optional `ORDER BY <items>` clause (nothing when the list is empty).
pub open spec fn sprint_order_by(items: Seq<(SExpr, ast::Direction)>) -> Seq<TokenView> {
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![kwv(Keyword::Order), kwv(Keyword::By)] + sprint_order_items(items)
    }
}

/// A base table `<ident> [AS <ident>]`. (Empty for a non-table, outside the
/// printable domain.)
pub open spec fn sprint_table(f: SFrom) -> Seq<TokenView> {
    match f {
        SFrom::Table { name, alias } => seq![TokenView::Ident(name)] + sprint_alias(alias),
        _ => Seq::empty(),
    }
}

/// The keyword sequence introducing a join: `JOIN`, `CROSS JOIN`, `LEFT JOIN`,
/// `RIGHT JOIN` (no `INNER` / `OUTER` spellings — the parse is identical).
pub open spec fn join_kw_toks(jt: ast::JoinType) -> Seq<TokenView> {
    match jt {
        ast::JoinType::Inner => seq![kwv(Keyword::Join)],
        ast::JoinType::Cross => seq![kwv(Keyword::Cross), kwv(Keyword::Join)],
        ast::JoinType::Left => seq![kwv(Keyword::Left), kwv(Keyword::Join)],
        ast::JoinType::Right => seq![kwv(Keyword::Right), kwv(Keyword::Join)],
    }
}

/// One join step: the join keywords, the right table, and `ON <expr>` unless CROSS.
pub open spec fn sprint_join_step(st: SJoinStep) -> Seq<TokenView> {
    join_kw_toks(st.join_type) + sprint_table(st.right)
        + (match st.predicate {
            Some(e) => seq![kwv(Keyword::On)] + sprint_min(e, 0),
            None => Seq::empty(),
        })
}

pub open spec fn sprint_join_steps(steps: Seq<SJoinStep>) -> Seq<TokenView>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Seq::empty()
    } else {
        sprint_join_step(steps[0]) + sprint_join_steps(steps.drop_first())
    }
}

/// One FROM item: the leftmost base table followed by its join steps (the
/// printer inverts the parser's left-deep fold via `from_head` / `from_steps`).
pub open spec fn sprint_from_item(f: SFrom) -> Seq<TokenView> {
    sprint_table(from_head(f)) + sprint_join_steps(from_steps(f))
}

pub open spec fn sprint_from_items(fs: Seq<SFrom>) -> Seq<TokenView>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else if fs.len() == 1 {
        sprint_from_item(fs[0])
    } else {
        sprint_from_item(fs[0]) + seq![TokenView::Comma] + sprint_from_items(fs.drop_first())
    }
}

/// Optional `FROM <items>` clause (nothing when the list is empty).
pub open spec fn sprint_from_clause(fs: Seq<SFrom>) -> Seq<TokenView> {
    if fs.len() == 0 {
        Seq::empty()
    } else {
        seq![kwv(Keyword::From)] + sprint_from_items(fs)
    }
}

/// The canonical datatype keyword (the parser also accepts aliases; the printer
/// emits the canonical spelling, which maps back to the same `DataType`).
pub open spec fn datatype_tok(dt: DataType) -> TokenView {
    match dt {
        DataType::Boolean => kwv(Keyword::Boolean),
        DataType::Integer => kwv(Keyword::Integer),
        DataType::Float => kwv(Keyword::Float),
        DataType::String => kwv(Keyword::String),
    }
}

/// A column's constraints in canonical order, DEFAULT last (so the DEFAULT
/// expression is always followed by `,` / `)`, never by a constraint keyword).
pub open spec fn sprint_constraints(c: SColumn) -> Seq<TokenView> {
    (if c.primary_key {
        seq![kwv(Keyword::Primary), kwv(Keyword::Key)]
    } else {
        Seq::empty()
    })
    + (match c.nullable {
        Some(true) => seq![kwv(Keyword::Null)],
        Some(false) => seq![kwv(Keyword::Not), kwv(Keyword::Null)],
        None => Seq::empty(),
    })
    + (if c.unique { seq![kwv(Keyword::Unique)] } else { Seq::empty() })
    + (if c.index { seq![kwv(Keyword::Index)] } else { Seq::empty() })
    + (match c.references {
        Some(t) => seq![kwv(Keyword::References), TokenView::Ident(t)],
        None => Seq::empty(),
    })
    + (match c.default {
        Some(e) => seq![kwv(Keyword::Default)] + sprint_min(e, 0),
        None => Seq::empty(),
    })
}

/// `<name> <datatype> <constraint>*`.
pub open spec fn sprint_column(c: SColumn) -> Seq<TokenView> {
    seq![TokenView::Ident(c.name), datatype_tok(c.datatype)] + sprint_constraints(c)
}

pub open spec fn sprint_columns(cols: Seq<SColumn>) -> Seq<TokenView>
    decreases cols.len(),
{
    if cols.len() == 0 {
        Seq::empty()
    } else if cols.len() == 1 {
        sprint_column(cols[0])
    } else {
        sprint_column(cols[0]) + seq![TokenView::Comma] + sprint_columns(cols.drop_first())
    }
}

/// Comma-separated bare identifiers (the INSERT column list body).
pub open spec fn sprint_idents(names: Seq<String>) -> Seq<TokenView>
    decreases names.len(),
{
    if names.len() == 0 {
        Seq::empty()
    } else if names.len() == 1 {
        seq![TokenView::Ident(names[0])]
    } else {
        seq![TokenView::Ident(names[0]), TokenView::Comma] + sprint_idents(names.drop_first())
    }
}

/// One `( <exprs> )` VALUES row.
pub open spec fn sprint_row(row: Seq<SExpr>) -> Seq<TokenView> {
    seq![TokenView::OpenParen] + sprint_exprs(row) + seq![TokenView::CloseParen]
}

pub open spec fn sprint_rows(rows: Seq<Seq<SExpr>>) -> Seq<TokenView>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else if rows.len() == 1 {
        sprint_row(rows[0])
    } else {
        sprint_row(rows[0]) + seq![TokenView::Comma] + sprint_rows(rows.drop_first())
    }
}

/// One UPDATE assignment `<ident> = (DEFAULT | <expr>)`.
pub open spec fn sprint_assign(a: (String, Option<SExpr>)) -> Seq<TokenView> {
    seq![TokenView::Ident(a.0), TokenView::Equal]
        + (match a.1 {
            Some(e) => sprint_min(e, 0),
            None => seq![kwv(Keyword::Default)],
        })
}

/// The BEGIN clause tail (everything after the `BEGIN` keyword).
pub open spec fn sprint_begin_body(read_only: bool, as_of: Option<u64>) -> Seq<TokenView> {
    (if read_only { seq![kwv(Keyword::Read), kwv(Keyword::Only)] } else { Seq::empty() })
    + (match as_of {
        Some(v) => seq![
            kwv(Keyword::As), kwv(Keyword::Of), kwv(Keyword::System), kwv(Keyword::Time),
            TokenView::Number(verified_integer::decimal_digits(v)),
        ],
        None => Seq::empty(),
    })
}

/// The SELECT clause tail (everything after the `SELECT` keyword).
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
    sprint_select_items(select)
    + sprint_from_clause(from)
    + sprint_kw_expr(Keyword::Where, where_clause)
    + sprint_group_by(group_by)
    + sprint_kw_expr(Keyword::Having, having)
    + sprint_order_by(order_by)
    + sprint_kw_expr(Keyword::Limit, limit)
    + sprint_kw_expr(Keyword::Offset, offset)
}

/// The min-parens statement printer: a keyword skeleton whose expression
/// positions are `sprint_min(e, 0)` and whose clause lists are the per-clause
/// printers above.
pub open spec fn sprint_min_stmt(s: SStmt) -> Seq<TokenView>
    decreases s,
{
    match s {
        SStmt::Commit => seq![kwv(Keyword::Commit)],
        SStmt::Rollback => seq![kwv(Keyword::Rollback)],
        SStmt::Begin { read_only, as_of } => {
            seq![kwv(Keyword::Begin)] + sprint_begin_body(read_only, as_of)
        },
        SStmt::DropTable { name, if_exists } => {
            seq![kwv(Keyword::Drop), kwv(Keyword::Table)]
            + (if if_exists { seq![kwv(Keyword::If), kwv(Keyword::Exists)] } else { Seq::empty() })
            + seq![TokenView::Ident(name)]
        },
        SStmt::Delete { table, where_clause } => {
            seq![kwv(Keyword::Delete), kwv(Keyword::From), TokenView::Ident(table)]
                + sprint_kw_expr(Keyword::Where, where_clause)
        },
        SStmt::CreateTable { name, columns } => {
            seq![
                kwv(Keyword::Create), kwv(Keyword::Table), TokenView::Ident(name),
                TokenView::OpenParen,
            ] + sprint_columns(columns) + seq![TokenView::CloseParen]
        },
        SStmt::Insert { table, columns, values } => {
            seq![kwv(Keyword::Insert), kwv(Keyword::Into), TokenView::Ident(table)]
            + (match columns {
                Some(cols) => seq![TokenView::OpenParen] + sprint_idents(cols)
                    + seq![TokenView::CloseParen],
                None => Seq::empty(),
            })
            + seq![kwv(Keyword::Values)] + sprint_rows(values)
        },
        SStmt::Update { table, set, where_clause } => {
            seq![kwv(Keyword::Update), TokenView::Ident(table), kwv(Keyword::Set)]
                + (if set.len() >= 1 { sprint_assign(set[0]) } else { Seq::empty() })
                + sprint_kw_expr(Keyword::Where, where_clause)
        },
        SStmt::Select { select, from, where_clause, group_by, having, order_by, limit, offset } => {
            seq![kwv(Keyword::Select)] + sprint_select_body(
                select, from, where_clause, group_by, having, order_by, limit, offset)
        },
        SStmt::Explain(inner) => seq![kwv(Keyword::Explain)] + sprint_min_stmt(*inner),
        SStmt::Unsupported => Seq::empty(),
    }
}

// ===========================================================================
// Head-token facts.
// ===========================================================================

/// A printed expression never *starts* with a keyword other than the literal /
/// operator keywords (`NULL`, `TRUE`, `FALSE`, `INFINITY`, `NAN`, `NOT`); in
/// particular it never starts with `DEFAULT`, which the UPDATE value grammar
/// checks before trying an expression.
pub proof fn sprint_min_head_not_default(e: SExpr, ctx: u8)
    requires
        printable_se(e),
    ensures
        sprint_min(e, ctx).len() > 0,
        sprint_min(e, ctx)[0] != kwv(Keyword::Default),
    decreases e, 1nat,
{
    reveal_with_fuel(verified_minparen::sprint_min, 1);
    verified_minparen::sprint_min_len(e, ctx);
    verified_minparen::sprint_body_nonempty(e);
    if verified_minparen::prec_min(e) < ctx {
        assert(sprint_min(e, ctx)[0] == TokenView::OpenParen);
    } else {
        assert(sprint_min(e, ctx) == verified_minparen::sprint_body(e));
        sprint_body_head_not_default(e);
    }
}

/// Body form of `sprint_min_head_not_default`.
pub proof fn sprint_body_head_not_default(e: SExpr)
    requires
        printable_se(e),
    ensures
        verified_minparen::sprint_body(e).len() > 0,
        verified_minparen::sprint_body(e)[0] != kwv(Keyword::Default),
    decreases e, 0nat,
{
    reveal_with_fuel(verified_minparen::sprint_body, 1);
    reveal(printable_se);
    reveal(verified_production::literal_views);
    verified_minparen::sprint_body_nonempty(e);
    match e {
        SExpr::All => {},
        SExpr::Column(t, c) => {
            match t {
                None => {},
                Some(_) => {},
            }
        },
        SExpr::Literal(l) => {
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(b) => {
                    if b {
                    } else {
                    }
                },
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Function(name, _) => {},
        SExpr::Unary(tag, inner) => {
            assert(verified_minparen::sprint_body(e)[0] == verified_minparen::pre_tok(tag));
            match tag {
                UnaryTag::Not => {},
                UnaryTag::Identity => {},
                UnaryTag::Negate => {},
            }
        },
        SExpr::Factorial(inner) => {
            sprint_min_head_not_default(*inner, 10);
            assert(verified_minparen::sprint_body(e)[0] == sprint_min(*inner, 10)[0]);
        },
        SExpr::Is(inner, lit) => {
            sprint_min_head_not_default(*inner, 10);
            assert(verified_minparen::sprint_body(e)[0] == sprint_min(*inner, 10)[0]);
        },
        SExpr::Binary(tag, left, right) => {
            let lc = (verified_minparen::bin_prec(tag) + 1 - verified_minparen::bin_assoc(
                tag,
            )) as u8;
            sprint_min_head_not_default(*left, lc);
            assert(verified_minparen::sprint_body(e)[0] == sprint_min(*left, lc)[0]);
        },
    }
}

// ===========================================================================
// Clause roundtrip lemmas. Each parses its printed clause followed by an
// arbitrary continuation `tail` whose head satisfies the clause's stop
// condition, recovering the clause exactly and leaving `tail`.
// ===========================================================================

/// A continuation that can follow a printed expression at context 0 AND stops
/// a comma-separated list: empty, or a non-operator head that is not a comma.
pub open spec fn expr_list_tail(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || (neutral_head(tail[0]) && tail[0] != TokenView::Comma)
}

/// An `expr_list_tail` is inert at level 0.
pub proof fn expr_list_tail_inert(tail: Seq<TokenView>)
    requires
        expr_list_tail(tail),
    ensures
        inert(tail, 0),
{
}

/// GROUP BY / row body: a printed one-or-more expression list parses back.
pub proof fn lemma_exprs_rt(items: Seq<SExpr>, tail: Seq<TokenView>)
    requires
        printable_exprs(items),
        items.len() >= 1,
        expr_list_tail(tail),
    ensures
        verified_stmt_prec::sparse_control_group_list(sprint_exprs(items) + tail)
            == (Some(items), tail),
    decreases items.len(),
{
    let input = sprint_exprs(items) + tail;
    verified_minparen::sprint_min_len(items[0], 0);
    if items.len() == 1 {
        assert(sprint_exprs(items) == sprint_min(items[0], 0));
        expr_list_tail_inert(tail);
        assert(input =~= sprint_min(items[0], 0) + tail);
        lemma_min(items[0], 0, tail, expr_fuel(input));
        assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(items[0]), tail));
        assert(verified_stmt_prec::sparse_control_group_list(input) == (Some(seq![items[0]]), tail));
        assert(seq![items[0]] =~= items);
    } else {
        let rest = items.drop_first();
        let tail1 = seq![TokenView::Comma] + sprint_exprs(rest) + tail;
        assert(input =~= sprint_min(items[0], 0) + tail1);
        assert(inert(tail1, 0)) by {
            assert(tail1[0] == TokenView::Comma);
        }
        lemma_min(items[0], 0, tail1, expr_fuel(input));
        assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(items[0]), tail1));
        assert(tail1[0] == TokenView::Comma);
        assert(tail1.drop_first() =~= sprint_exprs(rest) + tail);
        lemma_exprs_rt(rest, tail);
        assert(verified_stmt_prec::sparse_control_group_list(tail1.drop_first())
            == (Some(rest), tail));
        assert(verified_stmt_prec::sparse_control_group_list(input)
            == (Some(seq![items[0]] + rest), tail));
        assert(seq![items[0]] + rest =~= items);
    }
}

/// Select list: a printed one-or-more `<expr> [AS <ident>]` list parses back.
/// The tail must not look like a (bare-identifier) alias or a comma.
pub proof fn lemma_select_items_rt(items: Seq<(SExpr, Option<String>)>, tail: Seq<TokenView>)
    requires
        printable_select_items(items),
        items.len() >= 1,
        expr_list_tail(tail),
        tail.len() == 0 || (tail[0] != kwv(Keyword::As) && !(tail[0] is Ident)),
    ensures
        verified_stmt_prec::sparse_control_select_list(sprint_select_items(items) + tail)
            == (Some(items), tail),
    decreases items.len(),
{
    let input = sprint_select_items(items) + tail;
    let e = items[0].0;
    let alias = items[0].1;
    verified_minparen::sprint_min_len(e, 0);
    if items.len() == 1 {
        assert(sprint_select_items(items) == sprint_min(e, 0) + sprint_alias(alias));
        match alias {
            Some(a) => {
                let atail = seq![kwv(Keyword::As), TokenView::Ident(a)] + tail;
                assert(input =~= sprint_min(e, 0) + atail);
                assert(inert(atail, 0)) by {
                    assert(atail[0] == kwv(Keyword::As));
                    assert(neutral_head(kwv(Keyword::As)));
                }
                lemma_min(e, 0, atail, expr_fuel(input));
                assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), atail));
                // Alias resolution: `AS <ident>` consumed, alias recovered.
                assert(atail.drop_first() =~= seq![TokenView::Ident(a)] + tail);
                assert((seq![TokenView::Ident(a)] + tail).drop_first() =~= tail);
                assert(verified_stmt_prec::sparse_control_select_alias(e, atail)
                    == Some((Some(a), tail)));
                assert(verified_stmt_prec::sparse_control_select_list(input)
                    == (Some(seq![(e, alias)]), tail));
                assert(seq![(e, alias)] =~= items);
            },
            None => {
                assert(input =~= sprint_min(e, 0) + tail);
                expr_list_tail_inert(tail);
                lemma_min(e, 0, tail, expr_fuel(input));
                assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), tail));
                assert(verified_stmt_prec::sparse_control_select_alias(e, tail)
                    == Some((None::<String>, tail)));
                assert(verified_stmt_prec::sparse_control_select_list(input)
                    == (Some(seq![(e, alias)]), tail));
                assert(seq![(e, alias)] =~= items);
            },
        }
    } else {
        let rest = items.drop_first();
        let rest_toks = sprint_select_items(rest) + tail;
        let comma_rest = seq![TokenView::Comma] + rest_toks;
        match alias {
            Some(a) => {
                let atail = seq![kwv(Keyword::As), TokenView::Ident(a)] + comma_rest;
                assert(input =~= sprint_min(e, 0) + atail);
                assert(inert(atail, 0)) by {
                    assert(atail[0] == kwv(Keyword::As));
                    assert(neutral_head(kwv(Keyword::As)));
                }
                lemma_min(e, 0, atail, expr_fuel(input));
                assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), atail));
                assert(atail.drop_first() =~= seq![TokenView::Ident(a)] + comma_rest);
                assert((seq![TokenView::Ident(a)] + comma_rest).drop_first() =~= comma_rest);
                assert(verified_stmt_prec::sparse_control_select_alias(e, atail)
                    == Some((Some(a), comma_rest)));
                assert(comma_rest[0] == TokenView::Comma);
                assert(comma_rest.drop_first() =~= rest_toks);
                lemma_select_items_rt(rest, tail);
                assert(verified_stmt_prec::sparse_control_select_list(rest_toks)
                    == (Some(rest), tail));
                assert(verified_stmt_prec::sparse_control_select_list(input)
                    == (Some(seq![(e, alias)] + rest), tail));
                assert(seq![(e, alias)] + rest =~= items);
            },
            None => {
                assert(input =~= sprint_min(e, 0) + comma_rest);
                assert(inert(comma_rest, 0)) by {
                    assert(comma_rest[0] == TokenView::Comma);
                }
                lemma_min(e, 0, comma_rest, expr_fuel(input));
                assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), comma_rest));
                assert(verified_stmt_prec::sparse_control_select_alias(e, comma_rest)
                    == Some((None::<String>, comma_rest)));
                assert(comma_rest.drop_first() =~= rest_toks);
                lemma_select_items_rt(rest, tail);
                assert(verified_stmt_prec::sparse_control_select_list(input)
                    == (Some(seq![(e, alias)] + rest), tail));
                assert(seq![(e, alias)] + rest =~= items);
            },
        }
    }
}

/// ORDER BY list: a printed one-or-more `<expr> ASC|DESC` list parses back.
pub proof fn lemma_order_items_rt(items: Seq<(SExpr, ast::Direction)>, tail: Seq<TokenView>)
    requires
        printable_order_items(items),
        items.len() >= 1,
        expr_list_tail(tail),
    ensures
        verified_stmt_prec::sparse_control_order_list(sprint_order_items(items) + tail)
            == (Some(items), tail),
    decreases items.len(),
{
    let input = sprint_order_items(items) + tail;
    let e = items[0].0;
    let d = items[0].1;
    verified_minparen::sprint_min_len(e, 0);
    assert(neutral_head(dir_tok(d))) by {
        match d {
            ast::Direction::Ascending => {},
            ast::Direction::Descending => {},
        }
    }
    if items.len() == 1 {
        let dtail = seq![dir_tok(d)] + tail;
        assert(input =~= sprint_min(e, 0) + dtail);
        assert(inert(dtail, 0)) by {
            assert(dtail[0] == dir_tok(d));
        }
        lemma_min(e, 0, dtail, expr_fuel(input));
        assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), dtail));
        assert(dtail.drop_first() =~= tail);
        // Direction resolution and no trailing comma.
        match d {
            ast::Direction::Ascending => {
                assert(dtail[0] == kwv(Keyword::Asc));
            },
            ast::Direction::Descending => {
                assert(dtail[0] == kwv(Keyword::Desc));
                assert(dtail[0] != kwv(Keyword::Asc));
            },
        }
        assert(verified_stmt_prec::sparse_control_order_list(input) == (Some(seq![(e, d)]), tail));
        assert(seq![(e, d)] =~= items);
    } else {
        let rest = items.drop_first();
        let rest_toks = sprint_order_items(rest) + tail;
        let comma_rest = seq![TokenView::Comma] + rest_toks;
        let dtail = seq![dir_tok(d)] + comma_rest;
        assert(input =~= sprint_min(e, 0) + dtail);
        assert(inert(dtail, 0)) by {
            assert(dtail[0] == dir_tok(d));
        }
        lemma_min(e, 0, dtail, expr_fuel(input));
        assert(sparse_prec(input, 0, expr_fuel(input)) == (Some(e), dtail));
        assert(dtail.drop_first() =~= comma_rest);
        match d {
            ast::Direction::Ascending => {
                assert(dtail[0] == kwv(Keyword::Asc));
            },
            ast::Direction::Descending => {
                assert(dtail[0] == kwv(Keyword::Desc));
                assert(dtail[0] != kwv(Keyword::Asc));
            },
        }
        assert(comma_rest[0] == TokenView::Comma);
        assert(comma_rest.drop_first() =~= rest_toks);
        lemma_order_items_rt(rest, tail);
        assert(verified_stmt_prec::sparse_control_order_list(input)
            == (Some(seq![(e, d)] + rest), tail));
        assert(seq![(e, d)] + rest =~= items);
    }
}

/// INSERT column-name list: a printed one-or-more bare-identifier list parses back.
pub proof fn lemma_idents_rt(names: Seq<String>, tail: Seq<TokenView>)
    requires
        names.len() >= 1,
        tail.len() == 0 || tail[0] != TokenView::Comma,
    ensures
        verified_stmt_prec::sparse_control_ident_list(sprint_idents(names) + tail)
            == (Some(names), tail),
    decreases names.len(),
{
    let input = sprint_idents(names) + tail;
    if names.len() == 1 {
        assert(input =~= seq![TokenView::Ident(names[0])] + tail);
        assert(input[0] == TokenView::Ident(names[0]));
        assert(input.drop_first() =~= tail);
        assert(verified_stmt_prec::sparse_control_ident_list(input) == (Some(seq![names[0]]), tail));
        assert(seq![names[0]] =~= names);
    } else {
        let rest = names.drop_first();
        let rest_toks = sprint_idents(rest) + tail;
        assert(input =~= seq![TokenView::Ident(names[0]), TokenView::Comma] + rest_toks);
        assert(input[0] == TokenView::Ident(names[0]));
        assert(input.drop_first() =~= seq![TokenView::Comma] + rest_toks);
        assert(input.drop_first()[0] == TokenView::Comma);
        assert(input.drop_first().drop_first() =~= rest_toks);
        lemma_idents_rt(rest, tail);
        assert(verified_stmt_prec::sparse_control_ident_list(input)
            == (Some(seq![names[0]] + rest), tail));
        assert(seq![names[0]] + rest =~= names);
    }
}

/// One VALUES row `( <exprs> )` parses back, leaving the continuation untouched.
pub proof fn lemma_row_rt(row: Seq<SExpr>, tail: Seq<TokenView>)
    requires
        printable_exprs(row),
        row.len() >= 1,
    ensures
        verified_stmt_prec::sparse_control_row(sprint_row(row) + tail) == (Some(row), tail),
{
    let input = sprint_row(row) + tail;
    let close_tail = seq![TokenView::CloseParen] + tail;
    assert(input =~= seq![TokenView::OpenParen] + (sprint_exprs(row) + close_tail));
    assert(input[0] == TokenView::OpenParen);
    assert(input.drop_first() =~= sprint_exprs(row) + close_tail);
    assert(expr_list_tail(close_tail)) by {
        assert(close_tail[0] == TokenView::CloseParen);
        assert(neutral_head(TokenView::CloseParen));
    }
    lemma_exprs_rt(row, close_tail);
    assert(verified_stmt_prec::sparse_control_group_list(sprint_exprs(row) + close_tail)
        == (Some(row), close_tail));
    assert(close_tail[0] == TokenView::CloseParen);
    assert(close_tail.drop_first() =~= tail);
}

/// The VALUES body: a printed one-or-more row list parses back.
pub proof fn lemma_rows_rt(rows: Seq<Seq<SExpr>>, tail: Seq<TokenView>)
    requires
        printable_rows(rows),
        rows.len() >= 1,
        tail.len() == 0 || tail[0] != TokenView::Comma,
    ensures
        verified_stmt_prec::sparse_control_values(sprint_rows(rows) + tail) == (Some(rows), tail),
    decreases rows.len(),
{
    let input = sprint_rows(rows) + tail;
    if rows.len() == 1 {
        assert(input =~= sprint_row(rows[0]) + tail);
        lemma_row_rt(rows[0], tail);
        assert(verified_stmt_prec::sparse_control_row(input) == (Some(rows[0]), tail));
        assert(verified_stmt_prec::sparse_control_values(input) == (Some(seq![rows[0]]), tail));
        assert(seq![rows[0]] =~= rows);
    } else {
        let rest = rows.drop_first();
        let rest_toks = sprint_rows(rest) + tail;
        let comma_rest = seq![TokenView::Comma] + rest_toks;
        assert(input =~= sprint_row(rows[0]) + comma_rest);
        lemma_row_rt(rows[0], comma_rest);
        assert(verified_stmt_prec::sparse_control_row(input) == (Some(rows[0]), comma_rest));
        assert(comma_rest[0] == TokenView::Comma);
        assert(comma_rest.drop_first() =~= rest_toks);
        lemma_rows_rt(rest, tail);
        assert(verified_stmt_prec::sparse_control_values(input)
            == (Some(seq![rows[0]] + rest), tail));
        assert(seq![rows[0]] + rest =~= rows);
    }
}

// ---- CREATE TABLE columns --------------------------------------------------

/// A continuation that ends a column definition: empty, `,`, or `)` (the
/// constraint loop stops at the first non-keyword token).
pub open spec fn col_tail(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || tail[0] == TokenView::Comma || tail[0] == TokenView::CloseParen
}

/// One-step unfold: `PRIMARY KEY` folds into the accumulator.
proof fn lemma_colc_pk(t1: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Primary), kwv(Keyword::Key)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { primary_key: true, ..acc }),
{
    let input = seq![kwv(Keyword::Primary), kwv(Keyword::Key)] + t1;
    assert(input[0] == kwv(Keyword::Primary));
    assert(input.drop_first() =~= seq![kwv(Keyword::Key)] + t1);
    assert(input.drop_first()[0] == kwv(Keyword::Key));
    assert(input.drop_first().drop_first() =~= t1);
}

/// One-step unfold: `NULL` folds into the accumulator.
proof fn lemma_colc_null(t1: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    requires
        acc.nullable is None,
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Null)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { nullable: Some(true), ..acc }),
{
    let input = seq![kwv(Keyword::Null)] + t1;
    assert(input[0] == kwv(Keyword::Null));
    assert(input.drop_first() =~= t1);
}

/// One-step unfold: `NOT NULL` folds into the accumulator.
proof fn lemma_colc_notnull(t1: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    requires
        acc.nullable is None,
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Not), kwv(Keyword::Null)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { nullable: Some(false), ..acc }),
{
    let input = seq![kwv(Keyword::Not), kwv(Keyword::Null)] + t1;
    assert(input[0] == kwv(Keyword::Not));
    assert(input.drop_first() =~= seq![kwv(Keyword::Null)] + t1);
    assert(input.drop_first()[0] == kwv(Keyword::Null));
    assert(input.drop_first().drop_first() =~= t1);
}

/// One-step unfold: `UNIQUE` folds into the accumulator.
proof fn lemma_colc_unique(t1: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Unique)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { unique: true, ..acc }),
{
    let input = seq![kwv(Keyword::Unique)] + t1;
    assert(input[0] == kwv(Keyword::Unique));
    assert(input.drop_first() =~= t1);
}

/// One-step unfold: `INDEX` folds into the accumulator.
proof fn lemma_colc_index(t1: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Index)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { index: true, ..acc }),
{
    let input = seq![kwv(Keyword::Index)] + t1;
    assert(input[0] == kwv(Keyword::Index));
    assert(input.drop_first() =~= t1);
}

/// One-step unfold: `REFERENCES <ident>` folds into the accumulator.
proof fn lemma_colc_refs(
    rname: String,
    t1: Seq<TokenView>,
    name: String,
    dt: DataType,
    acc: verified_stmt_prec::ColAcc,
)
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::References), TokenView::Ident(rname)] + t1, name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                t1, name, dt, verified_stmt_prec::ColAcc { references: Some(rname), ..acc }),
{
    let input = seq![kwv(Keyword::References), TokenView::Ident(rname)] + t1;
    assert(input[0] == kwv(Keyword::References));
    assert(input.drop_first() =~= seq![TokenView::Ident(rname)] + t1);
    assert(input.drop_first()[0] == TokenView::Ident(rname));
    assert(input.drop_first().drop_first() =~= t1);
}

/// One-step unfold: `DEFAULT <expr>` parses the expression (min-parens) and
/// folds it into the accumulator.
proof fn lemma_colc_default(
    e: SExpr,
    tail: Seq<TokenView>,
    name: String,
    dt: DataType,
    acc: verified_stmt_prec::ColAcc,
)
    requires
        printable_se(e),
        inert(tail, 0),
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            seq![kwv(Keyword::Default)] + (sprint_min(e, 0) + tail), name, dt, acc)
            == verified_stmt_prec::sparse_control_col_constraints(
                tail, name, dt, verified_stmt_prec::ColAcc { default: Some(e), ..acc }),
{
    let input = seq![kwv(Keyword::Default)] + (sprint_min(e, 0) + tail);
    assert(input[0] == kwv(Keyword::Default));
    let e_in = input.drop_first();
    assert(e_in =~= sprint_min(e, 0) + tail);
    verified_minparen::sprint_min_len(e, 0);
    lemma_min(e, 0, tail, expr_fuel(e_in));
    assert(sparse_prec(e_in, 0, expr_fuel(e_in)) == (Some(e), tail));
}

/// The constraint loop stops at a non-keyword tail, yielding the accumulated
/// column.
proof fn lemma_colc_stop(tail: Seq<TokenView>, name: String, dt: DataType, acc: verified_stmt_prec::ColAcc)
    requires
        col_tail(tail),
    ensures
        verified_stmt_prec::sparse_control_col_constraints(tail, name, dt, acc)
            == (Some(verified_stmt_prec::col_from_acc(name, dt, acc)), tail),
{
}

/// The printed constraint chain parses from the empty accumulator back to the
/// column, stopping at the tail. The printer's canonical order (PRIMARY KEY,
/// NULL/NOT NULL, UNIQUE, INDEX, REFERENCES, DEFAULT) is one of the arbitrary
/// orders the any-order constraint loop accepts.
#[verifier::spinoff_prover]
#[verifier::rlimit(200000)]
pub proof fn lemma_constraints_rt(c: SColumn, tail: Seq<TokenView>)
    requires
        printable_column(c),
        col_tail(tail),
    ensures
        verified_stmt_prec::sparse_control_col_constraints(
            sprint_constraints(c) + tail,
            c.name,
            c.datatype,
            verified_stmt_prec::col_acc_empty(),
        ) == (Some(c), tail),
{
    let name = c.name;
    let dt = c.datatype;
    let s_pk: Seq<TokenView> = if c.primary_key {
        seq![kwv(Keyword::Primary), kwv(Keyword::Key)]
    } else {
        Seq::empty()
    };
    let s_null: Seq<TokenView> = match c.nullable {
        Some(true) => seq![kwv(Keyword::Null)],
        Some(false) => seq![kwv(Keyword::Not), kwv(Keyword::Null)],
        None => Seq::empty(),
    };
    let s_uni: Seq<TokenView> = if c.unique { seq![kwv(Keyword::Unique)] } else { Seq::empty() };
    let s_idx: Seq<TokenView> = if c.index { seq![kwv(Keyword::Index)] } else { Seq::empty() };
    let s_ref: Seq<TokenView> = match c.references {
        Some(rname) => seq![kwv(Keyword::References), TokenView::Ident(rname)],
        None => Seq::empty(),
    };
    let s_def: Seq<TokenView> = match c.default {
        Some(e) => seq![kwv(Keyword::Default)] + sprint_min(e, 0),
        None => Seq::empty(),
    };
    let t5 = s_def + tail;
    let t4 = s_ref + t5;
    let t3 = s_idx + t4;
    let t2 = s_uni + t3;
    let t1 = s_null + t2;
    let t0 = s_pk + t1;
    assert(sprint_constraints(c) + tail =~= t0);
    let acc0 = verified_stmt_prec::col_acc_empty();
    let acc1 = verified_stmt_prec::ColAcc { primary_key: c.primary_key, ..acc0 };
    let acc2 = verified_stmt_prec::ColAcc { nullable: c.nullable, ..acc1 };
    let acc3 = verified_stmt_prec::ColAcc { unique: c.unique, ..acc2 };
    let acc4 = verified_stmt_prec::ColAcc { index: c.index, ..acc3 };
    let acc5 = verified_stmt_prec::ColAcc { references: c.references, ..acc4 };
    let acc6 = verified_stmt_prec::ColAcc { default: c.default, ..acc5 };

    // PRIMARY KEY.
    if c.primary_key {
        assert(t0 =~= seq![kwv(Keyword::Primary), kwv(Keyword::Key)] + t1);
        lemma_colc_pk(t1, name, dt, acc0);
        assert(acc1 == verified_stmt_prec::ColAcc { primary_key: true, ..acc0 });
        assert(verified_stmt_prec::sparse_control_col_constraints(t0, name, dt, acc0)
            == verified_stmt_prec::sparse_control_col_constraints(t1, name, dt, acc1));
    } else {
        assert(t0 =~= t1);
        assert(acc1 == acc0);
    }

    // NULL / NOT NULL.
    match c.nullable {
        Some(b) => {
            assert(acc1.nullable is None);
            if b {
                assert(t1 =~= seq![kwv(Keyword::Null)] + t2);
                lemma_colc_null(t2, name, dt, acc1);
                assert(acc2 == verified_stmt_prec::ColAcc { nullable: Some(true), ..acc1 });
            } else {
                assert(t1 =~= seq![kwv(Keyword::Not), kwv(Keyword::Null)] + t2);
                lemma_colc_notnull(t2, name, dt, acc1);
                assert(acc2 == verified_stmt_prec::ColAcc { nullable: Some(false), ..acc1 });
            }
            assert(verified_stmt_prec::sparse_control_col_constraints(t1, name, dt, acc1)
                == verified_stmt_prec::sparse_control_col_constraints(t2, name, dt, acc2));
        },
        None => {
            assert(t1 =~= t2);
            assert(acc2 == acc1);
        },
    }

    // UNIQUE.
    if c.unique {
        assert(t2 =~= seq![kwv(Keyword::Unique)] + t3);
        lemma_colc_unique(t3, name, dt, acc2);
        assert(acc3 == verified_stmt_prec::ColAcc { unique: true, ..acc2 });
        assert(verified_stmt_prec::sparse_control_col_constraints(t2, name, dt, acc2)
            == verified_stmt_prec::sparse_control_col_constraints(t3, name, dt, acc3));
    } else {
        assert(t2 =~= t3);
        assert(acc3 == acc2);
    }

    // INDEX.
    if c.index {
        assert(t3 =~= seq![kwv(Keyword::Index)] + t4);
        lemma_colc_index(t4, name, dt, acc3);
        assert(acc4 == verified_stmt_prec::ColAcc { index: true, ..acc3 });
        assert(verified_stmt_prec::sparse_control_col_constraints(t3, name, dt, acc3)
            == verified_stmt_prec::sparse_control_col_constraints(t4, name, dt, acc4));
    } else {
        assert(t3 =~= t4);
        assert(acc4 == acc3);
    }

    // REFERENCES <ident>.
    match c.references {
        Some(rname) => {
            assert(t4 =~= seq![kwv(Keyword::References), TokenView::Ident(rname)] + t5);
            lemma_colc_refs(rname, t5, name, dt, acc4);
            assert(acc5 == verified_stmt_prec::ColAcc { references: Some(rname), ..acc4 });
            assert(verified_stmt_prec::sparse_control_col_constraints(t4, name, dt, acc4)
                == verified_stmt_prec::sparse_control_col_constraints(t5, name, dt, acc5));
        },
        None => {
            assert(t4 =~= t5);
            assert(acc5 == acc4);
        },
    }

    // DEFAULT <expr>.
    match c.default {
        Some(e) => {
            assert(t5 =~= seq![kwv(Keyword::Default)] + (sprint_min(e, 0) + tail));
            assert(inert(tail, 0)) by {
                if tail.len() > 0 {
                    assert(tail[0] == TokenView::Comma || tail[0] == TokenView::CloseParen);
                }
            }
            lemma_colc_default(e, tail, name, dt, acc5);
            assert(acc6 == verified_stmt_prec::ColAcc { default: Some(e), ..acc5 });
            assert(verified_stmt_prec::sparse_control_col_constraints(t5, name, dt, acc5)
                == verified_stmt_prec::sparse_control_col_constraints(tail, name, dt, acc6));
        },
        None => {
            assert(t5 =~= tail);
            assert(acc6 == acc5);
        },
    }

    // Stop at the tail (empty or a non-keyword `,` / `)`).
    lemma_colc_stop(tail, name, dt, acc6);
    assert(verified_stmt_prec::col_from_acc(name, dt, acc6) == c);
}

/// One printed column `<name> <datatype> <constraint>*` parses back.
pub proof fn lemma_column_rt(c: SColumn, tail: Seq<TokenView>)
    requires
        printable_column(c),
        col_tail(tail),
    ensures
        verified_stmt_prec::sparse_control_column(sprint_column(c) + tail) == (Some(c), tail),
{
    let input = sprint_column(c) + tail;
    assert(input =~= seq![TokenView::Ident(c.name)]
        + (seq![datatype_tok(c.datatype)] + (sprint_constraints(c) + tail)));
    assert(input[0] == TokenView::Ident(c.name));
    let r0 = input.drop_first();
    assert(r0 =~= seq![datatype_tok(c.datatype)] + (sprint_constraints(c) + tail));
    assert(r0[0] == datatype_tok(c.datatype));
    assert(verified_stmt_prec::parse_column_datatype_kw(datatype_tok(c.datatype))
        == Some(c.datatype)) by {
        match c.datatype {
            DataType::Boolean => {},
            DataType::Integer => {},
            DataType::Float => {},
            DataType::String => {},
        }
    }
    let r1 = r0.drop_first();
    assert(r1 =~= sprint_constraints(c) + tail);
    lemma_constraints_rt(c, tail);
    assert(verified_stmt_prec::sparse_control_col_constraints(
        r1, c.name, c.datatype, verified_stmt_prec::col_acc_empty()) == (Some(c), tail));
}

/// The printed one-or-more column list parses back.
pub proof fn lemma_columns_rt(cols: Seq<SColumn>, tail: Seq<TokenView>)
    requires
        printable_columns(cols),
        cols.len() >= 1,
        tail.len() == 0 || tail[0] == TokenView::CloseParen,
    ensures
        verified_stmt_prec::sparse_control_column_list(sprint_columns(cols) + tail)
            == (Some(cols), tail),
    decreases cols.len(),
{
    let input = sprint_columns(cols) + tail;
    if cols.len() == 1 {
        assert(input =~= sprint_column(cols[0]) + tail);
        lemma_column_rt(cols[0], tail);
        assert(verified_stmt_prec::sparse_control_column(input) == (Some(cols[0]), tail));
        assert(verified_stmt_prec::sparse_control_column_list(input) == (Some(seq![cols[0]]), tail));
        assert(seq![cols[0]] =~= cols);
    } else {
        let rest = cols.drop_first();
        let rest_toks = sprint_columns(rest) + tail;
        let comma_rest = seq![TokenView::Comma] + rest_toks;
        assert(input =~= sprint_column(cols[0]) + comma_rest);
        lemma_column_rt(cols[0], comma_rest);
        assert(verified_stmt_prec::sparse_control_column(input) == (Some(cols[0]), comma_rest));
        assert(comma_rest[0] == TokenView::Comma);
        assert(comma_rest.drop_first() =~= rest_toks);
        lemma_columns_rt(rest, tail);
        assert(verified_stmt_prec::sparse_control_column_list(input)
            == (Some(seq![cols[0]] + rest), tail));
        assert(seq![cols[0]] + rest =~= cols);
    }
}

// ---- FROM join trees --------------------------------------------------------

/// The leftmost leaf of any `SFrom` tree is a base table.
pub proof fn lemma_from_head_is_table(f: SFrom)
    ensures
        from_head(f) is Table,
    decreases f,
{
    match f {
        SFrom::Table { .. } => {},
        SFrom::Join { left, .. } => {
            lemma_from_head_is_table(*left);
        },
    }
}

/// `fold_joins` peels an appended step: `fold(h, steps ++ [st]) ==
/// apply_step(fold(h, steps), st)`.
pub proof fn lemma_fold_append(head: SFrom, steps: Seq<SJoinStep>, st: SJoinStep)
    ensures
        fold_joins(head, steps + seq![st]) == apply_step(fold_joins(head, steps), st),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(steps + seq![st] =~= seq![st]);
        assert(seq![st].drop_first() =~= Seq::<SJoinStep>::empty());
        assert(fold_joins(head, seq![st]) == fold_joins(apply_step(head, st), seq![st].drop_first()));
    } else {
        assert((steps + seq![st])[0] == steps[0]);
        assert((steps + seq![st]).drop_first() =~= steps.drop_first() + seq![st]);
        lemma_fold_append(apply_step(head, steps[0]), steps.drop_first(), st);
    }
}

/// `from_head` / `from_steps` invert the fold: every tree is its head folded
/// through its steps.
pub proof fn lemma_fold_head_steps(f: SFrom)
    ensures
        fold_joins(from_head(f), from_steps(f)) == f,
    decreases f,
{
    match f {
        SFrom::Table { .. } => {
            assert(from_steps(f) =~= Seq::<SJoinStep>::empty());
        },
        SFrom::Join { left, right, join_type, predicate } => {
            lemma_fold_head_steps(*left);
            let st = SJoinStep { join_type, right: *right, predicate };
            assert(from_steps(f) =~= from_steps(*left) + seq![st]);
            lemma_fold_append(from_head(*left), from_steps(*left), st);
            assert(from_head(f) == from_head(*left));
            assert(apply_step(*left, st) == f);
        },
    }
}

/// `printable_steps` distributes over append.
pub proof fn lemma_printable_steps_append(a: Seq<SJoinStep>, b: Seq<SJoinStep>)
    requires
        printable_steps(a),
        printable_steps(b),
    ensures
        printable_steps(a + b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_printable_steps_append(a.drop_first(), b);
    }
}

/// A printable tree's step decomposition is printable.
pub proof fn lemma_steps_printable(f: SFrom)
    requires
        printable_sfrom(f),
    ensures
        printable_steps(from_steps(f)),
    decreases f,
{
    match f {
        SFrom::Table { .. } => {
            assert(from_steps(f) =~= Seq::<SJoinStep>::empty());
        },
        SFrom::Join { left, right, join_type, predicate } => {
            lemma_steps_printable(*left);
            let st = SJoinStep { join_type, right: *right, predicate };
            assert(printable_step(st));
            assert(printable_steps(seq![st])) by {
                assert(seq![st][0] == st);
                assert(seq![st].drop_first() =~= Seq::<SJoinStep>::empty());
                assert(printable_steps(seq![st].drop_first()));
            }
            lemma_printable_steps_append(from_steps(*left), seq![st]);
            assert(from_steps(f) =~= from_steps(*left) + seq![st]);
        },
    }
}

/// A continuation that can follow a printed base table when its alias may be
/// absent: never `AS` or a bare identifier (which the alias grammar would eat).
pub open spec fn table_tail(rest: Seq<TokenView>) -> bool {
    rest.len() == 0 || (rest[0] != kwv(Keyword::As) && !(rest[0] is Ident))
}

/// A printed base table `<ident> [AS <ident>]` parses back.
pub proof fn lemma_from_table_rt(f: SFrom, rest: Seq<TokenView>)
    requires
        f is Table,
        table_tail(rest),
    ensures
        verified_stmt_prec::sparse_control_from_table(sprint_table(f) + rest) == (Some(f), rest),
{
    match f {
        SFrom::Table { name, alias } => {
            let input = sprint_table(f) + rest;
            match alias {
                Some(a) => {
                    assert(input =~= seq![TokenView::Ident(name)]
                        + (seq![kwv(Keyword::As), TokenView::Ident(a)] + rest));
                    assert(input[0] == TokenView::Ident(name));
                    let r = input.drop_first();
                    assert(r =~= seq![kwv(Keyword::As), TokenView::Ident(a)] + rest);
                    assert(r[0] == kwv(Keyword::As));
                    let r1 = r.drop_first();
                    assert(r1 =~= seq![TokenView::Ident(a)] + rest);
                    assert(r1[0] == TokenView::Ident(a));
                    assert(r1.drop_first() =~= rest);
                },
                None => {
                    assert(input =~= seq![TokenView::Ident(name)] + rest);
                    assert(input[0] == TokenView::Ident(name));
                    assert(input.drop_first() =~= rest);
                },
            }
        },
        _ => {},
    }
}

/// A continuation that can follow a printed join step: a non-operator head
/// that is not `AS` / an identifier (for the right table's absent alias).
pub open spec fn step_tail(rest: Seq<TokenView>) -> bool {
    rest.len() == 0 || (neutral_head(rest[0]) && rest[0] != kwv(Keyword::As) && !(rest[0] is Ident))
}

/// The head of a printed join step is a join keyword (and thus a neutral,
/// non-alias head for the preceding table / step).
pub proof fn lemma_join_step_head(st: SJoinStep)
    ensures
        sprint_join_step(st).len() > 0,
        verified_stmt_prec::is_join_start(sprint_join_step(st)),
        neutral_head(sprint_join_step(st)[0]),
        sprint_join_step(st)[0] != kwv(Keyword::As),
        !(sprint_join_step(st)[0] is Ident),
        sprint_join_step(st)[0] != TokenView::Comma,
    decreases st,
{
    match st.join_type {
        ast::JoinType::Inner => {
            assert(sprint_join_step(st)[0] == kwv(Keyword::Join));
        },
        ast::JoinType::Cross => {
            assert(sprint_join_step(st)[0] == kwv(Keyword::Cross));
        },
        ast::JoinType::Left => {
            assert(sprint_join_step(st)[0] == kwv(Keyword::Left));
        },
        ast::JoinType::Right => {
            assert(sprint_join_step(st)[0] == kwv(Keyword::Right));
        },
    }
}

/// One printed join step parses back.
#[verifier::spinoff_prover]
#[verifier::rlimit(600000)]
pub proof fn lemma_join_step_rt(st: SJoinStep, rest: Seq<TokenView>)
    requires
        printable_step(st),
        step_tail(rest),
    ensures
        verified_stmt_prec::sparse_control_from_step(sprint_join_step(st) + rest)
            == Some((st, rest)),
{
    let input = sprint_join_step(st) + rest;
    let jt = st.join_type;
    let on_part: Seq<TokenView> = match st.predicate {
        Some(e) => seq![kwv(Keyword::On)] + sprint_min(e, 0),
        None => Seq::empty(),
    };
    let tbl_rest = on_part + rest;
    let after_kw = sprint_table(st.right) + tbl_rest;
    assert(input =~= join_kw_toks(jt) + after_kw);
    // The join keyword sequence resolves to the join type.
    match jt {
        ast::JoinType::Inner => {
            assert(input[0] == kwv(Keyword::Join));
            assert(input.drop_first() =~= after_kw);
            assert(verified_stmt_prec::sparse_control_join_head(input)
                == Some((ast::JoinType::Inner, true, after_kw)));
        },
        ast::JoinType::Cross => {
            assert(input[0] == kwv(Keyword::Cross));
            assert(input.drop_first() =~= seq![kwv(Keyword::Join)] + after_kw);
            assert(input.drop_first()[0] == kwv(Keyword::Join));
            assert(input.drop_first().drop_first() =~= after_kw);
            assert(verified_stmt_prec::sparse_control_join_head(input)
                == Some((ast::JoinType::Cross, false, after_kw)));
        },
        ast::JoinType::Left => {
            assert(input[0] == kwv(Keyword::Left));
            assert(input.drop_first() =~= seq![kwv(Keyword::Join)] + after_kw);
            assert(input.drop_first()[0] == kwv(Keyword::Join));
            assert(input.drop_first()[0] != kwv(Keyword::Outer));
            assert(input.drop_first().drop_first() =~= after_kw);
            assert(verified_stmt_prec::sparse_control_join_head(input)
                == Some((ast::JoinType::Left, true, after_kw)));
        },
        ast::JoinType::Right => {
            assert(input[0] == kwv(Keyword::Right));
            assert(input.drop_first() =~= seq![kwv(Keyword::Join)] + after_kw);
            assert(input.drop_first()[0] == kwv(Keyword::Join));
            assert(input.drop_first()[0] != kwv(Keyword::Outer));
            assert(input.drop_first().drop_first() =~= after_kw);
            assert(verified_stmt_prec::sparse_control_join_head(input)
                == Some((ast::JoinType::Right, true, after_kw)));
        },
    }
    // The right table.
    assert(table_tail(tbl_rest)) by {
        match st.predicate {
            Some(e) => {
                assert(tbl_rest[0] == kwv(Keyword::On));
            },
            None => {
                assert(tbl_rest =~= rest);
            },
        }
    }
    lemma_from_table_rt(st.right, tbl_rest);
    assert(verified_stmt_prec::sparse_control_from_table(after_kw) == (Some(st.right), tbl_rest));
    // The ON predicate (unless CROSS).
    match st.predicate {
        Some(e) => {
            assert(!is_cross(jt));
            assert(tbl_rest =~= seq![kwv(Keyword::On)] + (sprint_min(e, 0) + rest));
            assert(tbl_rest[0] == kwv(Keyword::On));
            let e_in = tbl_rest.drop_first();
            assert(e_in =~= sprint_min(e, 0) + rest);
            assert(inert(rest, 0));
            lemma_min(e, 0, rest, expr_fuel(e_in));
            assert(sparse_prec(e_in, 0, expr_fuel(e_in)) == (Some(e), rest));
            assert(SJoinStep { join_type: jt, right: st.right, predicate: Some(e) } == st);
        },
        None => {
            assert(is_cross(jt));
            assert(tbl_rest =~= rest);
            assert(SJoinStep { join_type: jt, right: st.right, predicate: None } == st);
        },
    }
}

/// A continuation that stops the join fold: not a join keyword, and safe after
/// a printed table / ON expression.
pub open spec fn joins_tail(rest: Seq<TokenView>) -> bool {
    rest.len() == 0
        || (neutral_head(rest[0]) && rest[0] != kwv(Keyword::As) && !(rest[0] is Ident)
            && !verified_stmt_prec::is_join_start(rest))
}

/// The printed join steps replay the left-deep fold.
pub proof fn lemma_join_steps_rt(acc: SFrom, steps: Seq<SJoinStep>, rest: Seq<TokenView>)
    requires
        printable_steps(steps),
        joins_tail(rest),
    ensures
        verified_stmt_prec::sparse_control_from_joins(acc, sprint_join_steps(steps) + rest)
            == (Some(fold_joins(acc, steps)), rest),
    decreases steps.len(),
{
    let input = sprint_join_steps(steps) + rest;
    if steps.len() == 0 {
        assert(input =~= rest);
        assert(!verified_stmt_prec::is_join_start(rest));
        verified_stmt_prec::lemma_from_joins_stop(acc, rest);
        assert(fold_joins(acc, steps) == acc);
    } else {
        let st = steps[0];
        let more = steps.drop_first();
        let rest1 = sprint_join_steps(more) + rest;
        assert(input =~= sprint_join_step(st) + rest1);
        assert(step_tail(rest1)) by {
            if more.len() == 0 {
                assert(rest1 =~= rest);
            } else {
                lemma_join_step_head(more[0]);
                assert(sprint_join_steps(more) =~= sprint_join_step(more[0])
                    + sprint_join_steps(more.drop_first()));
                assert(rest1[0] == sprint_join_step(more[0])[0]);
            }
        }
        lemma_join_step_rt(st, rest1);
        assert(verified_stmt_prec::sparse_control_from_step(input) == Some((st, rest1)));
        lemma_join_steps_rt(apply_step(acc, st), more, rest);
        assert(verified_stmt_prec::sparse_control_from_joins(acc, input)
            == verified_stmt_prec::sparse_control_from_joins(apply_step(acc, st), rest1));
        assert(fold_joins(acc, steps) == fold_joins(apply_step(acc, st), more));
    }
}

/// One printed FROM item (base table + join steps) parses back.
pub proof fn lemma_from_item_rt(f: SFrom, rest: Seq<TokenView>)
    requires
        printable_sfrom(f),
        joins_tail(rest),
    ensures
        verified_stmt_prec::sparse_control_from_item(sprint_from_item(f) + rest) == (Some(f), rest),
{
    let head = from_head(f);
    let steps = from_steps(f);
    lemma_from_head_is_table(f);
    lemma_fold_head_steps(f);
    lemma_steps_printable(f);
    let steps_rest = sprint_join_steps(steps) + rest;
    let input = sprint_from_item(f) + rest;
    assert(input =~= sprint_table(head) + steps_rest);
    assert(table_tail(steps_rest)) by {
        if steps.len() == 0 {
            assert(steps_rest =~= rest);
        } else {
            lemma_join_step_head(steps[0]);
            assert(sprint_join_steps(steps) =~= sprint_join_step(steps[0])
                + sprint_join_steps(steps.drop_first()));
            assert(steps_rest[0] == sprint_join_step(steps[0])[0]);
        }
    }
    lemma_from_table_rt(head, steps_rest);
    assert(verified_stmt_prec::sparse_control_from_table(input) == (Some(head), steps_rest));
    lemma_join_steps_rt(head, steps, rest);
    assert(verified_stmt_prec::sparse_control_from_joins(head, steps_rest)
        == (Some(fold_joins(head, steps)), rest));
    assert(fold_joins(head, steps) == f);
}

/// A continuation that stops the FROM item list: `joins_tail` and not a comma.
pub open spec fn from_list_tail(rest: Seq<TokenView>) -> bool {
    joins_tail(rest) && (rest.len() == 0 || rest[0] != TokenView::Comma)
}

/// The printed one-or-more FROM item list parses back.
#[verifier::spinoff_prover]
#[verifier::rlimit(400000)]
pub proof fn lemma_from_items_rt(fs: Seq<SFrom>, rest: Seq<TokenView>)
    requires
        printable_froms(fs),
        fs.len() >= 1,
        from_list_tail(rest),
    ensures
        verified_stmt_prec::sparse_control_from_list(sprint_from_items(fs) + rest)
            == (Some(fs), rest),
    decreases fs.len(),
{
    let input = sprint_from_items(fs) + rest;
    if fs.len() == 1 {
        assert(input =~= sprint_from_item(fs[0]) + rest);
        lemma_from_item_rt(fs[0], rest);
        assert(verified_stmt_prec::sparse_control_from_item(input) == (Some(fs[0]), rest));
        assert(verified_stmt_prec::sparse_control_from_list(input) == (Some(seq![fs[0]]), rest));
        assert(seq![fs[0]] =~= fs);
    } else {
        let restfs = fs.drop_first();
        let rest_toks = sprint_from_items(restfs) + rest;
        let comma_rest = seq![TokenView::Comma] + rest_toks;
        assert(input =~= sprint_from_item(fs[0]) + comma_rest);
        assert(joins_tail(comma_rest)) by {
            assert(comma_rest[0] == TokenView::Comma);
            assert(neutral_head(TokenView::Comma));
        }
        lemma_from_item_rt(fs[0], comma_rest);
        assert(verified_stmt_prec::sparse_control_from_item(input) == (Some(fs[0]), comma_rest));
        assert(comma_rest[0] == TokenView::Comma);
        assert(comma_rest.drop_first() =~= rest_toks);
        lemma_from_items_rt(restfs, rest);
        assert(verified_stmt_prec::sparse_control_from_list(input)
            == (Some(seq![fs[0]] + restfs), rest));
        assert(seq![fs[0]] + restfs =~= fs);
    }
}

/// The optional printed FROM clause parses back.
pub proof fn lemma_from_clause_rt(fs: Seq<SFrom>, rest: Seq<TokenView>)
    requires
        printable_froms(fs),
        from_list_tail(rest),
        fs.len() == 0 ==> (rest.len() == 0 || rest[0] != kwv(Keyword::From)),
    ensures
        verified_stmt_prec::sparse_control_from(sprint_from_clause(fs) + rest) == (Some(fs), rest),
{
    if fs.len() == 0 {
        assert(sprint_from_clause(fs) + rest =~= rest);
        assert(fs =~= Seq::<SFrom>::empty());
    } else {
        let input = sprint_from_clause(fs) + rest;
        assert(input =~= seq![kwv(Keyword::From)] + (sprint_from_items(fs) + rest));
        assert(input[0] == kwv(Keyword::From));
        assert(input.drop_first() =~= sprint_from_items(fs) + rest);
        lemma_from_items_rt(fs, rest);
    }
}

// ---- optional keyword-expression clauses and clause wrappers ----------------

/// The optional printed `KW <expr>` clause parses back.
pub proof fn lemma_kw_expr_rt(k: Keyword, o: Option<SExpr>, rest: Seq<TokenView>)
    requires
        printable_opt_se(o),
        rest.len() == 0 || neutral_head(rest[0]),
        o is None ==> (rest.len() == 0 || rest[0] != kwv(k)),
    ensures
        verified_stmt_prec::sparse_control_kw_expr(sprint_kw_expr(k, o) + rest, k)
            == (Some(o), rest),
{
    match o {
        Some(e) => {
            let input = sprint_kw_expr(k, o) + rest;
            assert(input =~= seq![kwv(k)] + (sprint_min(e, 0) + rest));
            assert(input[0] == kwv(k));
            let e_in = input.drop_first();
            assert(e_in =~= sprint_min(e, 0) + rest);
            assert(inert(rest, 0));
            lemma_min(e, 0, rest, expr_fuel(e_in));
            assert(sparse_prec(e_in, 0, expr_fuel(e_in)) == (Some(e), rest));
        },
        None => {
            assert(sprint_kw_expr(k, o) + rest =~= rest);
        },
    }
}

/// The optional printed GROUP BY clause parses back.
pub proof fn lemma_group_by_rt(items: Seq<SExpr>, rest: Seq<TokenView>)
    requires
        printable_exprs(items),
        expr_list_tail(rest),
        items.len() == 0 ==> (rest.len() == 0 || rest[0] != kwv(Keyword::Group)),
    ensures
        verified_stmt_prec::sparse_control_group_by(sprint_group_by(items) + rest)
            == (Some(items), rest),
{
    if items.len() == 0 {
        assert(sprint_group_by(items) + rest =~= rest);
        assert(items =~= Seq::<SExpr>::empty());
    } else {
        let input = sprint_group_by(items) + rest;
        assert(input =~= seq![kwv(Keyword::Group)]
            + (seq![kwv(Keyword::By)] + (sprint_exprs(items) + rest)));
        assert(input[0] == kwv(Keyword::Group));
        assert(input.drop_first() =~= seq![kwv(Keyword::By)] + (sprint_exprs(items) + rest));
        assert(input[1] == kwv(Keyword::By));
        assert(input.drop_first().drop_first() =~= sprint_exprs(items) + rest);
        lemma_exprs_rt(items, rest);
    }
}

/// The optional printed ORDER BY clause parses back.
pub proof fn lemma_order_by_rt(items: Seq<(SExpr, ast::Direction)>, rest: Seq<TokenView>)
    requires
        printable_order_items(items),
        expr_list_tail(rest),
        items.len() == 0 ==> (rest.len() == 0 || rest[0] != kwv(Keyword::Order)),
    ensures
        verified_stmt_prec::sparse_control_order_by(sprint_order_by(items) + rest)
            == (Some(items), rest),
{
    if items.len() == 0 {
        assert(sprint_order_by(items) + rest =~= rest);
        assert(items =~= Seq::<(SExpr, ast::Direction)>::empty());
    } else {
        let input = sprint_order_by(items) + rest;
        assert(input =~= seq![kwv(Keyword::Order)]
            + (seq![kwv(Keyword::By)] + (sprint_order_items(items) + rest)));
        assert(input[0] == kwv(Keyword::Order));
        assert(input.drop_first() =~= seq![kwv(Keyword::By)] + (sprint_order_items(items) + rest));
        assert(input[1] == kwv(Keyword::By));
        assert(input.drop_first().drop_first() =~= sprint_order_items(items) + rest);
        lemma_order_items_rt(items, rest);
    }
}

/// One printed UPDATE assignment `<ident> = (DEFAULT | <expr>)` parses back.
pub proof fn lemma_assign_rt(a: (String, Option<SExpr>), rest: Seq<TokenView>)
    requires
        printable_opt_se(a.1),
        rest.len() == 0 || (neutral_head(rest[0]) && rest[0] != TokenView::Comma),
    ensures
        verified_stmt_prec::sparse_control_assign(sprint_assign(a) + rest) == (Some(a), rest),
{
    let input = sprint_assign(a) + rest;
    match a.1 {
        Some(e) => {
            assert(input =~= seq![TokenView::Ident(a.0), TokenView::Equal]
                + (sprint_min(e, 0) + rest));
            assert(input.len() >= 2);
            assert(input[0] == TokenView::Ident(a.0));
            assert(input[1] == TokenView::Equal);
            let e_in = input.drop_first().drop_first();
            assert(e_in =~= sprint_min(e, 0) + rest);
            sprint_min_head_not_default(e, 0);
            assert(e_in[0] == sprint_min(e, 0)[0]);
            assert(!(e_in.len() >= 1 && e_in[0] == kwv(Keyword::Default)));
            assert(inert(rest, 0));
            lemma_min(e, 0, rest, expr_fuel(e_in));
            assert(sparse_prec(e_in, 0, expr_fuel(e_in)) == (Some(e), rest));
            assert((a.0, Some(e)) == a);
        },
        None => {
            assert(input =~= seq![TokenView::Ident(a.0), TokenView::Equal]
                + (seq![kwv(Keyword::Default)] + rest));
            assert(input.len() >= 2);
            assert(input[0] == TokenView::Ident(a.0));
            assert(input[1] == TokenView::Equal);
            let e_in = input.drop_first().drop_first();
            assert(e_in =~= seq![kwv(Keyword::Default)] + rest);
            assert(e_in[0] == kwv(Keyword::Default));
            assert(e_in.drop_first() =~= rest);
            assert((a.0, None::<SExpr>) == a);
        },
    }
}

// ===========================================================================
// Task 4 — per-statement body roundtrips and the headline spec theorem.
// ===========================================================================

/// The printed BEGIN clause tail parses back.
pub proof fn lemma_begin_body_rt(read_only: bool, as_of: Option<u64>)
    ensures
        verified_stmt_prec::sparse_control_begin(sprint_begin_body(read_only, as_of))
            == (Some(SStmt::Begin { read_only, as_of }), Seq::<TokenView>::empty()),
{
    let asof_part: Seq<TokenView> = match as_of {
        Some(v) => seq![
            kwv(Keyword::As), kwv(Keyword::Of), kwv(Keyword::System), kwv(Keyword::Time),
            TokenView::Number(verified_integer::decimal_digits(v)),
        ],
        None => Seq::empty(),
    };
    let input = sprint_begin_body(read_only, as_of);
    // No TRANSACTION printed: the head (READ / AS / nothing) is not TRANSACTION.
    if read_only {
        assert(input =~= seq![kwv(Keyword::Read), kwv(Keyword::Only)] + asof_part);
        assert(input[0] == kwv(Keyword::Read));
        assert(input.drop_first() =~= seq![kwv(Keyword::Only)] + asof_part);
        assert(input.drop_first()[0] == kwv(Keyword::Only));
        assert(input.drop_first().drop_first() =~= asof_part);
    } else {
        assert(input =~= asof_part);
        match as_of {
            Some(v) => {
                assert(input[0] == kwv(Keyword::As));
            },
            None => {
                assert(input.len() == 0);
            },
        }
    }
    // The AS OF SYSTEM TIME chain (when present) recovers the version.
    match as_of {
        Some(v) => {
            assert(asof_part[0] == kwv(Keyword::As));
            assert(asof_part.drop_first()[0] == kwv(Keyword::Of));
            assert(asof_part.drop_first().drop_first()[0] == kwv(Keyword::System));
            assert(asof_part.drop_first().drop_first().drop_first()[0] == kwv(Keyword::Time));
            let r6 = asof_part.drop_first().drop_first().drop_first().drop_first();
            assert(r6[0] == TokenView::Number(verified_integer::decimal_digits(v)));
            verified_integer::print_parse_u64_roundtrip(v);
            assert(verified_integer::parse_digits_spec(verified_integer::decimal_digits(v))
                == Some(v));
            assert(r6.drop_first() =~= Seq::<TokenView>::empty());
        },
        None => {},
    }
}

/// The printed DROP TABLE clause tail parses back.
pub proof fn lemma_drop_body_rt(name: String, if_exists: bool)
    ensures
        verified_stmt_prec::sparse_control_drop(
            seq![kwv(Keyword::Table)]
            + (if if_exists { seq![kwv(Keyword::If), kwv(Keyword::Exists)] } else { Seq::empty() })
            + seq![TokenView::Ident(name)],
        ) == (Some(SStmt::DropTable { name, if_exists }), Seq::<TokenView>::empty()),
{
    if if_exists {
        let input = seq![kwv(Keyword::Table), kwv(Keyword::If), kwv(Keyword::Exists),
            TokenView::Ident(name)];
        assert(seq![kwv(Keyword::Table)] + seq![kwv(Keyword::If), kwv(Keyword::Exists)]
            + seq![TokenView::Ident(name)] =~= input);
        assert(input[0] == kwv(Keyword::Table));
        assert(input[1] == kwv(Keyword::If));
        assert(input[2] == kwv(Keyword::Exists));
        let r = input.drop_first().drop_first().drop_first();
        assert(r =~= seq![TokenView::Ident(name)]);
        assert(r[0] == TokenView::Ident(name));
        assert(r.drop_first() =~= Seq::<TokenView>::empty());
    } else {
        let input = seq![kwv(Keyword::Table), TokenView::Ident(name)];
        assert(seq![kwv(Keyword::Table)] + Seq::<TokenView>::empty()
            + seq![TokenView::Ident(name)] =~= input);
        assert(input[0] == kwv(Keyword::Table));
        assert(input[1] == TokenView::Ident(name));
        let r = input.drop_first();
        assert(r =~= seq![TokenView::Ident(name)]);
        assert(r[0] == TokenView::Ident(name));
        assert(r.drop_first() =~= Seq::<TokenView>::empty());
    }
}

/// The printed DELETE clause tail parses back.
pub proof fn lemma_delete_body_rt(table: String, where_clause: Option<SExpr>)
    requires
        printable_opt_se(where_clause),
    ensures
        verified_stmt_prec::sparse_control_delete(
            seq![kwv(Keyword::From), TokenView::Ident(table)]
                + sprint_kw_expr(Keyword::Where, where_clause),
        ) == (Some(SStmt::Delete { table, where_clause }), Seq::<TokenView>::empty()),
{
    let wpart = sprint_kw_expr(Keyword::Where, where_clause);
    let input = seq![kwv(Keyword::From), TokenView::Ident(table)] + wpart;
    assert(input[0] == kwv(Keyword::From));
    assert(input[1] == TokenView::Ident(table));
    let r = input.drop_first().drop_first();
    assert(r =~= wpart);
    match where_clause {
        Some(e) => {
            assert(wpart =~= seq![kwv(Keyword::Where)] + sprint_min(e, 0));
            assert(r[0] == kwv(Keyword::Where));
            let e_in = r.drop_first();
            assert(e_in =~= sprint_min(e, 0) + Seq::<TokenView>::empty());
            assert(inert(Seq::<TokenView>::empty(), 0));
            lemma_min(e, 0, Seq::<TokenView>::empty(), expr_fuel(e_in));
            assert(sparse_prec(e_in, 0, expr_fuel(e_in))
                == (Some(e), Seq::<TokenView>::empty()));
        },
        None => {
            assert(r.len() == 0);
        },
    }
}

/// The printed CREATE TABLE clause tail parses back.
pub proof fn lemma_create_body_rt(name: String, columns: Seq<SColumn>)
    requires
        columns.len() >= 1,
        printable_columns(columns),
    ensures
        verified_stmt_prec::sparse_control_create(
            seq![kwv(Keyword::Table), TokenView::Ident(name), TokenView::OpenParen]
                + sprint_columns(columns) + seq![TokenView::CloseParen],
        ) == (Some(SStmt::CreateTable { name, columns }), Seq::<TokenView>::empty()),
{
    let close: Seq<TokenView> = seq![TokenView::CloseParen];
    let input = seq![kwv(Keyword::Table), TokenView::Ident(name), TokenView::OpenParen]
        + sprint_columns(columns) + close;
    assert(input[0] == kwv(Keyword::Table));
    let r0 = input.drop_first();
    assert(r0[0] == TokenView::Ident(name));
    let r1 = r0.drop_first();
    assert(r1[0] == TokenView::OpenParen);
    let r2 = r1.drop_first();
    assert(r2 =~= sprint_columns(columns) + close);
    lemma_columns_rt(columns, close);
    assert(verified_stmt_prec::sparse_control_column_list(r2) == (Some(columns), close));
    assert(close[0] == TokenView::CloseParen);
    assert(close.drop_first() =~= Seq::<TokenView>::empty());
}

/// The printed INSERT clause tail parses back.
pub proof fn lemma_insert_body_rt(
    table: String,
    columns: Option<Seq<String>>,
    values: Seq<Seq<SExpr>>,
)
    requires
        (match columns {
            Some(cols) => cols.len() >= 1,
            None => true,
        }),
        values.len() >= 1,
        printable_rows(values),
    ensures
        verified_stmt_prec::sparse_control_insert(
            seq![kwv(Keyword::Into), TokenView::Ident(table)]
            + (match columns {
                Some(cols) => seq![TokenView::OpenParen] + sprint_idents(cols)
                    + seq![TokenView::CloseParen],
                None => Seq::<TokenView>::empty(),
            })
            + seq![kwv(Keyword::Values)] + sprint_rows(values),
        ) == (Some(SStmt::Insert { table, columns, values }), Seq::<TokenView>::empty()),
{
    let colpart: Seq<TokenView> = match columns {
        Some(cols) => seq![TokenView::OpenParen] + sprint_idents(cols)
            + seq![TokenView::CloseParen],
        None => Seq::empty(),
    };
    let vtail = seq![kwv(Keyword::Values)] + sprint_rows(values);
    let input = seq![kwv(Keyword::Into), TokenView::Ident(table)] + colpart + vtail;
    // Link the ensures' left-associated concatenation to `input`.
    assert(seq![kwv(Keyword::Into), TokenView::Ident(table)] + colpart
        + seq![kwv(Keyword::Values)] + sprint_rows(values) =~= input);
    assert(input[0] == kwv(Keyword::Into));
    let r0 = input.drop_first();
    assert(r0[0] == TokenView::Ident(table));
    let r1 = r0.drop_first();
    assert(r1 =~= colpart + vtail);
    // The optional column list.
    match columns {
        Some(cols) => {
            assert(r1 =~= seq![TokenView::OpenParen]
                + (sprint_idents(cols) + (seq![TokenView::CloseParen] + vtail)));
            assert(r1[0] == TokenView::OpenParen);
            let ctail = seq![TokenView::CloseParen] + vtail;
            assert(r1.drop_first() =~= sprint_idents(cols) + ctail);
            assert(ctail[0] == TokenView::CloseParen);
            lemma_idents_rt(cols, ctail);
            assert(verified_stmt_prec::sparse_control_ident_list(r1.drop_first())
                == (Some(cols), ctail));
            assert(ctail.drop_first() =~= vtail);
            assert(verified_stmt_prec::sparse_control_opt_columns(r1)
                == Some((Some(cols), vtail)));
        },
        None => {
            assert(r1 =~= vtail);
            assert(r1[0] == kwv(Keyword::Values));
            assert(verified_stmt_prec::sparse_control_opt_columns(r1)
                == Some((None::<Seq<String>>, vtail)));
        },
    }
    // VALUES and the rows.
    assert(vtail[0] == kwv(Keyword::Values));
    assert(vtail.drop_first() =~= sprint_rows(values) + Seq::<TokenView>::empty());
    lemma_rows_rt(values, Seq::<TokenView>::empty());
    assert(verified_stmt_prec::sparse_control_values(vtail.drop_first())
        == (Some(values), Seq::<TokenView>::empty()));
}

/// The printed UPDATE clause tail parses back (single assignment: the printable
/// domain, matching `view_stmt`'s singleton bridge).
pub proof fn lemma_update_body_rt(
    table: String,
    set: Seq<(String, Option<SExpr>)>,
    where_clause: Option<SExpr>,
)
    requires
        set.len() == 1,
        printable_opt_se(set[0].1),
        printable_opt_se(where_clause),
    ensures
        verified_stmt_prec::sparse_control_update(
            seq![TokenView::Ident(table), kwv(Keyword::Set)] + sprint_assign(set[0])
                + sprint_kw_expr(Keyword::Where, where_clause),
        ) == (Some(SStmt::Update { table, set, where_clause }), Seq::<TokenView>::empty()),
{
    let wpart = sprint_kw_expr(Keyword::Where, where_clause);
    let input = seq![TokenView::Ident(table), kwv(Keyword::Set)] + sprint_assign(set[0]) + wpart;
    assert(input[0] == TokenView::Ident(table));
    let r0 = input.drop_first();
    assert(r0[0] == kwv(Keyword::Set));
    let r1 = r0.drop_first();
    assert(r1 =~= sprint_assign(set[0]) + wpart);
    // The single assignment; the continuation is `WHERE ...` or empty.
    assert(wpart.len() == 0 || (neutral_head(wpart[0]) && wpart[0] != TokenView::Comma)) by {
        match where_clause {
            Some(e) => {
                assert(wpart[0] == kwv(Keyword::Where));
            },
            None => {},
        }
    }
    lemma_assign_rt(set[0], wpart);
    assert(verified_stmt_prec::sparse_control_assign(r1) == (Some(set[0]), wpart));
    assert(!(wpart.len() >= 1 && wpart[0] == TokenView::Comma)) by {
        match where_clause {
            Some(e) => {
                assert(wpart[0] == kwv(Keyword::Where));
            },
            None => {},
        }
    }
    assert(verified_stmt_prec::sparse_control_assign_list(r1) == (Some(seq![set[0]]), wpart));
    let items = seq![set[0]];
    assert(verified_stmt_prec::assign_keys_distinct(items));
    // The optional WHERE.
    match where_clause {
        Some(e) => {
            assert(wpart =~= seq![kwv(Keyword::Where)] + sprint_min(e, 0));
            assert(wpart[0] == kwv(Keyword::Where));
            let e_in = wpart.drop_first();
            assert(e_in =~= sprint_min(e, 0) + Seq::<TokenView>::empty());
            assert(inert(Seq::<TokenView>::empty(), 0));
            lemma_min(e, 0, Seq::<TokenView>::empty(), expr_fuel(e_in));
            assert(sparse_prec(e_in, 0, expr_fuel(e_in))
                == (Some(e), Seq::<TokenView>::empty()));
        },
        None => {
            assert(wpart.len() == 0);
        },
    }
    // The singleton boundary map yields exactly the statement.
    assert(verified_stmt_prec::assign_list_to_sstmt(table, items, where_clause)
        == SStmt::Update { table, set, where_clause }) by {
        assert(items[0] == set[0]);
        assert((items[0].0, items[0].1) == set[0]);
        assert(seq![(items[0].0, items[0].1)] =~= set);
    }
}

/// The printed SELECT clause tail parses back through the composed clause twin.
#[verifier::spinoff_prover]
#[verifier::rlimit(400000)]
pub proof fn lemma_select_body_rt(
    select: Seq<(SExpr, Option<String>)>,
    from: Seq<SFrom>,
    where_clause: Option<SExpr>,
    group_by: Seq<SExpr>,
    having: Option<SExpr>,
    order_by: Seq<(SExpr, ast::Direction)>,
    limit: Option<SExpr>,
    offset: Option<SExpr>,
)
    requires
        select.len() >= 1,
        printable_select_items(select),
        printable_froms(from),
        printable_opt_se(where_clause),
        printable_exprs(group_by),
        printable_opt_se(having),
        printable_order_items(order_by),
        printable_opt_se(limit),
        printable_opt_se(offset),
    ensures
        verified_stmt_prec::sparse_control_select(sprint_select_body(
            select, from, where_clause, group_by, having, order_by, limit, offset,
        )) == (
            Some(SStmt::Select {
                select, from, where_clause, group_by, having, order_by, limit, offset,
            }),
            Seq::<TokenView>::empty(),
        ),
{
    let t8: Seq<TokenView> = Seq::empty();
    let t7 = sprint_kw_expr(Keyword::Offset, offset) + t8;
    let t6 = sprint_kw_expr(Keyword::Limit, limit) + t7;
    let t5 = sprint_order_by(order_by) + t6;
    let t4 = sprint_kw_expr(Keyword::Having, having) + t5;
    let t3 = sprint_group_by(group_by) + t4;
    let t2 = sprint_kw_expr(Keyword::Where, where_clause) + t3;
    let t1 = sprint_from_clause(from) + t2;
    let body = sprint_select_items(select) + t1;
    assert(sprint_select_body(select, from, where_clause, group_by, having, order_by, limit,
        offset) =~= body);

    // Heads of the successive suffixes: each is empty or a later clause keyword.
    assert(t7.len() == 0 || t7[0] == kwv(Keyword::Offset)) by {
        match offset {
            Some(e) => {
                assert(t7[0] == kwv(Keyword::Offset));
            },
            None => {
                assert(t7 =~= t8);
            },
        }
    }
    assert(t6.len() == 0 || t6[0] == kwv(Keyword::Limit) || t6[0] == kwv(Keyword::Offset)) by {
        match limit {
            Some(e) => {
                assert(t6[0] == kwv(Keyword::Limit));
            },
            None => {
                assert(t6 =~= t7);
            },
        }
    }
    assert(t5.len() == 0 || t5[0] == kwv(Keyword::Order) || t5[0] == kwv(Keyword::Limit)
        || t5[0] == kwv(Keyword::Offset)) by {
        if order_by.len() > 0 {
            assert(t5[0] == kwv(Keyword::Order));
        } else {
            assert(t5 =~= t6);
        }
    }
    assert(t4.len() == 0 || t4[0] == kwv(Keyword::Having) || t4[0] == kwv(Keyword::Order)
        || t4[0] == kwv(Keyword::Limit) || t4[0] == kwv(Keyword::Offset)) by {
        match having {
            Some(e) => {
                assert(t4[0] == kwv(Keyword::Having));
            },
            None => {
                assert(t4 =~= t5);
            },
        }
    }
    assert(t3.len() == 0 || t3[0] == kwv(Keyword::Group) || t3[0] == kwv(Keyword::Having)
        || t3[0] == kwv(Keyword::Order) || t3[0] == kwv(Keyword::Limit)
        || t3[0] == kwv(Keyword::Offset)) by {
        if group_by.len() > 0 {
            assert(t3[0] == kwv(Keyword::Group));
        } else {
            assert(t3 =~= t4);
        }
    }
    assert(t2.len() == 0 || t2[0] == kwv(Keyword::Where) || t2[0] == kwv(Keyword::Group)
        || t2[0] == kwv(Keyword::Having) || t2[0] == kwv(Keyword::Order)
        || t2[0] == kwv(Keyword::Limit) || t2[0] == kwv(Keyword::Offset)) by {
        match where_clause {
            Some(e) => {
                assert(t2[0] == kwv(Keyword::Where));
            },
            None => {
                assert(t2 =~= t3);
            },
        }
    }
    assert(t1.len() == 0 || t1[0] == kwv(Keyword::From) || t1[0] == kwv(Keyword::Where)
        || t1[0] == kwv(Keyword::Group) || t1[0] == kwv(Keyword::Having)
        || t1[0] == kwv(Keyword::Order) || t1[0] == kwv(Keyword::Limit)
        || t1[0] == kwv(Keyword::Offset)) by {
        if from.len() > 0 {
            assert(t1[0] == kwv(Keyword::From));
        } else {
            assert(t1 =~= t2);
        }
    }

    // The clause keywords are all neutral, non-comma, non-alias, non-join heads.
    assert(neutral_head(kwv(Keyword::From)) && neutral_head(kwv(Keyword::Where))
        && neutral_head(kwv(Keyword::Group)) && neutral_head(kwv(Keyword::Having))
        && neutral_head(kwv(Keyword::Order)) && neutral_head(kwv(Keyword::Limit))
        && neutral_head(kwv(Keyword::Offset)));

    // Chain the clause roundtrips.
    lemma_select_items_rt(select, t1);
    assert(verified_stmt_prec::sparse_control_select_list(body) == (Some(select), t1));
    lemma_from_clause_rt(from, t2);
    assert(verified_stmt_prec::sparse_control_from(t1) == (Some(from), t2));
    lemma_kw_expr_rt(Keyword::Where, where_clause, t3);
    assert(verified_stmt_prec::sparse_control_kw_expr(t2, Keyword::Where)
        == (Some(where_clause), t3));
    lemma_group_by_rt(group_by, t4);
    assert(verified_stmt_prec::sparse_control_group_by(t3) == (Some(group_by), t4));
    lemma_kw_expr_rt(Keyword::Having, having, t5);
    assert(verified_stmt_prec::sparse_control_kw_expr(t4, Keyword::Having)
        == (Some(having), t5));
    lemma_order_by_rt(order_by, t6);
    assert(verified_stmt_prec::sparse_control_order_by(t5) == (Some(order_by), t6));
    lemma_kw_expr_rt(Keyword::Limit, limit, t7);
    assert(verified_stmt_prec::sparse_control_kw_expr(t6, Keyword::Limit) == (Some(limit), t7));
    lemma_kw_expr_rt(Keyword::Offset, offset, t8);
    assert(verified_stmt_prec::sparse_control_kw_expr(t7, Keyword::Offset) == (Some(offset), t8));
}

/// A printable non-EXPLAIN statement's print never begins with `EXPLAIN` (the
/// nested-EXPLAIN guard of the dispatch twin).
pub proof fn lemma_stmt_head_not_explain(s: SStmt)
    requires
        printable_stmt(s),
        !(s is Explain),
    ensures
        sprint_min_stmt(s).len() >= 1,
        sprint_min_stmt(s)[0] != kwv(Keyword::Explain),
{
    match s {
        SStmt::Commit => {},
        SStmt::Rollback => {},
        SStmt::Begin { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Begin));
        },
        SStmt::DropTable { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Drop));
        },
        SStmt::Delete { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Delete));
        },
        SStmt::CreateTable { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Create));
        },
        SStmt::Insert { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Insert));
        },
        SStmt::Update { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Update));
        },
        SStmt::Select { .. } => {
            assert(sprint_min_stmt(s)[0] == kwv(Keyword::Select));
        },
        SStmt::Explain(_) => {},
        SStmt::Unsupported => {},
    }
}

/// HEADLINE (task 4, spec level): the min-parens print of any printable mirror
/// statement re-parses through the statement dispatch twin to exactly that
/// statement, consuming every token:
///
///   sparse_control(sprint_min_stmt(s)) == (Some(s), empty)
///
/// Because every expression position prints via `sprint_min` (bare precedence
/// syntax) and every clause list prints without redundant delimiters, this
/// pins the statement grammar's keyword skeleton, clause sequencing, list
/// separators, join folding, and the full precedence/associativity table,
/// end to end.
#[verifier::spinoff_prover]
#[verifier::rlimit(200000)]
pub proof fn stmt_min_roundtrip(s: SStmt)
    requires
        printable_stmt(s),
    ensures
        verified_stmt_prec::sparse_control(sprint_min_stmt(s))
            == (Some(s), Seq::<TokenView>::empty()),
    decreases s,
{
    let toks = sprint_min_stmt(s);
    match s {
        SStmt::Commit => {
            assert(toks =~= seq![kwv(Keyword::Commit)]);
            assert(toks[0] == kwv(Keyword::Commit));
            assert(toks.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Rollback => {
            assert(toks =~= seq![kwv(Keyword::Rollback)]);
            assert(toks[0] == kwv(Keyword::Rollback));
            assert(toks.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Begin { read_only, as_of } => {
            assert(toks =~= seq![kwv(Keyword::Begin)] + sprint_begin_body(read_only, as_of));
            assert(toks[0] == kwv(Keyword::Begin));
            assert(toks.drop_first() =~= sprint_begin_body(read_only, as_of));
            lemma_begin_body_rt(read_only, as_of);
        },
        SStmt::DropTable { name, if_exists } => {
            let body = seq![kwv(Keyword::Table)]
                + (if if_exists {
                    seq![kwv(Keyword::If), kwv(Keyword::Exists)]
                } else {
                    Seq::<TokenView>::empty()
                })
                + seq![TokenView::Ident(name)];
            assert(toks =~= seq![kwv(Keyword::Drop)] + body);
            assert(toks[0] == kwv(Keyword::Drop));
            assert(toks.drop_first() =~= body);
            lemma_drop_body_rt(name, if_exists);
        },
        SStmt::Delete { table, where_clause } => {
            let body = seq![kwv(Keyword::From), TokenView::Ident(table)]
                + sprint_kw_expr(Keyword::Where, where_clause);
            assert(toks =~= seq![kwv(Keyword::Delete)] + body);
            assert(toks[0] == kwv(Keyword::Delete));
            assert(toks.drop_first() =~= body);
            lemma_delete_body_rt(table, where_clause);
        },
        SStmt::CreateTable { name, columns } => {
            let body = seq![kwv(Keyword::Table), TokenView::Ident(name), TokenView::OpenParen]
                + sprint_columns(columns) + seq![TokenView::CloseParen];
            assert(toks =~= seq![kwv(Keyword::Create)] + body);
            assert(toks[0] == kwv(Keyword::Create));
            assert(toks.drop_first() =~= body);
            lemma_create_body_rt(name, columns);
        },
        SStmt::Insert { table, columns, values } => {
            let body = seq![kwv(Keyword::Into), TokenView::Ident(table)]
                + (match columns {
                    Some(cols) => seq![TokenView::OpenParen] + sprint_idents(cols)
                        + seq![TokenView::CloseParen],
                    None => Seq::<TokenView>::empty(),
                })
                + seq![kwv(Keyword::Values)] + sprint_rows(values);
            assert(toks =~= seq![kwv(Keyword::Insert)] + body);
            assert(toks[0] == kwv(Keyword::Insert));
            assert(toks.drop_first() =~= body);
            lemma_insert_body_rt(table, columns, values);
        },
        SStmt::Update { table, set, where_clause } => {
            let body = seq![TokenView::Ident(table), kwv(Keyword::Set)] + sprint_assign(set[0])
                + sprint_kw_expr(Keyword::Where, where_clause);
            assert(toks =~= seq![kwv(Keyword::Update)] + body);
            assert(toks[0] == kwv(Keyword::Update));
            assert(toks.drop_first() =~= body);
            lemma_update_body_rt(table, set, where_clause);
        },
        SStmt::Select { select, from, where_clause, group_by, having, order_by, limit, offset } => {
            let body = sprint_select_body(
                select, from, where_clause, group_by, having, order_by, limit, offset);
            assert(toks =~= seq![kwv(Keyword::Select)] + body);
            assert(toks[0] == kwv(Keyword::Select));
            assert(toks.drop_first() =~= body);
            lemma_select_body_rt(
                select, from, where_clause, group_by, having, order_by, limit, offset);
        },
        SStmt::Explain(inner) => {
            assert(toks =~= seq![kwv(Keyword::Explain)] + sprint_min_stmt(*inner));
            assert(toks[0] == kwv(Keyword::Explain));
            assert(toks.drop_first() =~= sprint_min_stmt(*inner));
            stmt_min_roundtrip(*inner);
            lemma_stmt_head_not_explain(*inner);
            assert(sprint_min_stmt(*inner)[0] != kwv(Keyword::Explain));
            assert(verified_stmt_prec::sparse_control_explain(sprint_min_stmt(*inner))
                == (Some(SStmt::Explain(Box::new(*inner))), Seq::<TokenView>::empty()));
            assert(SStmt::Explain(Box::new(*inner)) == s);
        },
        SStmt::Unsupported => {},
    }
}

// ===========================================================================
// Task 3 remainder — the executable statement printer, refining
// `sprint_min_stmt` at the token-view level.
// ===========================================================================

/// Push one token, tracking the token view.
fn push_tok(out: &mut Vec<Token>, t: Token)
    ensures
        verified_production::token_views(final(out)@)
            == verified_production::token_views(old(out)@)
                + seq![verified_production::token_view(t)],
{
    let ghost o = out@;
    let ghost tt = t;
    out.push(t);
    proof {
        assert(out@ =~= o + seq![tt]);
        verified_production::token_views_concat(o, seq![tt]);
        reveal_with_fuel(verified_production::token_views, 2);
        assert(verified_production::token_views(seq![tt])
            =~= seq![verified_production::token_view(tt)]);
    }
}

/// Append a token vector, tracking the token views.
fn append_toks(out: &mut Vec<Token>, more: Vec<Token>)
    ensures
        verified_production::token_views(final(out)@)
            == verified_production::token_views(old(out)@)
                + verified_production::token_views(more@),
{
    let ghost o = out@;
    let mut more = more;
    let ghost m = more@;
    out.append(&mut more);
    proof {
        assert(out@ =~= o + m);
        verified_production::token_views_concat(o, m);
    }
}

/// `view_select_list` length.
pub proof fn lemma_view_select_list_len(items: Seq<(ast::Expression, Option<String>)>)
    ensures
        verified_stmt::view_select_list(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_view_select_list_len(items.drop_first());
    }
}

/// `view_order_list` length.
pub proof fn lemma_view_order_list_len(items: Seq<(ast::Expression, ast::Direction)>)
    ensures
        verified_stmt::view_order_list(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_view_order_list_len(items.drop_first());
    }
}

/// `view_rows` length.
pub proof fn lemma_view_rows_len(rows: Seq<Vec<ast::Expression>>)
    ensures
        verified_stmt::view_rows(rows).len() == rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_view_rows_len(rows.drop_first());
    }
}

/// `view_columns` length.
pub proof fn lemma_view_columns_len(cols: Seq<ast::Column>)
    ensures
        verified_stmt::view_columns(cols).len() == cols.len(),
    decreases cols.len(),
{
    if cols.len() > 0 {
        lemma_view_columns_len(cols.drop_first());
    }
}

/// `view_froms` length.
pub proof fn lemma_view_froms_len(fs: Seq<ast::From>)
    ensures
        verified_stmt::view_froms(fs).len() == fs.len(),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_view_froms_len(fs.drop_first());
    }
}

/// Exec printer for a comma-separated expression list.
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn print_exprs_slice(s: &[ast::Expression]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_exprs(verified_roundtrip::view_args(s@)),
    ensures
        verified_production::token_views(r@) == sprint_exprs(verified_roundtrip::view_args(s@)),
    decreases s@.len(),
{
    let ghost va = verified_roundtrip::view_args(s@);
    proof {
        verified_roundtrip::view_args_len(s@);
        assert(va == seq![verified_roundtrip::view_expr(s@[0])]
            + verified_roundtrip::view_args(s@.drop_first()));
        assert(va[0] == verified_roundtrip::view_expr(s@[0]));
        assert(va.drop_first() =~= verified_roundtrip::view_args(s@.drop_first()));
        assert(printable_se(va[0]));
    }
    if s.len() == 1 {
        proof {
            assert(sprint_exprs(va) == sprint_min(va[0], 0));
        }
        verified_minparen::print_min_at(&s[0], 0)
    } else {
        let mut r = verified_minparen::print_min_at(&s[0], 0);
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_exprs_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_min(va[0], 0) + seq![TokenView::Comma] + sprint_exprs(va.drop_first()));
            assert(sprint_exprs(va)
                == sprint_min(va[0], 0) + seq![TokenView::Comma] + sprint_exprs(va.drop_first()));
        }
        r
    }
}

/// Exec printer for the select list.
#[verifier::spinoff_prover]
#[verifier::rlimit(150000)]
fn print_select_items_slice(s: &[(ast::Expression, Option<String>)]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_select_items(verified_stmt::view_select_list(s@)),
    ensures
        verified_production::token_views(r@)
            == sprint_select_items(verified_stmt::view_select_list(s@)),
    decreases s@.len(),
{
    let ghost vl = verified_stmt::view_select_list(s@);
    proof {
        lemma_view_select_list_len(s@);
        assert(vl == seq![(verified_roundtrip::view_expr(s@[0].0), s@[0].1)]
            + verified_stmt::view_select_list(s@.drop_first()));
        assert(vl[0] == (verified_roundtrip::view_expr(s@[0].0), s@[0].1));
        assert(vl.drop_first() =~= verified_stmt::view_select_list(s@.drop_first()));
        assert(printable_se(vl[0].0));
    }
    let mut r = verified_minparen::print_min_at(&s[0].0, 0);
    match &s[0].1 {
        Some(a) => {
            push_tok(&mut r, Token::Keyword(Keyword::As));
            push_tok(&mut r, Token::Ident(a.clone()));
            proof {
                assert(verified_production::token_views(r@)
                    =~= sprint_min(vl[0].0, 0) + sprint_alias(vl[0].1));
            }
        },
        None => {
            proof {
                assert(sprint_alias(vl[0].1) =~= Seq::<TokenView>::empty());
                assert(verified_production::token_views(r@)
                    =~= sprint_min(vl[0].0, 0) + sprint_alias(vl[0].1));
            }
        },
    }
    if s.len() == 1 {
        proof {
            assert(sprint_select_items(vl) == sprint_min(vl[0].0, 0) + sprint_alias(vl[0].1));
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_select_items_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_min(vl[0].0, 0) + sprint_alias(vl[0].1) + seq![TokenView::Comma]
                    + sprint_select_items(vl.drop_first()));
        }
        r
    }
}

/// Exec printer for the ORDER BY list.
#[verifier::spinoff_prover]
#[verifier::rlimit(150000)]
fn print_order_items_slice(s: &[(ast::Expression, ast::Direction)]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_order_items(verified_stmt::view_order_list(s@)),
    ensures
        verified_production::token_views(r@)
            == sprint_order_items(verified_stmt::view_order_list(s@)),
    decreases s@.len(),
{
    let ghost vl = verified_stmt::view_order_list(s@);
    proof {
        lemma_view_order_list_len(s@);
        assert(vl == seq![(verified_roundtrip::view_expr(s@[0].0), s@[0].1)]
            + verified_stmt::view_order_list(s@.drop_first()));
        assert(vl[0] == (verified_roundtrip::view_expr(s@[0].0), s@[0].1));
        assert(vl.drop_first() =~= verified_stmt::view_order_list(s@.drop_first()));
        assert(printable_se(vl[0].0));
    }
    let mut r = verified_minparen::print_min_at(&s[0].0, 0);
    match s[0].1 {
        ast::Direction::Ascending => {
            push_tok(&mut r, Token::Keyword(Keyword::Asc));
        },
        ast::Direction::Descending => {
            push_tok(&mut r, Token::Keyword(Keyword::Desc));
        },
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= sprint_min(vl[0].0, 0) + seq![dir_tok(vl[0].1)]);
    }
    if s.len() == 1 {
        proof {
            assert(sprint_order_items(vl) == sprint_min(vl[0].0, 0) + seq![dir_tok(vl[0].1)]);
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_order_items_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_min(vl[0].0, 0) + seq![dir_tok(vl[0].1)] + seq![TokenView::Comma]
                    + sprint_order_items(vl.drop_first()));
        }
        r
    }
}

/// Exec printer for the INSERT column-name list.
fn print_idents_slice(s: &[String]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
    ensures
        verified_production::token_views(r@) == sprint_idents(s@),
    decreases s@.len(),
{
    let mut r: Vec<Token> = Vec::new();
    push_tok(&mut r, Token::Ident(s[0].clone()));
    if s.len() == 1 {
        proof {
            assert(verified_production::token_views(r@) =~= seq![TokenView::Ident(s@[0])]);
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_idents_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= seq![TokenView::Ident(s@[0]), TokenView::Comma]
                    + sprint_idents(s@.drop_first()));
        }
        r
    }
}

/// Exec printer for the VALUES rows.
#[verifier::spinoff_prover]
#[verifier::rlimit(150000)]
fn print_rows_slice(s: &[Vec<ast::Expression>]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_rows(verified_stmt::view_rows(s@)),
    ensures
        verified_production::token_views(r@) == sprint_rows(verified_stmt::view_rows(s@)),
    decreases s@.len(),
{
    let ghost vr = verified_stmt::view_rows(s@);
    proof {
        lemma_view_rows_len(s@);
        assert(vr == seq![verified_roundtrip::view_args(s@[0]@)]
            + verified_stmt::view_rows(s@.drop_first()));
        assert(vr[0] == verified_roundtrip::view_args(s@[0]@));
        assert(vr.drop_first() =~= verified_stmt::view_rows(s@.drop_first()));
        verified_roundtrip::view_args_len(s@[0]@);
    }
    let mut r: Vec<Token> = Vec::new();
    push_tok(&mut r, Token::OpenParen);
    let row = print_exprs_slice(s[0].as_slice());
    append_toks(&mut r, row);
    push_tok(&mut r, Token::CloseParen);
    proof {
        assert(verified_production::token_views(r@) =~= sprint_row(vr[0]));
    }
    if s.len() == 1 {
        proof {
            assert(sprint_rows(vr) == sprint_row(vr[0]));
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_rows_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_row(vr[0]) + seq![TokenView::Comma] + sprint_rows(vr.drop_first()));
        }
        r
    }
}

/// Exec printer for one CREATE TABLE column.
#[verifier::spinoff_prover]
#[verifier::rlimit(300000)]
fn print_column_toks(c: &ast::Column) -> (r: Vec<Token>)
    requires
        printable_column(verified_stmt::view_column(*c)),
    ensures
        verified_production::token_views(r@) == sprint_column(verified_stmt::view_column(*c)),
{
    let ghost vc = verified_stmt::view_column(*c);
    let mut r: Vec<Token> = Vec::new();
    push_tok(&mut r, Token::Ident(c.name.clone()));
    match c.datatype {
        DataType::Boolean => push_tok(&mut r, Token::Keyword(Keyword::Boolean)),
        DataType::Integer => push_tok(&mut r, Token::Keyword(Keyword::Integer)),
        DataType::Float => push_tok(&mut r, Token::Keyword(Keyword::Float)),
        DataType::String => push_tok(&mut r, Token::Keyword(Keyword::String)),
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![TokenView::Ident(vc.name), datatype_tok(vc.datatype)]);
    }
    let ghost head = verified_production::token_views(r@);
    let ghost s_pk: Seq<TokenView> = if vc.primary_key {
        seq![kwv(Keyword::Primary), kwv(Keyword::Key)]
    } else {
        Seq::empty()
    };
    let ghost s_null: Seq<TokenView> = match vc.nullable {
        Some(true) => seq![kwv(Keyword::Null)],
        Some(false) => seq![kwv(Keyword::Not), kwv(Keyword::Null)],
        None => Seq::empty(),
    };
    let ghost s_uni: Seq<TokenView> = if vc.unique { seq![kwv(Keyword::Unique)] } else { Seq::empty() };
    let ghost s_idx: Seq<TokenView> = if vc.index { seq![kwv(Keyword::Index)] } else { Seq::empty() };
    let ghost s_ref: Seq<TokenView> = match vc.references {
        Some(rname) => seq![kwv(Keyword::References), TokenView::Ident(rname)],
        None => Seq::empty(),
    };
    let ghost s_def: Seq<TokenView> = match vc.default {
        Some(e) => seq![kwv(Keyword::Default)] + sprint_min(e, 0),
        None => Seq::empty(),
    };
    if c.primary_key {
        push_tok(&mut r, Token::Keyword(Keyword::Primary));
        push_tok(&mut r, Token::Keyword(Keyword::Key));
    }
    proof {
        assert(verified_production::token_views(r@) =~= head + s_pk);
    }
    match c.nullable {
        Some(b) => {
            if b {
                push_tok(&mut r, Token::Keyword(Keyword::Null));
            } else {
                push_tok(&mut r, Token::Keyword(Keyword::Not));
                push_tok(&mut r, Token::Keyword(Keyword::Null));
            }
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@) =~= head + s_pk + s_null);
    }
    if c.unique {
        push_tok(&mut r, Token::Keyword(Keyword::Unique));
    }
    if c.index {
        push_tok(&mut r, Token::Keyword(Keyword::Index));
    }
    proof {
        assert(verified_production::token_views(r@) =~= head + s_pk + s_null + s_uni + s_idx);
    }
    match &c.references {
        Some(rname) => {
            push_tok(&mut r, Token::Keyword(Keyword::References));
            push_tok(&mut r, Token::Ident(rname.clone()));
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= head + s_pk + s_null + s_uni + s_idx + s_ref);
    }
    match &c.default {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Default));
            proof {
                assert(vc.default == Some(verified_roundtrip::view_expr(*e)));
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= head + s_pk + s_null + s_uni + s_idx + s_ref + s_def);
        assert(sprint_constraints(vc) == s_pk + s_null + s_uni + s_idx + s_ref + s_def);
        assert(sprint_column(vc)
            =~= head + s_pk + s_null + s_uni + s_idx + s_ref + s_def);
    }
    r
}

/// Exec printer for the CREATE TABLE column list.
fn print_columns_slice(s: &[ast::Column]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_columns(verified_stmt::view_columns(s@)),
    ensures
        verified_production::token_views(r@) == sprint_columns(verified_stmt::view_columns(s@)),
    decreases s@.len(),
{
    let ghost vl = verified_stmt::view_columns(s@);
    proof {
        lemma_view_columns_len(s@);
        assert(vl == seq![verified_stmt::view_column(s@[0])]
            + verified_stmt::view_columns(s@.drop_first()));
        assert(vl[0] == verified_stmt::view_column(s@[0]));
        assert(vl.drop_first() =~= verified_stmt::view_columns(s@.drop_first()));
    }
    let mut r = print_column_toks(&s[0]);
    if s.len() == 1 {
        proof {
            assert(sprint_columns(vl) == sprint_column(vl[0]));
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_columns_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_column(vl[0]) + seq![TokenView::Comma]
                    + sprint_columns(vl.drop_first()));
        }
        r
    }
}

/// `sprint_join_steps` distributes over append.
pub proof fn lemma_sprint_join_steps_append(a: Seq<SJoinStep>, b: Seq<SJoinStep>)
    ensures
        sprint_join_steps(a + b) == sprint_join_steps(a) + sprint_join_steps(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(sprint_join_steps(a) =~= Seq::<TokenView>::empty());
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_sprint_join_steps_append(a.drop_first(), b);
        assert(sprint_join_steps(a + b)
            =~= sprint_join_step(a[0]) + (sprint_join_steps(a.drop_first())
                + sprint_join_steps(b)));
        assert(sprint_join_steps(a) == sprint_join_step(a[0]) + sprint_join_steps(a.drop_first()));
    }
}

/// The print of a join tree decomposes into the left subtree's print followed
/// by the topmost step's print.
pub proof fn lemma_sprint_from_item_join(
    left: SFrom,
    right: SFrom,
    join_type: ast::JoinType,
    predicate: Option<SExpr>,
)
    ensures
        sprint_from_item(SFrom::Join {
            left: Box::new(left), right: Box::new(right), join_type, predicate,
        }) == sprint_from_item(left)
            + sprint_join_step(SJoinStep { join_type, right, predicate }),
{
    let f = SFrom::Join { left: Box::new(left), right: Box::new(right), join_type, predicate };
    let st = SJoinStep { join_type, right, predicate };
    assert(from_head(f) == from_head(left));
    assert(from_steps(f) =~= from_steps(left) + seq![st]);
    lemma_sprint_join_steps_append(from_steps(left), seq![st]);
    assert(sprint_join_steps(seq![st]) =~= sprint_join_step(st)) by {
        assert(seq![st][0] == st);
        assert(seq![st].drop_first() =~= Seq::<SJoinStep>::empty());
        assert(sprint_join_steps(seq![st].drop_first()) =~= Seq::<TokenView>::empty());
    }
    assert(sprint_from_item(f)
        =~= (sprint_table(from_head(left)) + sprint_join_steps(from_steps(left)))
            + sprint_join_step(st));
}

/// Exec printer for one FROM item (a left-deep join tree).
#[verifier::spinoff_prover]
#[verifier::rlimit(300000)]
fn print_from_item_toks(f: &ast::From) -> (r: Vec<Token>)
    requires
        printable_sfrom(verified_stmt::view_from(*f)),
    ensures
        verified_production::token_views(r@) == sprint_from_item(verified_stmt::view_from(*f)),
    decreases *f,
{
    let ghost vf = verified_stmt::view_from(*f);
    match f {
        ast::From::Table { name, alias } => {
            let mut r: Vec<Token> = Vec::new();
            push_tok(&mut r, Token::Ident(name.clone()));
            match alias {
                Some(a) => {
                    push_tok(&mut r, Token::Keyword(Keyword::As));
                    push_tok(&mut r, Token::Ident(a.clone()));
                },
                None => {},
            }
            proof {
                assert(vf is Table);
                assert(from_head(vf) == vf);
                assert(from_steps(vf) =~= Seq::<SJoinStep>::empty());
                assert(sprint_join_steps(from_steps(vf)) =~= Seq::<TokenView>::empty());
                assert(verified_production::token_views(r@) =~= sprint_table(vf));
                assert(sprint_from_item(vf) =~= sprint_table(vf));
            }
            r
        },
        ast::From::Join { left, right, join_type, predicate } => {
            let ghost vleft = verified_stmt::view_from(*(*left));
            let ghost vright = verified_stmt::view_from(*(*right));
            let ghost vpred = verified_stmt::view_opt(*predicate);
            let ghost st = SJoinStep { join_type: *join_type, right: vright, predicate: vpred };
            proof {
                assert(vf == SFrom::Join {
                    left: Box::new(vleft), right: Box::new(vright),
                    join_type: *join_type, predicate: vpred,
                });
                assert(printable_sfrom(vleft));
                assert(printable_step(st));
            }
            let mut r = print_from_item_toks(&**left);
            match join_type {
                ast::JoinType::Inner => {
                    push_tok(&mut r, Token::Keyword(Keyword::Join));
                },
                ast::JoinType::Cross => {
                    push_tok(&mut r, Token::Keyword(Keyword::Cross));
                    push_tok(&mut r, Token::Keyword(Keyword::Join));
                },
                ast::JoinType::Left => {
                    push_tok(&mut r, Token::Keyword(Keyword::Left));
                    push_tok(&mut r, Token::Keyword(Keyword::Join));
                },
                ast::JoinType::Right => {
                    push_tok(&mut r, Token::Keyword(Keyword::Right));
                    push_tok(&mut r, Token::Keyword(Keyword::Join));
                },
            }
            proof {
                assert(verified_production::token_views(r@)
                    =~= sprint_from_item(vleft) + join_kw_toks(*join_type));
            }
            // The right side is a base table in the printable domain.
            match &**right {
                ast::From::Table { name, alias } => {
                    push_tok(&mut r, Token::Ident(name.clone()));
                    match alias {
                        Some(a) => {
                            push_tok(&mut r, Token::Keyword(Keyword::As));
                            push_tok(&mut r, Token::Ident(a.clone()));
                        },
                        None => {},
                    }
                    proof {
                        assert(vright is Table);
                        assert(verified_production::token_views(r@)
                            =~= sprint_from_item(vleft) + join_kw_toks(*join_type)
                                + sprint_table(vright));
                    }
                },
                ast::From::Join { .. } => {
                    proof {
                        assert(vright is Join);
                        assert(!(st.right is Table));
                        assert(false);
                    }
                },
            }
            match predicate {
                Some(e) => {
                    push_tok(&mut r, Token::Keyword(Keyword::On));
                    proof {
                        assert(vpred == Some(verified_roundtrip::view_expr(*e)));
                        assert(printable_se(verified_roundtrip::view_expr(*e)));
                    }
                    let ex = verified_minparen::print_min_at(e, 0);
                    append_toks(&mut r, ex);
                },
                None => {},
            }
            proof {
                assert(verified_production::token_views(r@)
                    =~= sprint_from_item(vleft) + sprint_join_step(st));
                lemma_sprint_from_item_join(vleft, vright, *join_type, vpred);
                assert(sprint_from_item(vf)
                    == sprint_from_item(vleft) + sprint_join_step(st));
            }
            r
        },
    }
}

/// Exec printer for the FROM item list.
fn print_from_items_slice(s: &[ast::From]) -> (r: Vec<Token>)
    requires
        s@.len() >= 1,
        printable_froms(verified_stmt::view_froms(s@)),
    ensures
        verified_production::token_views(r@) == sprint_from_items(verified_stmt::view_froms(s@)),
    decreases s@.len(),
{
    let ghost vl = verified_stmt::view_froms(s@);
    proof {
        lemma_view_froms_len(s@);
        assert(vl == seq![verified_stmt::view_from(s@[0])]
            + verified_stmt::view_froms(s@.drop_first()));
        assert(vl[0] == verified_stmt::view_from(s@[0]));
        assert(vl.drop_first() =~= verified_stmt::view_froms(s@.drop_first()));
    }
    let mut r = print_from_item_toks(&s[0]);
    if s.len() == 1 {
        proof {
            assert(sprint_from_items(vl) == sprint_from_item(vl[0]));
        }
        r
    } else {
        push_tok(&mut r, Token::Comma);
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof {
            assert(rest@ =~= s@.drop_first());
        }
        let more = print_from_items_slice(rest);
        append_toks(&mut r, more);
        proof {
            assert(verified_production::token_views(r@)
                =~= sprint_from_item(vl[0]) + seq![TokenView::Comma]
                    + sprint_from_items(vl.drop_first()));
        }
        r
    }
}

/// The UPDATE arm of the statement printer, split out so each spinoff query
/// stays within the solver's reach.
#[verifier::spinoff_prover]
#[verifier::rlimit(400000)]
fn print_min_update_stmt(
    table: &String,
    set: &BTreeMap<String, Option<ast::Expression>>,
    where_clause: &Option<ast::Expression>,
) -> (r: Vec<Token>)
    requires
        printable_stmt(verified_stmt::view_update_arm(*table, set@, *where_clause)),
    ensures
        verified_production::token_views(r@)
            == sprint_min_stmt(verified_stmt::view_update_arm(*table, set@, *where_clause)),
{
    let ghost vs = verified_stmt::view_update_arm(*table, set@, *where_clause);
    let mut r: Vec<Token> = Vec::new();
    proof {
        broadcast use vstd::std_specs::btree::axiom_key_obeys_cmp_spec_meaning;

        verified_stmt::axiom_string_obeys_cmp();
        assert(vstd::std_specs::btree::key_obeys_cmp_spec::<String>());
        // In the printable domain the assignment map is a singleton (otherwise
        // `view_update_arm` yields `Unsupported`, which is not printable).
        if set@.dom().len() != 1 {
            assert(vs == SStmt::Unsupported);
            assert(false);
        }
        assert(set@.dom().len() == 1);
    }
    let ghost k0 = set@.dom().choose();
    let ghost vset: Seq<(String, Option<SExpr>)> = seq![(k0, verified_stmt::view_opt(set@[k0]))];
    proof {
        assert(vs == SStmt::Update {
            table: *table,
            set: vset,
            where_clause: verified_stmt::view_opt(*where_clause),
        });
    }
    push_tok(&mut r, Token::Keyword(Keyword::Update));
    push_tok(&mut r, Token::Ident(table.clone()));
    push_tok(&mut r, Token::Keyword(Keyword::Set));
    let mut it = set.iter();
    let ghost rem0 = vstd::std_specs::iter::IteratorSpec::remaining(&it);
    proof {
        broadcast use vstd::std_specs::btree::axiom_key_obeys_cmp_spec_meaning;

        assert(rem0.len() == set@.dom().len());
        // The sole pair in `remaining` is `(k0, set@[k0])`.
        assert(set@.dom().contains(k0)) by {
            assert(rem0.len() == 1);
            assert(set@.contains_key(*rem0[0].0));
        }
        assert(set@.contains_key(k0));
        assert(rem0.contains((&k0, &set@[k0])));
        assert(rem0[0] == (&k0, &set@[k0]));
    }
    let kv = it.next();
    match kv {
        Some(pair) => {
            let (k, v) = pair;
            proof {
                assert((k, v) == rem0[0]);
                assert(*k == k0);
                assert(*v == set@[k0]);
            }
            push_tok(&mut r, Token::Ident(k.clone()));
            push_tok(&mut r, Token::Equal);
            match v {
                Some(e) => {
                    proof {
                        assert(verified_stmt::view_opt(set@[k0])
                            == Some(verified_roundtrip::view_expr(*e)));
                        assert(printable_opt_se(vset[0].1));
                        assert(printable_se(verified_roundtrip::view_expr(*e)));
                    }
                    let ex = verified_minparen::print_min_at(e, 0);
                    append_toks(&mut r, ex);
                },
                None => {
                    push_tok(&mut r, Token::Keyword(Keyword::Default));
                },
            }
            proof {
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Update), TokenView::Ident(*table), kwv(Keyword::Set)]
                        + sprint_assign(vset[0]));
            }
        },
        None => {
            proof {
                assert(rem0.len() == 1);
                assert(false);
            }
        },
    }
    match where_clause {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Where));
            proof {
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Update), TokenView::Ident(*table), kwv(Keyword::Set)]
                + sprint_assign(vset[0])
                + sprint_kw_expr(Keyword::Where, verified_stmt::view_opt(*where_clause)));
        assert(sprint_min_stmt(vs)
            == seq![kwv(Keyword::Update), TokenView::Ident(*table), kwv(Keyword::Set)]
                + sprint_assign(vset[0])
                + sprint_kw_expr(Keyword::Where, verified_stmt::view_opt(*where_clause)));
    }
    r
}

/// The SELECT arm of the statement printer, split out so each spinoff query
/// stays within the solver's reach.
#[verifier::spinoff_prover]
#[verifier::rlimit(600000)]
fn print_min_select_stmt(
    select: &Vec<(ast::Expression, Option<String>)>,
    from: &Vec<ast::From>,
    where_clause: &Option<ast::Expression>,
    group_by: &Vec<ast::Expression>,
    having: &Option<ast::Expression>,
    order_by: &Vec<(ast::Expression, ast::Direction)>,
    limit: &Option<ast::Expression>,
    offset: &Option<ast::Expression>,
) -> (r: Vec<Token>)
    requires
        verified_stmt::view_select_list(select@).len() >= 1,
        printable_select_items(verified_stmt::view_select_list(select@)),
        printable_froms(verified_stmt::view_froms(from@)),
        printable_opt_se(verified_stmt::view_opt(*where_clause)),
        printable_exprs(verified_roundtrip::view_args(group_by@)),
        printable_opt_se(verified_stmt::view_opt(*having)),
        printable_order_items(verified_stmt::view_order_list(order_by@)),
        printable_opt_se(verified_stmt::view_opt(*limit)),
        printable_opt_se(verified_stmt::view_opt(*offset)),
    ensures
        verified_production::token_views(r@)
            == seq![kwv(Keyword::Select)] + sprint_select_body(
                verified_stmt::view_select_list(select@),
                verified_stmt::view_froms(from@),
                verified_stmt::view_opt(*where_clause),
                verified_roundtrip::view_args(group_by@),
                verified_stmt::view_opt(*having),
                verified_stmt::view_order_list(order_by@),
                verified_stmt::view_opt(*limit),
                verified_stmt::view_opt(*offset)),
{
    let ghost v_select = verified_stmt::view_select_list(select@);
    let ghost v_from = verified_stmt::view_froms(from@);
    let ghost v_where = verified_stmt::view_opt(*where_clause);
    let ghost v_group = verified_roundtrip::view_args(group_by@);
    let ghost v_having = verified_stmt::view_opt(*having);
    let ghost v_order = verified_stmt::view_order_list(order_by@);
    let ghost v_limit = verified_stmt::view_opt(*limit);
    let ghost v_offset = verified_stmt::view_opt(*offset);
    let mut r: Vec<Token> = Vec::new();
    proof {
        lemma_view_select_list_len(select@);
        lemma_view_froms_len(from@);
        verified_roundtrip::view_args_len(group_by@);
        lemma_view_order_list_len(order_by@);
    }
    push_tok(&mut r, Token::Keyword(Keyword::Select));
    let items = print_select_items_slice(select.as_slice());
    append_toks(&mut r, items);
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_items(v_select));
    }
    if from.len() > 0 {
        push_tok(&mut r, Token::Keyword(Keyword::From));
        let fi = print_from_items_slice(from.as_slice());
        append_toks(&mut r, fi);
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_items(v_select)
                + sprint_from_clause(v_from));
    }
    match where_clause {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Where));
            proof {
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_items(v_select)
                + sprint_from_clause(v_from)
                + sprint_kw_expr(Keyword::Where, v_where));
    }
    if group_by.len() > 0 {
        push_tok(&mut r, Token::Keyword(Keyword::Group));
        push_tok(&mut r, Token::Keyword(Keyword::By));
        let g = print_exprs_slice(group_by.as_slice());
        append_toks(&mut r, g);
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_items(v_select)
                + sprint_from_clause(v_from)
                + sprint_kw_expr(Keyword::Where, v_where)
                + sprint_group_by(v_group));
    }
    match having {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Having));
            proof {
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    if order_by.len() > 0 {
        push_tok(&mut r, Token::Keyword(Keyword::Order));
        push_tok(&mut r, Token::Keyword(Keyword::By));
        let o = print_order_items_slice(order_by.as_slice());
        append_toks(&mut r, o);
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_items(v_select)
                + sprint_from_clause(v_from)
                + sprint_kw_expr(Keyword::Where, v_where)
                + sprint_group_by(v_group)
                + sprint_kw_expr(Keyword::Having, v_having)
                + sprint_order_by(v_order));
    }
    match limit {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Limit));
            proof {
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    match offset {
        Some(e) => {
            push_tok(&mut r, Token::Keyword(Keyword::Offset));
            proof {
                assert(printable_se(verified_roundtrip::view_expr(*e)));
            }
            let ex = verified_minparen::print_min_at(e, 0);
            append_toks(&mut r, ex);
        },
        None => {},
    }
    proof {
        assert(verified_production::token_views(r@)
            =~= seq![kwv(Keyword::Select)] + sprint_select_body(
                v_select, v_from, v_where, v_group, v_having, v_order, v_limit, v_offset));
    }
    r
}

/// The executable min-parens statement printer: a real `Vec<Token>` whose
/// token view is `sprint_min_stmt(view_stmt(*s))` — the spec printer applied
/// to the statement's mirror.
#[verifier::spinoff_prover]
#[verifier::rlimit(400000)]
pub fn print_min_stmt(s: &ast::Statement) -> (r: Vec<Token>)
    requires
        printable_stmt(verified_stmt::view_stmt(*s)),
    ensures
        verified_production::token_views(r@) == sprint_min_stmt(verified_stmt::view_stmt(*s)),
    decreases *s,
{
    let ghost vs = verified_stmt::view_stmt(*s);
    let mut r: Vec<Token> = Vec::new();
    match s {
        ast::Statement::Commit => {
            push_tok(&mut r, Token::Keyword(Keyword::Commit));
            proof {
                assert(verified_production::token_views(r@) =~= sprint_min_stmt(vs));
            }
            r
        },
        ast::Statement::Rollback => {
            push_tok(&mut r, Token::Keyword(Keyword::Rollback));
            proof {
                assert(verified_production::token_views(r@) =~= sprint_min_stmt(vs));
            }
            r
        },
        ast::Statement::Begin { read_only, as_of } => {
            push_tok(&mut r, Token::Keyword(Keyword::Begin));
            if *read_only {
                push_tok(&mut r, Token::Keyword(Keyword::Read));
                push_tok(&mut r, Token::Keyword(Keyword::Only));
            }
            match as_of {
                Some(v) => {
                    push_tok(&mut r, Token::Keyword(Keyword::As));
                    push_tok(&mut r, Token::Keyword(Keyword::Of));
                    push_tok(&mut r, Token::Keyword(Keyword::System));
                    push_tok(&mut r, Token::Keyword(Keyword::Time));
                    let digits = verified_integer::print_u64(*v);
                    push_tok(&mut r, Token::Number(digits));
                },
                None => {},
            }
            proof {
                assert(vs == SStmt::Begin { read_only: *read_only, as_of: *as_of });
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Begin)] + sprint_begin_body(*read_only, *as_of));
            }
            r
        },
        ast::Statement::DropTable { name, if_exists } => {
            push_tok(&mut r, Token::Keyword(Keyword::Drop));
            push_tok(&mut r, Token::Keyword(Keyword::Table));
            if *if_exists {
                push_tok(&mut r, Token::Keyword(Keyword::If));
                push_tok(&mut r, Token::Keyword(Keyword::Exists));
            }
            push_tok(&mut r, Token::Ident(name.clone()));
            proof {
                assert(vs == SStmt::DropTable { name: *name, if_exists: *if_exists });
                assert(verified_production::token_views(r@) =~= sprint_min_stmt(vs));
            }
            r
        },
        ast::Statement::Delete { table, where_clause } => {
            push_tok(&mut r, Token::Keyword(Keyword::Delete));
            push_tok(&mut r, Token::Keyword(Keyword::From));
            push_tok(&mut r, Token::Ident(table.clone()));
            proof {
                assert(vs == SStmt::Delete {
                    table: *table,
                    where_clause: verified_stmt::view_opt(*where_clause),
                });
            }
            match where_clause {
                Some(e) => {
                    push_tok(&mut r, Token::Keyword(Keyword::Where));
                    proof {
                        assert(printable_se(verified_roundtrip::view_expr(*e)));
                    }
                    let ex = verified_minparen::print_min_at(e, 0);
                    append_toks(&mut r, ex);
                },
                None => {},
            }
            proof {
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Delete), kwv(Keyword::From), TokenView::Ident(*table)]
                        + sprint_kw_expr(Keyword::Where, verified_stmt::view_opt(*where_clause)));
            }
            r
        },
        ast::Statement::CreateTable { name, columns } => {
            push_tok(&mut r, Token::Keyword(Keyword::Create));
            push_tok(&mut r, Token::Keyword(Keyword::Table));
            push_tok(&mut r, Token::Ident(name.clone()));
            push_tok(&mut r, Token::OpenParen);
            proof {
                assert(vs == SStmt::CreateTable {
                    name: *name,
                    columns: verified_stmt::view_columns(columns@),
                });
                lemma_view_columns_len(columns@);
            }
            let cols = print_columns_slice(columns.as_slice());
            append_toks(&mut r, cols);
            push_tok(&mut r, Token::CloseParen);
            proof {
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Create), kwv(Keyword::Table), TokenView::Ident(*name),
                        TokenView::OpenParen]
                        + sprint_columns(verified_stmt::view_columns(columns@))
                        + seq![TokenView::CloseParen]);
            }
            r
        },
        ast::Statement::Insert { table, columns, values } => {
            push_tok(&mut r, Token::Keyword(Keyword::Insert));
            push_tok(&mut r, Token::Keyword(Keyword::Into));
            push_tok(&mut r, Token::Ident(table.clone()));
            let ghost vcols: Option<Seq<String>> = match columns {
                Some(cols) => Some(cols@),
                None => None,
            };
            proof {
                assert(vs == SStmt::Insert {
                    table: *table,
                    columns: vcols,
                    values: verified_stmt::view_rows(values@),
                });
            }
            match columns {
                Some(cols) => {
                    push_tok(&mut r, Token::OpenParen);
                    let c = print_idents_slice(cols.as_slice());
                    append_toks(&mut r, c);
                    push_tok(&mut r, Token::CloseParen);
                },
                None => {},
            }
            push_tok(&mut r, Token::Keyword(Keyword::Values));
            proof {
                lemma_view_rows_len(values@);
            }
            let rows = print_rows_slice(values.as_slice());
            append_toks(&mut r, rows);
            proof {
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Insert), kwv(Keyword::Into), TokenView::Ident(*table)]
                        + (match vcols {
                            Some(cs) => seq![TokenView::OpenParen] + sprint_idents(cs)
                                + seq![TokenView::CloseParen],
                            None => Seq::<TokenView>::empty(),
                        })
                        + seq![kwv(Keyword::Values)]
                        + sprint_rows(verified_stmt::view_rows(values@)));
            }
            r
        },
        ast::Statement::Update { table, set, where_clause } => {
            proof {
                assert(vs == verified_stmt::view_update_arm(*table, set@, *where_clause));
            }
            print_min_update_stmt(table, set, where_clause)
        },
        ast::Statement::Select {
            select, from, where_clause, group_by, having, order_by, offset, limit,
        } => {
            proof {
                assert(vs == SStmt::Select {
                    select: verified_stmt::view_select_list(select@),
                    from: verified_stmt::view_froms(from@),
                    where_clause: verified_stmt::view_opt(*where_clause),
                    group_by: verified_roundtrip::view_args(group_by@),
                    having: verified_stmt::view_opt(*having),
                    order_by: verified_stmt::view_order_list(order_by@),
                    limit: verified_stmt::view_opt(*limit),
                    offset: verified_stmt::view_opt(*offset),
                });
            }
            print_min_select_stmt(
                select, from, where_clause, group_by, having, order_by, limit, offset)
        },
        ast::Statement::Explain(inner) => {
            push_tok(&mut r, Token::Keyword(Keyword::Explain));
            proof {
                assert(vs == SStmt::Explain(Box::new(verified_stmt::view_stmt(*(*inner)))));
                assert(printable_stmt(verified_stmt::view_stmt(*(*inner))));
            }
            let it = print_min_stmt(&**inner);
            append_toks(&mut r, it);
            proof {
                assert(verified_production::token_views(r@)
                    =~= seq![kwv(Keyword::Explain)]
                        + sprint_min_stmt(verified_stmt::view_stmt(*(*inner))));
            }
            r
        },
    }
}

// ===========================================================================
// Task 4 remainder — the live statement roundtrip over the executable printer.
// ===========================================================================

/// HEADLINE (task 4, live): the production statement parser recovers a
/// printable statement from its executable min-parens print, up to
/// `view_stmt`, consuming every token:
///
///   parse_control_at(print_min_stmt(s), 0)
///       == (Some(s'), print_min_stmt(s).len(), _)  with view_stmt(s') == view_stmt(s).
///
/// This lifts `stmt_min_roundtrip` (a `sparse_control` fact) through phase 6
/// task 2's refinement of the dispatch to the live code path: the whole
/// statement grammar — keyword skeleton, clause sequencing, list separators,
/// join folding, and the precedence/associativity table in every expression
/// position — provably inverts the min-parens printer.
#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
pub fn stmt_min_roundtrip_live(s: &ast::Statement) -> (r: (
    Option<ast::Statement>,
    usize,
    Option<ParseError>,
))
    requires
        printable_stmt(verified_stmt::view_stmt(*s)),
        sprint_min_stmt(verified_stmt::view_stmt(*s)).len() <= (usize::MAX - 3) / 2,
    ensures
        r.0 is Some,
        verified_stmt::view_stmt(r.0->Some_0) == verified_stmt::view_stmt(*s),
        r.1 == sprint_min_stmt(verified_stmt::view_stmt(*s)).len(),
{
    let ghost vs = verified_stmt::view_stmt(*s);
    let toks = print_min_stmt(s);
    proof {
        verified_roundtrip::token_views_len(toks@);
        assert(toks@.len() == sprint_min_stmt(vs).len());
    }
    let (opt, pos, err) = verified_control::parse_control_at(&toks, 0);
    proof {
        assert(toks@.subrange(0, toks@.len() as int) =~= toks@);
        assert(verified_production::token_views(toks@.subrange(0, toks@.len() as int))
            == sprint_min_stmt(vs));
        stmt_min_roundtrip(vs);
        assert(verified_stmt_prec::sparse_control(sprint_min_stmt(vs))
            == (Some(vs), Seq::<TokenView>::empty()));
        assert(opt is Some);
        assert(verified_stmt::view_stmt(opt->Some_0) == vs);
        verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        assert(verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            == Seq::<TokenView>::empty());
        assert(pos == toks@.len());
    }
    (opt, pos, err)
}

} // verus!
