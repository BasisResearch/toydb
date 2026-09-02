#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_precedence::sparse_prec;
#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::SExpr;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::{SColumn, SFrom, SStmt};
#[allow(unused_imports)]
use super::{
    Keyword, ast, verified_precedence, verified_production, verified_roundtrip, verified_stmt,
};
#[allow(unused_imports)]
use crate::sql::types::DataType;

verus! {


pub open spec fn expr_fuel(input: Seq<TokenView>) -> nat {
    (2 * input.len() + 3) as nat
}


pub open spec fn sparse_control_delete(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 2 || input[0] != TokenView::Keyword(Keyword::From) {
        (None, input)
    } else {
        match input[1] {
            TokenView::Ident(table) => {
                let r = input.drop_first().drop_first();
                if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Where) {
                    let e_in = r.drop_first();
                    match sparse_prec(e_in, 0, expr_fuel(e_in)) {
                        (Some(e), rest) => (
                            Some(SStmt::Delete { table, where_clause: Some(e) }),
                            rest,
                        ),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(SStmt::Delete { table, where_clause: None }), r)
                }
            },
            _ => (None, input),
        }
    }
}


pub open spec fn sparse_control_drop(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Table) {
        (None, input)
    } else {
        let has_if = input.len() >= 2 && input[1] == TokenView::Keyword(Keyword::If);
        let has_if_exists = input.len() >= 3
            && input[1] == TokenView::Keyword(Keyword::If)
            && input[2] == TokenView::Keyword(Keyword::Exists);
        if has_if && !has_if_exists {
            (None, input)
        } else {
            let if_exists = has_if_exists;
            let r = if has_if_exists {
                input.drop_first().drop_first().drop_first()
            } else {
                input.drop_first()
            };
            if r.len() < 1 {
                (None, input)
            } else {
                match r[0] {
                    TokenView::Ident(name) => (
                        Some(SStmt::DropTable { name, if_exists }),
                        r.drop_first(),
                    ),
                    _ => (None, input),
                }
            }
        }
    }
}


pub open spec fn sparse_control_begin(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    let r0 = if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Transaction) {
        input.drop_first()
    } else {
        input
    };
    let read_res: Option<(bool, Seq<TokenView>)> =
        if r0.len() >= 1 && r0[0] == TokenView::Keyword(Keyword::Read) {
            let r1 = r0.drop_first();
            if r1.len() < 1 {
                None
            } else if r1[0] == TokenView::Keyword(Keyword::Only) {
                Some((true, r1.drop_first()))
            } else if r1[0] == TokenView::Keyword(Keyword::Write) {
                Some((false, r1.drop_first()))
            } else {
                None
            }
        } else {
            Some((false, r0))
        };
    match read_res {
        None => (None, input),
        Some((read_only, r2)) => {
            if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::As) {
                let r3 = r2.drop_first();
                if r3.len() < 1 || r3[0] != TokenView::Keyword(Keyword::Of) {
                    (None, input)
                } else {
                    let r4 = r3.drop_first();
                    if r4.len() < 1 || r4[0] != TokenView::Keyword(Keyword::System) {
                        (None, input)
                    } else {
                        let r5 = r4.drop_first();
                        if r5.len() < 1 || r5[0] != TokenView::Keyword(Keyword::Time) {
                            (None, input)
                        } else {
                            let r6 = r5.drop_first();
                            if r6.len() < 1 {
                                (None, input)
                            } else {
                                match r6[0] {
                                    TokenView::Number(bytes) =>
                                        match super::verified_integer::parse_digits_spec(bytes) {
                                            Some(version) => (
                                                Some(SStmt::Begin { read_only, as_of: Some(version) }),
                                                r6.drop_first(),
                                            ),
                                            None => (None, input),
                                        },
                                    _ => (None, input),
                                }
                            }
                        }
                    }
                }
            } else {
                (Some(SStmt::Begin { read_only, as_of: None }), r2)
            }
        },
    }
}


pub open spec fn sparse_control_order_list(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_order_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            let (d, r1) = if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc) {
                (ast::Direction::Ascending, r.drop_first())
            } else if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc) {
                (ast::Direction::Descending, r.drop_first())
            } else {
                (ast::Direction::Ascending, r)
            };
            if r1.len() >= 1 && r1[0] == TokenView::Comma {
                match sparse_control_order_list(r1.drop_first()) {
                    (Some(more), r2) => (Some(seq![(e, d)] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![(e, d)]), r1)
            }
        },
        (None, _) => (None, input),
    }
}

#[via_fn]
proof fn sparse_control_order_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
}

pub open spec fn sparse_control_order_by(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>)
{
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Order) {
        (Some(Seq::<(SExpr, ast::Direction)>::empty()), input)
    } else if input.len() < 2 || input[1] != TokenView::Keyword(Keyword::By) {
        (None, input)
    } else {
        let r = input.drop_first().drop_first();
        match sparse_control_order_list(r) {
            (Some(items), rest) => (Some(items), rest),
            (None, _) => (None, input),
        }
    }
}

pub proof fn lemma_view_order_list_append(
    a: Seq<(ast::Expression, ast::Direction)>,
    b: Seq<(ast::Expression, ast::Direction)>,
)
    ensures
        verified_stmt::view_order_list(a + b)
            == verified_stmt::view_order_list(a) + verified_stmt::view_order_list(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_order_list, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_order_list_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_order_list_single(expr: ast::Expression, d: ast::Direction)
    ensures
        verified_stmt::view_order_list(seq![(expr, d)])
            == seq![(verified_roundtrip::view_expr(expr), d)],
{
    reveal_with_fuel(verified_stmt::view_order_list, 2);
    let s = seq![(expr, d)];
    assert(s.len() == 1);
    assert(s[0] == (expr, d));
    assert(s.drop_first() =~= Seq::<(ast::Expression, ast::Direction)>::empty());
    assert(verified_stmt::view_order_list(s.drop_first())
        =~= Seq::<(SExpr, ast::Direction)>::empty());
    assert(verified_stmt::view_order_list(s)
        =~= seq![(verified_roundtrip::view_expr(expr), d)]);
}

pub open spec fn order_list_prepend(
    done: Seq<(SExpr, ast::Direction)>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>),
) -> (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_order_list_step(cur: Seq<TokenView>, e: SExpr, d: ast::Direction, r: Seq<TokenView>, r1: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc)) ==> d == ast::Direction::Ascending && r1 == r.drop_first(),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc)) ==> d == ast::Direction::Descending && r1 == r.drop_first(),
        !(r.len() >= 1 && (r[0] == TokenView::Keyword(Keyword::Asc) || r[0] == TokenView::Keyword(Keyword::Desc)))
            ==> d == ast::Direction::Ascending && r1 == r,
        r1.len() >= 1,
        r1[0] == TokenView::Comma,
    ensures
        sparse_control_order_list(cur)
            == order_list_prepend(seq![(e, d)], cur, sparse_control_order_list(r1.drop_first())),
{
    match sparse_control_order_list(r1.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_order_list(cur) == (Some(seq![(e, d)] + more), r2));
            assert(seq![(e, d)] + more == seq![(e, d)] + more);
        },
        (None, _) => {
            assert(sparse_control_order_list(cur) == (None::<Seq<(SExpr, ast::Direction)>>, cur));
        },
    }
}

pub proof fn lemma_order_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<(SExpr, ast::Direction)>,
    se: SExpr,
    d: ast::Direction,
    whole: (Option<Seq<(SExpr, ast::Direction)>>, Seq<TokenView>),
)
    requires
        whole == order_list_prepend(done, ls, sparse_control_order_list(cur)),
        sparse_control_order_list(cur)
            == order_list_prepend(seq![(se, d)], cur, sparse_control_order_list(cur1)),
    ensures
        whole == order_list_prepend(done + seq![(se, d)], ls, sparse_control_order_list(cur1)),
{
    match sparse_control_order_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![(se, d)] + more) == (done + seq![(se, d)]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_order_list_last(cur: Seq<TokenView>, e: SExpr, d: ast::Direction, r: Seq<TokenView>, r1: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Asc)) ==> d == ast::Direction::Ascending && r1 == r.drop_first(),
        (r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Desc)) ==> d == ast::Direction::Descending && r1 == r.drop_first(),
        !(r.len() >= 1 && (r[0] == TokenView::Keyword(Keyword::Asc) || r[0] == TokenView::Keyword(Keyword::Desc)))
            ==> d == ast::Direction::Ascending && r1 == r,
        !(r1.len() >= 1 && r1[0] == TokenView::Comma),
    ensures
        sparse_control_order_list(cur) == (Some(seq![(e, d)]), r1),
{
}


pub open spec fn sparse_control_group_list(input: Seq<TokenView>)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_group_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_group_list(r.drop_first()) {
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

#[via_fn]
proof fn sparse_control_group_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
}

pub open spec fn sparse_control_group_by(input: Seq<TokenView>)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
{
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Group) {
        (Some(Seq::<SExpr>::empty()), input)
    } else if input.len() < 2 || input[1] != TokenView::Keyword(Keyword::By) {
        (None, input)
    } else {
        let r = input.drop_first().drop_first();
        match sparse_control_group_list(r) {
            (Some(items), rest) => (Some(items), rest),
            (None, _) => (None, input),
        }
    }
}

pub proof fn lemma_view_args_append(
    a: Seq<ast::Expression>,
    b: Seq<ast::Expression>,
)
    ensures
        verified_roundtrip::view_args(a + b)
            == verified_roundtrip::view_args(a) + verified_roundtrip::view_args(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_roundtrip::view_args, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_args_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_args_single(expr: ast::Expression)
    ensures
        verified_roundtrip::view_args(seq![expr]) == seq![verified_roundtrip::view_expr(expr)],
{
    reveal_with_fuel(verified_roundtrip::view_args, 2);
    let s = seq![expr];
    assert(s.len() == 1);
    assert(s[0] == expr);
    assert(s.drop_first() =~= Seq::<ast::Expression>::empty());
    assert(verified_roundtrip::view_args(s.drop_first()) =~= Seq::<SExpr>::empty());
    assert(verified_roundtrip::view_args(s) =~= seq![verified_roundtrip::view_expr(expr)]);
}

pub open spec fn group_list_prepend(
    done: Seq<SExpr>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<SExpr>>, Seq<TokenView>),
) -> (Option<Seq<SExpr>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_group_list_step(cur: Seq<TokenView>, e: SExpr, r: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_group_list(cur)
            == group_list_prepend(seq![e], cur, sparse_control_group_list(r.drop_first())),
{
    match sparse_control_group_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_group_list(cur) == (Some(seq![e] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_group_list(cur) == (None::<Seq<SExpr>>, cur));
        },
    }
}

pub proof fn lemma_group_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<SExpr>,
    se: SExpr,
    whole: (Option<Seq<SExpr>>, Seq<TokenView>),
)
    requires
        whole == group_list_prepend(done, ls, sparse_control_group_list(cur)),
        sparse_control_group_list(cur)
            == group_list_prepend(seq![se], cur, sparse_control_group_list(cur1)),
    ensures
        whole == group_list_prepend(done + seq![se], ls, sparse_control_group_list(cur1)),
{
    match sparse_control_group_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![se] + more) == (done + seq![se]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_group_list_last(cur: Seq<TokenView>, e: SExpr, r: Seq<TokenView>)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_group_list(cur) == (Some(seq![e]), r),
{
}


pub open spec fn parse_column_datatype_kw(t: TokenView) -> Option<DataType> {
    match t {
        TokenView::Keyword(Keyword::Bool) => Some(DataType::Boolean),
        TokenView::Keyword(Keyword::Boolean) => Some(DataType::Boolean),
        TokenView::Keyword(Keyword::Float) => Some(DataType::Float),
        TokenView::Keyword(Keyword::Double) => Some(DataType::Float),
        TokenView::Keyword(Keyword::Int) => Some(DataType::Integer),
        TokenView::Keyword(Keyword::Integer) => Some(DataType::Integer),
        TokenView::Keyword(Keyword::String) => Some(DataType::String),
        TokenView::Keyword(Keyword::Text) => Some(DataType::String),
        TokenView::Keyword(Keyword::Varchar) => Some(DataType::String),
        _ => None,
    }
}

pub struct ColAcc {
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<SExpr>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

pub open spec fn col_from_acc(name: String, datatype: DataType, acc: ColAcc) -> SColumn {
    SColumn {
        name,
        datatype,
        primary_key: acc.primary_key,
        nullable: acc.nullable,
        default: acc.default,
        unique: acc.unique,
        index: acc.index,
        references: acc.references,
    }
}

pub open spec fn sparse_control_col_constraints(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
) -> (Option<SColumn>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_col_constraints_decreases
{
    if input.len() < 1 {
        (Some(col_from_acc(name, datatype, acc)), input)
    } else {
        match input[0] {
            TokenView::Keyword(k) => {
                let r = input.drop_first();
                if k == Keyword::Primary {
                    if r.len() < 1 || r[0] != TokenView::Keyword(Keyword::Key) {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r.drop_first(), name, datatype,
                            ColAcc { primary_key: true, ..acc })
                    }
                } else if k == Keyword::Null {
                    if acc.nullable is Some {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r, name, datatype,
                            ColAcc { nullable: Some(true), ..acc })
                    }
                } else if k == Keyword::Not {
                    if r.len() < 1 || r[0] != TokenView::Keyword(Keyword::Null) {
                        (None, input)
                    } else if acc.nullable is Some {
                        (None, input)
                    } else {
                        sparse_control_col_constraints(
                            r.drop_first(), name, datatype,
                            ColAcc { nullable: Some(false), ..acc })
                    }
                } else if k == Keyword::Default {
                    match sparse_prec(r, 0, expr_fuel(r)) {
                        (Some(e), r6) => sparse_control_col_constraints(
                            r6, name, datatype,
                            ColAcc { default: Some(e), ..acc }),
                        (None, _) => (None, input),
                    }
                } else if k == Keyword::Unique {
                    sparse_control_col_constraints(
                        r, name, datatype, ColAcc { unique: true, ..acc })
                } else if k == Keyword::Index {
                    sparse_control_col_constraints(
                        r, name, datatype, ColAcc { index: true, ..acc })
                } else if k == Keyword::References {
                    if r.len() < 1 {
                        (None, input)
                    } else {
                        match r[0] {
                            TokenView::Ident(n) => sparse_control_col_constraints(
                                r.drop_first(), name, datatype,
                                ColAcc { references: Some(n), ..acc }),
                            _ => (None, input),
                        }
                    }
                } else {
                    (None, input)
                }
            },
            _ => (Some(col_from_acc(name, datatype, acc)), input),
        }
    }
}

#[via_fn]
proof fn sparse_control_col_constraints_decreases(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
) {
    if input.len() >= 1 {
        let r = input.drop_first();
        verified_precedence::lemma_prec_slen(r, 0, expr_fuel(r));
    }
}

pub open spec fn opt_view_expr(d: Option<ast::Expression>) -> Option<SExpr> {
    match d {
        Some(e) => Some(verified_roundtrip::view_expr(e)),
        None => None,
    }
}

pub open spec fn col_acc_empty() -> ColAcc {
    ColAcc {
        primary_key: false,
        nullable: None,
        default: None,
        unique: false,
        index: false,
        references: None,
    }
}

pub open spec fn sparse_control_column(input: Seq<TokenView>) -> (Option<SColumn>, Seq<TokenView>) {
    if input.len() < 1 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                let r0 = input.drop_first();
                if r0.len() < 1 {
                    (None, input)
                } else {
                    match parse_column_datatype_kw(r0[0]) {
                        Some(datatype) => {
                            let r1 = r0.drop_first();
                            match sparse_control_col_constraints(r1, name, datatype, col_acc_empty()) {
                                (Some(c), rest) => (Some(c), rest),
                                (None, _) => (None, input),
                            }
                        },
                        None => (None, input),
                    }
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_control_column_list(input: Seq<TokenView>)
    -> (Option<Seq<SColumn>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_column_list_decreases
{
    match sparse_control_column(input) {
        (Some(c), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_column_list(r.drop_first()) {
                    (Some(more), r2) => (Some(seq![c] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![c]), r)
            }
        },
        (None, _) => (None, input),
    }
}

#[via_fn]
proof fn sparse_control_column_list_decreases(input: Seq<TokenView>) {
    lemma_control_column_slen(input);
}

pub proof fn lemma_control_column_slen(input: Seq<TokenView>)
    ensures
        sparse_control_column(input).1.len() <= input.len(),
        sparse_control_column(input).0 is Some ==> sparse_control_column(input).1.len() < input.len(),
{
    if input.len() >= 1 {
        match input[0] {
            TokenView::Ident(name) => {
                let r0 = input.drop_first();
                if r0.len() >= 1 {
                    match parse_column_datatype_kw(r0[0]) {
                        Some(datatype) => {
                            let r1 = r0.drop_first();
                            lemma_col_constraints_slen(r1, name, datatype, col_acc_empty());
                        },
                        None => {},
                    }
                }
            },
            _ => {},
        }
    }
}

pub proof fn lemma_col_constraints_slen(
    input: Seq<TokenView>,
    name: String,
    datatype: DataType,
    acc: ColAcc,
)
    ensures
        sparse_control_col_constraints(input, name, datatype, acc).1.len() <= input.len(),
    decreases input.len(),
{
    if input.len() >= 1 {
        match input[0] {
            TokenView::Keyword(k) => {
                let r = input.drop_first();
                if k == Keyword::Primary {
                    if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Key) {
                        lemma_col_constraints_slen(r.drop_first(), name, datatype,
                            ColAcc { primary_key: true, ..acc });
                    }
                } else if k == Keyword::Null {
                    if !(acc.nullable is Some) {
                        lemma_col_constraints_slen(r, name, datatype,
                            ColAcc { nullable: Some(true), ..acc });
                    }
                } else if k == Keyword::Not {
                    if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Null) && !(acc.nullable is Some) {
                        lemma_col_constraints_slen(r.drop_first(), name, datatype,
                            ColAcc { nullable: Some(false), ..acc });
                    }
                } else if k == Keyword::Default {
                    verified_precedence::lemma_prec_slen(r, 0, expr_fuel(r));
                    match sparse_prec(r, 0, expr_fuel(r)) {
                        (Some(e), r6) => lemma_col_constraints_slen(r6, name, datatype,
                            ColAcc { default: Some(e), ..acc }),
                        (None, _) => {},
                    }
                } else if k == Keyword::Unique {
                    lemma_col_constraints_slen(r, name, datatype, ColAcc { unique: true, ..acc });
                } else if k == Keyword::Index {
                    lemma_col_constraints_slen(r, name, datatype, ColAcc { index: true, ..acc });
                } else if k == Keyword::References {
                    if r.len() >= 1 {
                        match r[0] {
                            TokenView::Ident(n) => lemma_col_constraints_slen(r.drop_first(), name, datatype,
                                ColAcc { references: Some(n), ..acc }),
                            _ => {},
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

pub open spec fn column_list_prepend(
    done: Seq<SColumn>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<SColumn>>, Seq<TokenView>),
) -> (Option<Seq<SColumn>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_view_columns_append(
    a: Seq<ast::Column>,
    b: Seq<ast::Column>,
)
    ensures
        verified_stmt::view_columns(a + b)
            == verified_stmt::view_columns(a) + verified_stmt::view_columns(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_columns, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_columns_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_columns_single(c: ast::Column)
    ensures
        verified_stmt::view_columns(seq![c]) == seq![verified_stmt::view_column(c)],
{
    reveal_with_fuel(verified_stmt::view_columns, 2);
    let s = seq![c];
    assert(s.len() == 1);
    assert(s[0] == c);
    assert(s.drop_first() =~= Seq::<ast::Column>::empty());
    assert(verified_stmt::view_columns(s.drop_first()) =~= Seq::<SColumn>::empty());
    assert(verified_stmt::view_columns(s) =~= seq![verified_stmt::view_column(c)]);
}

pub proof fn lemma_column_list_step(cur: Seq<TokenView>, c: SColumn, r: Seq<TokenView>)
    requires
        sparse_control_column(cur) == (Some(c), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_column_list(cur)
            == column_list_prepend(seq![c], cur, sparse_control_column_list(r.drop_first())),
{
    match sparse_control_column_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_column_list(cur) == (Some(seq![c] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_column_list(cur) == (None::<Seq<SColumn>>, cur));
        },
    }
}

pub proof fn lemma_column_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<SColumn>,
    sc: SColumn,
    whole: (Option<Seq<SColumn>>, Seq<TokenView>),
)
    requires
        whole == column_list_prepend(done, ls, sparse_control_column_list(cur)),
        sparse_control_column_list(cur)
            == column_list_prepend(seq![sc], cur, sparse_control_column_list(cur1)),
    ensures
        whole == column_list_prepend(done + seq![sc], ls, sparse_control_column_list(cur1)),
{
    match sparse_control_column_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![sc] + more) == (done + seq![sc]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_column_list_last(cur: Seq<TokenView>, c: SColumn, r: Seq<TokenView>)
    requires
        sparse_control_column(cur) == (Some(c), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_column_list(cur) == (Some(seq![c]), r),
{
}

pub open spec fn sparse_control_create(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Table) {
        (None, input)
    } else {
        let r0 = input.drop_first();
        if r0.len() < 1 {
            (None, input)
        } else {
            match r0[0] {
                TokenView::Ident(name) => {
                    let r1 = r0.drop_first();
                    if r1.len() < 1 || r1[0] != TokenView::OpenParen {
                        (None, input)
                    } else {
                        let r2 = r1.drop_first();
                        match sparse_control_column_list(r2) {
                            (Some(cols), r3) => {
                                if r3.len() >= 1 && r3[0] == TokenView::CloseParen {
                                    (Some(SStmt::CreateTable { name, columns: cols }), r3.drop_first())
                                } else {
                                    (None, input)
                                }
                            },
                            (None, _) => (None, input),
                        }
                    }
                },
                _ => (None, input),
            }
        }
    }
}


pub open spec fn sparse_control_select_alias(e: SExpr, r: Seq<TokenView>)
    -> Option<(Option<String>, Seq<TokenView>)> {
    let is_as = r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::As);
    let is_ident = r.len() >= 1 && (match r[0] {
        TokenView::Ident(_) => true,
        _ => false,
    });
    if is_as || is_ident {
        if e == SExpr::All {
            None
        } else if is_as {
            let r1 = r.drop_first();
            if r1.len() < 1 {
                None
            } else {
                match r1[0] {
                    TokenView::Ident(name) => Some((Some(name), r1.drop_first())),
                    _ => None,
                }
            }
        } else {
            match r[0] {
                TokenView::Ident(name) => Some((Some(name), r.drop_first())),
                _ => None,
            }
        }
    } else {
        Some((None, r))
    }
}

pub open spec fn sparse_control_select_list(input: Seq<TokenView>)
    -> (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_select_list_decreases
{
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            match sparse_control_select_alias(e, r) {
                Some((alias, r1)) => {
                    if r1.len() >= 1 && r1[0] == TokenView::Comma {
                        match sparse_control_select_list(r1.drop_first()) {
                            (Some(more), r2) => (Some(seq![(e, alias)] + more), r2),
                            (None, _) => (None, input),
                        }
                    } else {
                        (Some(seq![(e, alias)]), r1)
                    }
                },
                None => (None, input),
            }
        },
        (None, _) => (None, input),
    }
}

#[via_fn]
proof fn sparse_control_select_list_decreases(input: Seq<TokenView>) {
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
}

pub proof fn lemma_view_select_list_append(
    a: Seq<(ast::Expression, Option<String>)>,
    b: Seq<(ast::Expression, Option<String>)>,
)
    ensures
        verified_stmt::view_select_list(a + b)
            == verified_stmt::view_select_list(a) + verified_stmt::view_select_list(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_select_list, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_select_list_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_select_list_single(expr: ast::Expression, alias: Option<String>)
    ensures
        verified_stmt::view_select_list(seq![(expr, alias)])
            == seq![(verified_roundtrip::view_expr(expr), alias)],
{
    reveal_with_fuel(verified_stmt::view_select_list, 2);
    let s = seq![(expr, alias)];
    assert(s.len() == 1);
    assert(s[0] == (expr, alias));
    assert(s.drop_first() =~= Seq::<(ast::Expression, Option<String>)>::empty());
    assert(verified_stmt::view_select_list(s.drop_first())
        =~= Seq::<(SExpr, Option<String>)>::empty());
    assert(verified_stmt::view_select_list(s)
        =~= seq![(verified_roundtrip::view_expr(expr), alias)]);
}

pub open spec fn select_list_prepend(
    done: Seq<(SExpr, Option<String>)>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>),
) -> (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_select_list_step(
    cur: Seq<TokenView>,
    e: SExpr,
    alias: Option<String>,
    r: Seq<TokenView>,
    r1: Seq<TokenView>,
)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        sparse_control_select_alias(e, r) == Some((alias, r1)),
        r1.len() >= 1,
        r1[0] == TokenView::Comma,
    ensures
        sparse_control_select_list(cur)
            == select_list_prepend(seq![(e, alias)], cur, sparse_control_select_list(r1.drop_first())),
{
    match sparse_control_select_list(r1.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_select_list(cur) == (Some(seq![(e, alias)] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_select_list(cur)
                == (None::<Seq<(SExpr, Option<String>)>>, cur));
        },
    }
}

pub proof fn lemma_select_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<(SExpr, Option<String>)>,
    se: SExpr,
    alias: Option<String>,
    whole: (Option<Seq<(SExpr, Option<String>)>>, Seq<TokenView>),
)
    requires
        whole == select_list_prepend(done, ls, sparse_control_select_list(cur)),
        sparse_control_select_list(cur)
            == select_list_prepend(seq![(se, alias)], cur, sparse_control_select_list(cur1)),
    ensures
        whole == select_list_prepend(done + seq![(se, alias)], ls, sparse_control_select_list(cur1)),
{
    match sparse_control_select_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![(se, alias)] + more) == (done + seq![(se, alias)]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_select_list_last(
    cur: Seq<TokenView>,
    e: SExpr,
    alias: Option<String>,
    r: Seq<TokenView>,
    r1: Seq<TokenView>,
)
    requires
        sparse_prec(cur, 0, expr_fuel(cur)) == (Some(e), r),
        sparse_control_select_alias(e, r) == Some((alias, r1)),
        !(r1.len() >= 1 && r1[0] == TokenView::Comma),
    ensures
        sparse_control_select_list(cur) == (Some(seq![(e, alias)]), r1),
{
}


pub open spec fn sparse_control_ident_list(input: Seq<TokenView>)
    -> (Option<Seq<String>>, Seq<TokenView>)
    decreases input.len(),
{
    if input.len() < 1 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                let r = input.drop_first();
                if r.len() >= 1 && r[0] == TokenView::Comma {
                    match sparse_control_ident_list(r.drop_first()) {
                        (Some(more), r2) => (Some(seq![name] + more), r2),
                        (None, _) => (None, input),
                    }
                } else {
                    (Some(seq![name]), r)
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn ident_list_prepend(
    done: Seq<String>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<String>>, Seq<TokenView>),
) -> (Option<Seq<String>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_ident_list_step(cur: Seq<TokenView>, name: String, r: Seq<TokenView>)
    requires
        cur.len() >= 1,
        cur[0] == TokenView::Ident(name),
        r == cur.drop_first(),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_ident_list(cur)
            == ident_list_prepend(seq![name], cur, sparse_control_ident_list(r.drop_first())),
{
    match sparse_control_ident_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_ident_list(cur) == (Some(seq![name] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_ident_list(cur) == (None::<Seq<String>>, cur));
        },
    }
}

pub proof fn lemma_ident_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<String>,
    name: String,
    whole: (Option<Seq<String>>, Seq<TokenView>),
)
    requires
        whole == ident_list_prepend(done, ls, sparse_control_ident_list(cur)),
        sparse_control_ident_list(cur)
            == ident_list_prepend(seq![name], cur, sparse_control_ident_list(cur1)),
    ensures
        whole == ident_list_prepend(done + seq![name], ls, sparse_control_ident_list(cur1)),
{
    match sparse_control_ident_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![name] + more) == (done + seq![name]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_ident_list_last(cur: Seq<TokenView>, name: String, r: Seq<TokenView>)
    requires
        cur.len() >= 1,
        cur[0] == TokenView::Ident(name),
        r == cur.drop_first(),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_ident_list(cur) == (Some(seq![name]), r),
{
}

pub open spec fn sparse_control_row(input: Seq<TokenView>)
    -> (Option<Seq<SExpr>>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::OpenParen {
        (None, input)
    } else {
        match sparse_control_group_list(input.drop_first()) {
            (Some(exprs), r) => {
                if r.len() >= 1 && r[0] == TokenView::CloseParen {
                    (Some(exprs), r.drop_first())
                } else {
                    (None, input)
                }
            },
            (None, _) => (None, input),
        }
    }
}

pub open spec fn sparse_control_values(input: Seq<TokenView>)
    -> (Option<Seq<Seq<SExpr>>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_values_decreases
{
    match sparse_control_row(input) {
        (Some(row), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_values(r.drop_first()) {
                    (Some(more), r2) => (Some(seq![row] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![row]), r)
            }
        },
        (None, _) => (None, input),
    }
}

#[via_fn]
proof fn sparse_control_values_decreases(input: Seq<TokenView>) {
    if input.len() >= 1 && input[0] == TokenView::OpenParen {
        let after_open = input.drop_first();
        match sparse_control_group_list(after_open) {
            (Some(exprs), r) => {
                lemma_group_list_slen(after_open);
            },
            (None, _) => {},
        }
    }
}

pub proof fn lemma_group_list_slen(input: Seq<TokenView>)
    ensures
        sparse_control_group_list(input).1.len() <= input.len(),
    decreases input.len(),
{
    verified_precedence::lemma_prec_slen(input, 0, expr_fuel(input));
    match sparse_prec(input, 0, expr_fuel(input)) {
        (Some(e), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_group_list(r.drop_first()) {
                    (Some(more), r2) => {
                        lemma_group_list_slen(r.drop_first());
                    },
                    (None, _) => {},
                }
            }
        },
        (None, _) => {},
    }
}

pub open spec fn values_prepend(
    done: Seq<Seq<SExpr>>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<Seq<SExpr>>>, Seq<TokenView>),
) -> (Option<Seq<Seq<SExpr>>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_values_step(cur: Seq<TokenView>, row: Seq<SExpr>, r: Seq<TokenView>)
    requires
        sparse_control_row(cur) == (Some(row), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_values(cur)
            == values_prepend(seq![row], cur, sparse_control_values(r.drop_first())),
{
    match sparse_control_values(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_values(cur) == (Some(seq![row] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_values(cur) == (None::<Seq<Seq<SExpr>>>, cur));
        },
    }
}

pub proof fn lemma_values_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<Seq<SExpr>>,
    row: Seq<SExpr>,
    whole: (Option<Seq<Seq<SExpr>>>, Seq<TokenView>),
)
    requires
        whole == values_prepend(done, ls, sparse_control_values(cur)),
        sparse_control_values(cur)
            == values_prepend(seq![row], cur, sparse_control_values(cur1)),
    ensures
        whole == values_prepend(done + seq![row], ls, sparse_control_values(cur1)),
{
    match sparse_control_values(cur1).0 {
        Some(more) => {
            assert(done + (seq![row] + more) == (done + seq![row]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_values_last(cur: Seq<TokenView>, row: Seq<SExpr>, r: Seq<TokenView>)
    requires
        sparse_control_row(cur) == (Some(row), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_values(cur) == (Some(seq![row]), r),
{
}

pub proof fn lemma_view_rows_append(
    a: Seq<Vec<ast::Expression>>,
    b: Seq<Vec<ast::Expression>>,
)
    ensures
        verified_stmt::view_rows(a + b)
            == verified_stmt::view_rows(a) + verified_stmt::view_rows(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_rows, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_rows_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_rows_single(row: Vec<ast::Expression>)
    ensures
        verified_stmt::view_rows(seq![row]) == seq![verified_roundtrip::view_args(row@)],
{
    reveal_with_fuel(verified_stmt::view_rows, 2);
    let s = seq![row];
    assert(s.len() == 1);
    assert(s[0] == row);
    assert(s.drop_first() =~= Seq::<Vec<ast::Expression>>::empty());
    assert(verified_stmt::view_rows(s.drop_first()) =~= Seq::<Seq<SExpr>>::empty());
    assert(verified_stmt::view_rows(s) =~= seq![verified_roundtrip::view_args(row@)]);
}

pub open spec fn sparse_control_opt_columns(r1: Seq<TokenView>)
    -> Option<(Option<Seq<String>>, Seq<TokenView>)> {
    if r1.len() >= 1 && r1[0] == TokenView::OpenParen {
        match sparse_control_ident_list(r1.drop_first()) {
            (Some(names), rc) => {
                if rc.len() >= 1 && rc[0] == TokenView::CloseParen {
                    Some((Some(names), rc.drop_first()))
                } else {
                    None
                }
            },
            (None, _) => None,
        }
    } else {
        Some((None, r1))
    }
}

pub open spec fn sparse_control_insert(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::Into) {
        (None, input)
    } else {
        let r0 = input.drop_first();
        if r0.len() < 1 {
            (None, input)
        } else {
            match r0[0] {
                TokenView::Ident(table) => {
                    let r1 = r0.drop_first();
                    match sparse_control_opt_columns(r1) {
                        Some((cols, r2)) => {
                            if r2.len() < 1 || r2[0] != TokenView::Keyword(Keyword::Values) {
                                (None, input)
                            } else {
                                match sparse_control_values(r2.drop_first()) {
                                    (Some(rows), r3) =>
                                        (Some(SStmt::Insert { table, columns: cols, values: rows }), r3),
                                    (None, _) => (None, input),
                                }
                            }
                        },
                        None => (None, input),
                    }
                },
                _ => (None, input),
            }
        }
    }
}


pub open spec fn sparse_control_from_table(input: Seq<TokenView>)
    -> (Option<SFrom>, Seq<TokenView>) {
    if input.len() < 1 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                let r = input.drop_first();
                let is_as = r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::As);
                let is_ident = r.len() >= 1 && (match r[0] {
                    TokenView::Ident(_) => true,
                    _ => false,
                });
                if is_as {
                    let r1 = r.drop_first();
                    if r1.len() < 1 {
                        (None, input)
                    } else {
                        match r1[0] {
                            TokenView::Ident(a) =>
                                (Some(SFrom::Table { name, alias: Some(a) }), r1.drop_first()),
                            _ => (None, input),
                        }
                    }
                } else if is_ident {
                    match r[0] {
                        TokenView::Ident(a) =>
                            (Some(SFrom::Table { name, alias: Some(a) }), r.drop_first()),
                        _ => (None, input),
                    }
                } else {
                    (Some(SFrom::Table { name, alias: None }), r)
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn is_join_start(input: Seq<TokenView>) -> bool {
    input.len() >= 1 && (
        input[0] == TokenView::Keyword(Keyword::Join)
        || input[0] == TokenView::Keyword(Keyword::Cross)
        || input[0] == TokenView::Keyword(Keyword::Inner)
        || input[0] == TokenView::Keyword(Keyword::Left)
        || input[0] == TokenView::Keyword(Keyword::Right)
    )
}

pub open spec fn sparse_control_join_head(input: Seq<TokenView>)
    -> Option<(ast::JoinType, bool, Seq<TokenView>)> {
    if input.len() < 1 {
        None
    } else {
        match input[0] {
            TokenView::Keyword(Keyword::Join) =>
                Some((ast::JoinType::Inner, true, input.drop_first())),
            TokenView::Keyword(Keyword::Cross) => {
                let r = input.drop_first();
                if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Join) {
                    Some((ast::JoinType::Cross, false, r.drop_first()))
                } else {
                    None
                }
            },
            TokenView::Keyword(Keyword::Inner) => {
                let r = input.drop_first();
                if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Join) {
                    Some((ast::JoinType::Inner, true, r.drop_first()))
                } else {
                    None
                }
            },
            TokenView::Keyword(Keyword::Left) => {
                let r = input.drop_first();
                let r2 = if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Outer) {
                    r.drop_first()
                } else {
                    r
                };
                if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::Join) {
                    Some((ast::JoinType::Left, true, r2.drop_first()))
                } else {
                    None
                }
            },
            TokenView::Keyword(Keyword::Right) => {
                let r = input.drop_first();
                let r2 = if r.len() >= 1 && r[0] == TokenView::Keyword(Keyword::Outer) {
                    r.drop_first()
                } else {
                    r
                };
                if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::Join) {
                    Some((ast::JoinType::Right, true, r2.drop_first()))
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

pub open spec fn sparse_control_from_step(input: Seq<TokenView>)
    -> Option<(verified_stmt::SJoinStep, Seq<TokenView>)> {
    match sparse_control_join_head(input) {
        None => None,
        Some((join_type, needs_on, r)) => {
            match sparse_control_from_table(r) {
                (None, _) => None,
                (Some(right), r1) => {
                    if needs_on {
                        if r1.len() < 1 || r1[0] != TokenView::Keyword(Keyword::On) {
                            None
                        } else {
                            match sparse_prec(r1.drop_first(), 0, expr_fuel(r1.drop_first())) {
                                (Some(e), r2) => Some((verified_stmt::SJoinStep {
                                    join_type, right, predicate: Some(e) }, r2)),
                                (None, _) => None,
                            }
                        }
                    } else {
                        Some((verified_stmt::SJoinStep {
                            join_type, right, predicate: None }, r1))
                    }
                },
            }
        },
    }
}

pub open spec fn sparse_control_from_joins(acc: SFrom, input: Seq<TokenView>)
    -> (Option<SFrom>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_from_joins_decreases
{
    match sparse_control_from_step(input) {
        None => {
            if is_join_start(input) {
                (None, input)
            } else {
                (Some(acc), input)
            }
        },
        Some((step, r)) => {
            sparse_control_from_joins(verified_stmt::apply_step(acc, step), r)
        },
    }
}

#[via_fn]
proof fn sparse_control_from_joins_decreases(acc: SFrom, input: Seq<TokenView>) {
    match sparse_control_from_step(input) {
        Some((step, r)) => {
            lemma_from_step_slen(input);
        },
        None => {},
    }
}

pub proof fn lemma_from_table_slen(input: Seq<TokenView>)
    ensures
        sparse_control_from_table(input).0 is Some ==>
            sparse_control_from_table(input).1.len() < input.len(),
{
}

pub proof fn lemma_from_step_slen(input: Seq<TokenView>)
    ensures
        sparse_control_from_step(input) is Some ==>
            sparse_control_from_step(input)->Some_0.1.len() < input.len(),
{
    match sparse_control_join_head(input) {
        Some((join_type, needs_on, r)) => {
            assert(r.len() < input.len());
            lemma_from_table_slen(r);
            match sparse_control_from_table(r) {
                (Some(right), r1) => {
                    if needs_on && r1.len() >= 1 && r1[0] == TokenView::Keyword(Keyword::On) {
                        verified_precedence::lemma_prec_slen(
                            r1.drop_first(), 0, expr_fuel(r1.drop_first()));
                    }
                },
                (None, _) => {},
            }
        },
        None => {},
    }
}

pub proof fn lemma_from_joins_step(acc: SFrom, cur: Seq<TokenView>, step: verified_stmt::SJoinStep, r: Seq<TokenView>)
    requires
        sparse_control_from_step(cur) == Some((step, r)),
    ensures
        sparse_control_from_joins(acc, cur)
            == sparse_control_from_joins(verified_stmt::apply_step(acc, step), r),
{
}

pub proof fn lemma_from_joins_stop(acc: SFrom, cur: Seq<TokenView>)
    requires
        !is_join_start(cur),
    ensures
        sparse_control_from_joins(acc, cur) == (Some(acc), cur),
{
    assert(sparse_control_join_head(cur) is None);
    assert(sparse_control_from_step(cur) is None);
}

pub proof fn lemma_from_joins_reject(acc: SFrom, cur: Seq<TokenView>)
    requires
        is_join_start(cur),
        sparse_control_from_step(cur) is None,
    ensures
        sparse_control_from_joins(acc, cur) == (None::<SFrom>, cur),
{
}

pub open spec fn sparse_control_from_item(input: Seq<TokenView>)
    -> (Option<SFrom>, Seq<TokenView>) {
    match sparse_control_from_table(input) {
        (None, _) => (None, input),
        (Some(base), r) => sparse_control_from_joins(base, r),
    }
}

pub open spec fn sparse_control_from_list(input: Seq<TokenView>)
    -> (Option<Seq<SFrom>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_from_list_decreases
{
    match sparse_control_from_item(input) {
        (None, _) => (None, input),
        (Some(item), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_from_list(r.drop_first()) {
                    (Some(more), r2) => (Some(seq![item] + more), r2),
                    (None, _) => (None, input),
                }
            } else {
                (Some(seq![item]), r)
            }
        },
    }
}

#[via_fn]
proof fn sparse_control_from_list_decreases(input: Seq<TokenView>) {
    lemma_from_item_slen(input);
}

pub proof fn lemma_from_item_slen(input: Seq<TokenView>)
    ensures
        sparse_control_from_item(input).0 is Some ==>
            sparse_control_from_item(input).1.len() < input.len(),
{
    lemma_from_table_slen(input);
    match sparse_control_from_table(input) {
        (Some(base), r) => {
            lemma_from_joins_slen(base, r);
        },
        (None, _) => {},
    }
}

pub proof fn lemma_from_joins_slen(acc: SFrom, input: Seq<TokenView>)
    ensures
        sparse_control_from_joins(acc, input).1.len() <= input.len(),
    decreases input.len(),
{
    match sparse_control_from_step(input) {
        Some((step, r)) => {
            lemma_from_step_slen(input);
            lemma_from_joins_slen(verified_stmt::apply_step(acc, step), r);
        },
        None => {},
    }
}

pub open spec fn sparse_control_from(input: Seq<TokenView>)
    -> (Option<Seq<SFrom>>, Seq<TokenView>) {
    if input.len() < 1 || input[0] != TokenView::Keyword(Keyword::From) {
        (Some(Seq::<SFrom>::empty()), input)
    } else {
        sparse_control_from_list(input.drop_first())
    }
}


pub proof fn lemma_view_froms_append(a: Seq<ast::From>, b: Seq<ast::From>)
    ensures
        verified_stmt::view_froms(a + b)
            == verified_stmt::view_froms(a) + verified_stmt::view_froms(b),
    decreases a.len(),
{
    reveal_with_fuel(verified_stmt::view_froms, 1);
    if a.len() == 0 {
        assert(a + b == b);
    } else {
        assert((a + b).drop_first() == a.drop_first() + b);
        lemma_view_froms_append(a.drop_first(), b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_view_froms_single(f: ast::From)
    ensures
        verified_stmt::view_froms(seq![f]) == seq![verified_stmt::view_from(f)],
{
    reveal_with_fuel(verified_stmt::view_froms, 2);
    let s = seq![f];
    assert(s.len() == 1);
    assert(s[0] == f);
    assert(s.drop_first() =~= Seq::<ast::From>::empty());
    assert(verified_stmt::view_froms(s.drop_first()) =~= Seq::<SFrom>::empty());
    assert(verified_stmt::view_froms(s) =~= seq![verified_stmt::view_from(f)]);
}

pub open spec fn from_list_prepend(
    done: Seq<SFrom>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<SFrom>>, Seq<TokenView>),
) -> (Option<Seq<SFrom>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_from_list_step(cur: Seq<TokenView>, item: SFrom, r: Seq<TokenView>)
    requires
        sparse_control_from_item(cur) == (Some(item), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_from_list(cur)
            == from_list_prepend(seq![item], cur, sparse_control_from_list(r.drop_first())),
{
    match sparse_control_from_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_from_list(cur) == (Some(seq![item] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_from_list(cur) == (None::<Seq<SFrom>>, cur));
        },
    }
}

pub proof fn lemma_from_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<SFrom>,
    item: SFrom,
    whole: (Option<Seq<SFrom>>, Seq<TokenView>),
)
    requires
        whole == from_list_prepend(done, ls, sparse_control_from_list(cur)),
        sparse_control_from_list(cur)
            == from_list_prepend(seq![item], cur, sparse_control_from_list(cur1)),
    ensures
        whole == from_list_prepend(done + seq![item], ls, sparse_control_from_list(cur1)),
{
    match sparse_control_from_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![item] + more) == (done + seq![item]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_from_list_last(cur: Seq<TokenView>, item: SFrom, r: Seq<TokenView>)
    requires
        sparse_control_from_item(cur) == (Some(item), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_from_list(cur) == (Some(seq![item]), r),
{
}


pub open spec fn sparse_control_assign(input: Seq<TokenView>)
    -> (Option<(String, Option<SExpr>)>, Seq<TokenView>) {
    if input.len() < 2 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                if input[1] != TokenView::Equal {
                    (None, input)
                } else {
                    let rest = input.drop_first().drop_first();
                    if rest.len() >= 1 && rest[0] == TokenView::Keyword(Keyword::Default) {
                        (Some((name, None)), rest.drop_first())
                    } else {
                        match sparse_prec(rest, 0, expr_fuel(rest)) {
                            (Some(e), r) => (Some((name, Some(e))), r),
                            (None, _) => (None, input),
                        }
                    }
                }
            },
            _ => (None, input),
        }
    }
}

pub proof fn lemma_control_assign_slen(input: Seq<TokenView>)
    ensures
        sparse_control_assign(input).1.len() <= input.len(),
{
    if input.len() >= 2 {
        match input[0] {
            TokenView::Ident(name) => {
                if input[1] == TokenView::Equal {
                    let rest = input.drop_first().drop_first();
                    if rest.len() >= 1 && rest[0] == TokenView::Keyword(Keyword::Default) {
                    } else {
                        verified_precedence::lemma_prec_slen(rest, 0, expr_fuel(rest));
                    }
                }
            },
            _ => {},
        }
    }
}

pub open spec fn sparse_control_assign_list(input: Seq<TokenView>)
    -> (Option<Seq<(String, Option<SExpr>)>>, Seq<TokenView>)
    decreases input.len(),
    when true
    via sparse_control_assign_list_decreases
{
    match sparse_control_assign(input) {
        (Some(a), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_assign_list(r.drop_first()) {
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

#[via_fn]
proof fn sparse_control_assign_list_decreases(input: Seq<TokenView>) {
    lemma_control_assign_slen(input);
}

pub proof fn lemma_control_assign_list_slen(input: Seq<TokenView>)
    ensures
        sparse_control_assign_list(input).1.len() <= input.len(),
    decreases input.len(),
{
    lemma_control_assign_slen(input);
    match sparse_control_assign(input) {
        (Some(a), r) => {
            if r.len() >= 1 && r[0] == TokenView::Comma {
                match sparse_control_assign_list(r.drop_first()) {
                    (Some(more), r2) => {
                        lemma_control_assign_list_slen(r.drop_first());
                    },
                    (None, _) => {},
                }
            }
        },
        (None, _) => {},
    }
}

pub open spec fn assign_list_prepend(
    done: Seq<(String, Option<SExpr>)>,
    whole: Seq<TokenView>,
    tail: (Option<Seq<(String, Option<SExpr>)>>, Seq<TokenView>),
) -> (Option<Seq<(String, Option<SExpr>)>>, Seq<TokenView>) {
    match tail.0 {
        Some(m) => (Some(done + m), tail.1),
        None => (None, whole),
    }
}

pub proof fn lemma_assign_list_step(cur: Seq<TokenView>, a: (String, Option<SExpr>), r: Seq<TokenView>)
    requires
        sparse_control_assign(cur) == (Some(a), r),
        r.len() >= 1,
        r[0] == TokenView::Comma,
    ensures
        sparse_control_assign_list(cur)
            == assign_list_prepend(seq![a], cur, sparse_control_assign_list(r.drop_first())),
{
    match sparse_control_assign_list(r.drop_first()) {
        (Some(more), r2) => {
            assert(sparse_control_assign_list(cur) == (Some(seq![a] + more), r2));
        },
        (None, _) => {
            assert(sparse_control_assign_list(cur)
                == (None::<Seq<(String, Option<SExpr>)>>, cur));
        },
    }
}

pub proof fn lemma_assign_list_resume_step(
    ls: Seq<TokenView>,
    cur: Seq<TokenView>,
    cur1: Seq<TokenView>,
    done: Seq<(String, Option<SExpr>)>,
    a: (String, Option<SExpr>),
    whole: (Option<Seq<(String, Option<SExpr>)>>, Seq<TokenView>),
)
    requires
        whole == assign_list_prepend(done, ls, sparse_control_assign_list(cur)),
        sparse_control_assign_list(cur)
            == assign_list_prepend(seq![a], cur, sparse_control_assign_list(cur1)),
    ensures
        whole == assign_list_prepend(done + seq![a], ls, sparse_control_assign_list(cur1)),
{
    match sparse_control_assign_list(cur1).0 {
        Some(more) => {
            assert(done + (seq![a] + more) == (done + seq![a]) + more);
        },
        None => {},
    }
}

pub proof fn lemma_assign_list_last(cur: Seq<TokenView>, a: (String, Option<SExpr>), r: Seq<TokenView>)
    requires
        sparse_control_assign(cur) == (Some(a), r),
        !(r.len() >= 1 && r[0] == TokenView::Comma),
    ensures
        sparse_control_assign_list(cur) == (Some(seq![a]), r),
{
}

pub open spec fn assign_keys(items: Seq<(String, Option<SExpr>)>) -> Seq<String> {
    items.map_values(|kv: (String, Option<SExpr>)| kv.0)
}

pub open spec fn assign_keys_distinct(items: Seq<(String, Option<SExpr>)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0
}

pub open spec fn assign_list_to_sstmt(
    table: String,
    items: Seq<(String, Option<SExpr>)>,
    where_clause: Option<SExpr>,
) -> SStmt {
    if items.len() == 1 {
        SStmt::Update { table, set: seq![(items[0].0, items[0].1)], where_clause }
    } else {
        SStmt::Unsupported
    }
}

pub proof fn lemma_assign_list_head(cur: Seq<TokenView>, a: (String, Option<SExpr>), r: Seq<TokenView>)
    requires
        sparse_control_assign(cur) == (Some(a), r),
    ensures
        sparse_control_assign_list(cur).0 is Some ==> {
            let lst = sparse_control_assign_list(cur).0.unwrap();
            lst.len() >= 1 && lst[0] == a
        },
{
    if r.len() >= 1 && r[0] == TokenView::Comma {
        match sparse_control_assign_list(r.drop_first()) {
            (Some(more), r2) => {
                assert(sparse_control_assign_list(cur).0.unwrap() == seq![a] + more);
                assert((seq![a] + more)[0] == a);
            },
            (None, _) => {},
        }
    } else {
        assert(sparse_control_assign_list(cur) == (Some(seq![a]), r));
    }
}

pub proof fn lemma_update_reject_on_duplicate(
    input: Seq<TokenView>,
    table: String,
    cur: Seq<TokenView>,
    a: (String, Option<SExpr>),
    r_after: Seq<TokenView>,
    done: Seq<(String, Option<SExpr>)>,
    di: int,
)
    requires
        input.len() >= 1,
        input[0] == TokenView::Ident(table),
        input.drop_first().len() >= 1,
        input.drop_first()[0] == TokenView::Keyword(Keyword::Set),
        sparse_control_assign_list(input.drop_first().drop_first())
            == assign_list_prepend(done, input.drop_first().drop_first(),
                sparse_control_assign_list(cur)),
        sparse_control_assign(cur) == (Some(a), r_after),
        0 <= di < done.len(),
        done[di].0 == a.0,
    ensures
        sparse_control_update(input).0 is None,
{
    let r1 = input.drop_first().drop_first();
    let al_whole = sparse_control_assign_list(r1);
    match sparse_control_assign_list(cur).0 {
        Some(lst) => {
            lemma_assign_list_head(cur, a, r_after);
            assert(lst.len() >= 1 && lst[0] == a);
            assert(al_whole == (Some(done + lst), sparse_control_assign_list(cur).1));
            let full = done + lst;
            assert(full[di].0 == done[di].0);
            assert(full[done.len() as int] == lst[0]);
            assert(full[done.len() as int].0 == a.0);
            assert(di < done.len());
            assert(!assign_keys_distinct(full)) by {
                assert(full[di].0 == full[done.len() as int].0);
                assert(0 <= di < (done.len() as int) < full.len());
            }
        },
        None => {
            assert(al_whole.0 is None);
        },
    }
}

pub proof fn lemma_update_reject_on_list_none(input: Seq<TokenView>, table: String)
    requires
        input.len() >= 1,
        input[0] == TokenView::Ident(table),
        input.drop_first().len() >= 1,
        input.drop_first()[0] == TokenView::Keyword(Keyword::Set),
        sparse_control_assign_list(input.drop_first().drop_first()).0 is None,
    ensures
        sparse_control_update(input).0 is None,
{
}

pub proof fn lemma_update_reject_on_where_none(
    input: Seq<TokenView>,
    table: String,
    items: Seq<(String, Option<SExpr>)>,
    r2: Seq<TokenView>,
)
    requires
        input.len() >= 1,
        input[0] == TokenView::Ident(table),
        input.drop_first().len() >= 1,
        input.drop_first()[0] == TokenView::Keyword(Keyword::Set),
        sparse_control_assign_list(input.drop_first().drop_first()) == (Some(items), r2),
        assign_keys_distinct(items),
        r2.len() >= 1,
        r2[0] == TokenView::Keyword(Keyword::Where),
        sparse_prec(r2.drop_first(), 0, expr_fuel(r2.drop_first())).0 is None,
    ensures
        sparse_control_update(input).0 is None,
{
}


pub open spec fn sparse_control_kw_expr(input: Seq<TokenView>, kw: Keyword)
    -> (Option<Option<SExpr>>, Seq<TokenView>) {
    if input.len() >= 1 && input[0] == TokenView::Keyword(kw) {
        let e_in = input.drop_first();
        match sparse_prec(e_in, 0, expr_fuel(e_in)) {
            (Some(e), r) => (Some(Some(e)), r),
            (None, _) => (None, input),
        }
    } else {
        (Some(None), input)
    }
}

pub open spec fn sparse_control_select(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    match sparse_control_select_list(input) {
        (None, _) => (None, input),
        (Some(select), r1) => match sparse_control_from(r1) {
            (None, _) => (None, input),
            (Some(from), r2) => match sparse_control_kw_expr(r2, Keyword::Where) {
                (None, _) => (None, input),
                (Some(where_clause), r3) => match sparse_control_group_by(r3) {
                    (None, _) => (None, input),
                    (Some(group_by), r4) => match sparse_control_kw_expr(r4, Keyword::Having) {
                        (None, _) => (None, input),
                        (Some(having), r5) => match sparse_control_order_by(r5) {
                            (None, _) => (None, input),
                            (Some(order_by), r6) => match sparse_control_kw_expr(r6, Keyword::Limit) {
                                (None, _) => (None, input),
                                (Some(limit), r7) => match sparse_control_kw_expr(r7, Keyword::Offset) {
                                    (None, _) => (None, input),
                                    (Some(offset), r8) => (
                                        Some(SStmt::Select {
                                            select, from, where_clause, group_by, having,
                                            order_by, limit, offset,
                                        }),
                                        r8,
                                    ),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn sparse_control_update(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 1 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Ident(table) => {
                let r0 = input.drop_first();
                if r0.len() < 1 || r0[0] != TokenView::Keyword(Keyword::Set) {
                    (None, input)
                } else {
                    let r1 = r0.drop_first();
                    match sparse_control_assign_list(r1) {
                        (Some(items), r2) => {
                            if !assign_keys_distinct(items) {
                                (None, input)
                            } else if r2.len() >= 1 && r2[0] == TokenView::Keyword(Keyword::Where) {
                                match sparse_prec(r2.drop_first(), 0, expr_fuel(r2.drop_first())) {
                                    (Some(e), r3) =>
                                        (Some(assign_list_to_sstmt(table, items, Some(e))), r3),
                                    (None, _) => (None, input),
                                }
                            } else {
                                (Some(assign_list_to_sstmt(table, items, None)), r2)
                            }
                        },
                        (None, _) => (None, input),
                    }
                }
            },
            _ => (None, input),
        }
    }
}


pub open spec fn sparse_control(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>)
    decreases input.len(), 0int,
{
    if input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Keyword(Keyword::Commit) => (Some(SStmt::Commit), input.drop_first()),
            TokenView::Keyword(Keyword::Rollback) => (Some(SStmt::Rollback), input.drop_first()),
            TokenView::Keyword(Keyword::Begin) =>
                control_norm(input, sparse_control_begin(input.drop_first())),
            TokenView::Keyword(Keyword::Drop) =>
                control_norm(input, sparse_control_drop(input.drop_first())),
            TokenView::Keyword(Keyword::Delete) =>
                control_norm(input, sparse_control_delete(input.drop_first())),
            TokenView::Keyword(Keyword::Insert) =>
                control_norm(input, sparse_control_insert(input.drop_first())),
            TokenView::Keyword(Keyword::Update) =>
                control_norm(input, sparse_control_update(input.drop_first())),
            TokenView::Keyword(Keyword::Create) =>
                control_norm(input, sparse_control_create(input.drop_first())),
            TokenView::Keyword(Keyword::Select) =>
                control_norm(input, sparse_control_select(input.drop_first())),
            TokenView::Keyword(Keyword::Explain) =>
                control_norm(input, sparse_control_explain(input.drop_first())),
            _ => (None, input),
        }
    }
}

pub open spec fn control_norm(whole: Seq<TokenView>, sub: (Option<SStmt>, Seq<TokenView>))
    -> (Option<SStmt>, Seq<TokenView>) {
    match sub.0 {
        Some(s) => (Some(s), sub.1),
        None => (None, whole),
    }
}

pub open spec fn sparse_control_explain(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>)
    decreases input.len(), 1int,
{
    if input.len() >= 1 && input[0] == TokenView::Keyword(Keyword::Explain) {
        (None, input)
    } else {
        match sparse_control(input) {
            (Some(inner), r) => (Some(SStmt::Explain(Box::new(inner))), r),
            (None, _) => (None, input),
        }
    }
}

}
