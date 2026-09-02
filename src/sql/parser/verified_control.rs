
#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::parse_error::ParseError;
#[allow(unused_imports)]
use super::{Keyword, Token, ast, verified_integer, verified_precedence};
#[allow(unused_imports)]
use super::{verified_production, verified_roundtrip, verified_stmt, verified_stmt_prec};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::SExpr;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::SStmt;
use crate::sql::types::DataType;
use std::collections::BTreeMap;

verus! {

#[verifier::spinoff_prover]
#[verifier::rlimit(200000)]
pub fn parse_control_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
    decreases toks.len() - pos, 0int,
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        reveal(verified_production::token_view);
        assert(input.drop_first() == verified_production::token_views(
            toks@.subrange((pos + 1) as int, toks@.len() as int)));
    }
    match &toks[pos] {
        Token::Keyword(Keyword::Commit) => (Some(ast::Statement::Commit), pos + 1, None),
        Token::Keyword(Keyword::Rollback) => (Some(ast::Statement::Rollback), pos + 1, None),
        Token::Keyword(Keyword::Begin) => parse_begin_at(toks, pos + 1),
        Token::Keyword(Keyword::Drop) => parse_drop_at(toks, pos + 1),
        Token::Keyword(Keyword::Delete) => parse_delete_at(toks, pos + 1),
        Token::Keyword(Keyword::Insert) => parse_insert_at(toks, pos + 1),
        Token::Keyword(Keyword::Update) => parse_update_at(toks, pos + 1),
        Token::Keyword(Keyword::Create) => parse_create_at(toks, pos + 1),
        Token::Keyword(Keyword::Select) => parse_select_at(toks, pos + 1),
        Token::Keyword(Keyword::Explain) => parse_explain_at(toks, pos + 1),
        _ => (None, pos, Some(ParseError::UnexpectedToken(toks[pos].clone()))),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_explain_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_explain(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
    decreases toks.len() - pos, 1int,
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof {
        verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        if pos < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, pos as int);
            reveal(verified_production::token_view);
        }
    }
    if pos < toks.len() && matches!(toks[pos], Token::Keyword(Keyword::Explain)) {
        proof {
            if sized {
                assert(input.len() >= 1 && input[0] == verified_production::TokenView::Keyword(
                    Keyword::Explain));
                assert(verified_stmt_prec::sparse_control_explain(input).0 is None);
            }
        }
        return (None, pos, Some(ParseError::NestedExplain));
    }
    let (opt, newpos, e) = parse_control_at(toks, pos);
    match opt {
        Some(inner) => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control(input)
                        == (Some(verified_stmt::view_stmt(inner)),
                            verified_production::token_views(
                                toks@.subrange(newpos as int, toks@.len() as int))));
                    assert(verified_stmt::view_stmt(ast::Statement::Explain(Box::new(inner)))
                        == SStmt::Explain(Box::new(verified_stmt::view_stmt(inner))));
                }
            }
            (Some(ast::Statement::Explain(Box::new(inner))), newpos, None)
        },
        None => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control(input).0 is None);
                    assert(verified_stmt_prec::sparse_control_explain(input).0 is None);
                }
            }
            (None, pos, e)
        },
    }
}

fn parse_clause_expr_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Expression>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_precedence::sparse_prec(input, 0, verified_stmt_prec::expr_fuel(input));
            match r.0 {
                Some(e) => sopt is Some
                    && verified_roundtrip::view_expr(e) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let n = toks.len() - pos;
    if n > (usize::MAX - 3) / 2 {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let fuel = 2 * n + 3;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    verified_precedence::parse_expression_at(toks, pos, 0, fuel)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(600000)]
fn parse_select_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_select(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    let (sopt, c1, serr) = parse_select_list_at(toks, pos);
    let select = match sopt {
        Some(s) => s,
        None => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_select_list(input).0 is None);
                    assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                }
            }
            return (None, pos, serr);
        },
    };
    let mut cur = c1;
    let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_select_list(input)
                == (Some(verified_stmt::view_select_list(select@)), r1));
        }
    }

    let (fopt, c2, ferr) = parse_from_clause_at(toks, cur);
    let from = match fopt {
        Some(f) => f,
        None => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_from(r1).0 is None);
                    assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                }
            }
            return (None, pos, ferr);
        },
    };
    cur = c2;
    let ghost r2 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_from(r1)
                == (Some(verified_stmt::view_froms(from@)), r2));
        }
    }

    let mut where_clause: Option<ast::Expression> = None;
    proof {
        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        cur = cur + 1;
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r2.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        let (opt, c, werr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r2, Keyword::Where)
                            == (Some(Some(verified_roundtrip::view_expr(e))),
                                verified_production::token_views(
                                    toks@.subrange(c as int, toks@.len() as int))));
                    }
                }
                where_clause = Some(e);
                cur = c;
            },
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r2, Keyword::Where).0 is None);
                        assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                    }
                }
                return (None, pos, werr);
            },
        }
    } else {
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_kw_expr(r2, Keyword::Where)
                    == (Some(None::<SExpr>), r2));
            }
        }
    }
    let ghost r3 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_kw_expr(r2, Keyword::Where)
                == (Some(verified_stmt::view_opt(where_clause)), r3));
        }
    }

    let (gopt, cg, gerr) = parse_group_by_at(toks, cur);
    let group_by = match gopt {
        Some(g) => g,
        None => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_group_by(r3).0 is None);
                    assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                }
            }
            return (None, pos, gerr);
        },
    };
    cur = cg;
    let ghost r4 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_group_by(r3)
                == (Some(verified_roundtrip::view_args(group_by@)), r4));
        }
    }

    let mut having: Option<ast::Expression> = None;
    proof {
        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Having)) {
        cur = cur + 1;
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r4.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        let (opt, c, herr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r4, Keyword::Having)
                            == (Some(Some(verified_roundtrip::view_expr(e))),
                                verified_production::token_views(
                                    toks@.subrange(c as int, toks@.len() as int))));
                    }
                }
                having = Some(e);
                cur = c;
            },
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r4, Keyword::Having).0 is None);
                        assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                    }
                }
                return (None, pos, herr);
            },
        }
    } else {
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_kw_expr(r4, Keyword::Having)
                    == (Some(None::<SExpr>), r4));
            }
        }
    }
    let ghost r5 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_kw_expr(r4, Keyword::Having)
                == (Some(verified_stmt::view_opt(having)), r5));
        }
    }

    let (oopt, co, oerr) = parse_order_by_at(toks, cur);
    let order_by = match oopt {
        Some(o) => o,
        None => {
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_order_by(r5).0 is None);
                    assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                }
            }
            return (None, pos, oerr);
        },
    };
    cur = co;
    let ghost r6 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_order_by(r5)
                == (Some(verified_stmt::view_order_list(order_by@)), r6));
        }
    }

    let mut limit: Option<ast::Expression> = None;
    proof {
        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Limit)) {
        cur = cur + 1;
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r6.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        let (opt, c, lerr) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r6, Keyword::Limit)
                            == (Some(Some(verified_roundtrip::view_expr(e))),
                                verified_production::token_views(
                                    toks@.subrange(c as int, toks@.len() as int))));
                    }
                }
                limit = Some(e);
                cur = c;
            },
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r6, Keyword::Limit).0 is None);
                        assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                    }
                }
                return (None, pos, lerr);
            },
        }
    } else {
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_kw_expr(r6, Keyword::Limit)
                    == (Some(None::<SExpr>), r6));
            }
        }
    }
    let ghost r7 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_kw_expr(r6, Keyword::Limit)
                == (Some(verified_stmt::view_opt(limit)), r7));
        }
    }

    let mut offset: Option<ast::Expression> = None;
    proof {
        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Offset)) {
        cur = cur + 1;
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r7.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        let (opt, c, ferr2) = parse_clause_expr_at(toks, cur);
        match opt {
            Some(e) => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r7, Keyword::Offset)
                            == (Some(Some(verified_roundtrip::view_expr(e))),
                                verified_production::token_views(
                                    toks@.subrange(c as int, toks@.len() as int))));
                    }
                }
                offset = Some(e);
                cur = c;
            },
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_kw_expr(r7, Keyword::Offset).0 is None);
                        assert(verified_stmt_prec::sparse_control_select(input).0 is None);
                    }
                }
                return (None, pos, ferr2);
            },
        }
    } else {
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_kw_expr(r7, Keyword::Offset)
                    == (Some(None::<SExpr>), r7));
            }
        }
    }
    let ghost r8 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_kw_expr(r7, Keyword::Offset)
                == (Some(verified_stmt::view_opt(offset)), r8));
        }
    }

    let statement = ast::Statement::Select {
        select,
        from,
        where_clause,
        group_by,
        having,
        order_by,
        offset,
        limit,
    };
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_select(input)
                == (Some(SStmt::Select {
                    select: verified_stmt::view_select_list(select@),
                    from: verified_stmt::view_froms(from@),
                    where_clause: verified_stmt::view_opt(where_clause),
                    group_by: verified_roundtrip::view_args(group_by@),
                    having: verified_stmt::view_opt(having),
                    order_by: verified_stmt::view_order_list(order_by@),
                    limit: verified_stmt::view_opt(limit),
                    offset: verified_stmt::view_opt(offset),
                }), r8));
            assert(verified_stmt::view_stmt(statement) == SStmt::Select {
                select: verified_stmt::view_select_list(select@),
                from: verified_stmt::view_froms(from@),
                where_clause: verified_stmt::view_opt(where_clause),
                group_by: verified_roundtrip::view_args(group_by@),
                having: verified_stmt::view_opt(having),
                order_by: verified_stmt::view_order_list(order_by@),
                limit: verified_stmt::view_opt(limit),
                offset: verified_stmt::view_opt(offset),
            });
        }
    }
    (Some(statement), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80000)]
fn parse_select_list_at(toks: &Vec<Token>, pos: usize) -> (r: (
    Option<Vec<(ast::Expression, Option<String>)>>,
    usize,
    Option<ParseError>,
))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_select_list(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_stmt::view_select_list(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost list_start = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_select_list(list_start);
    let mut select: Vec<(ast::Expression, Option<String>)> = Vec::new();
    let mut cur = pos;
    loop
        invariant_except_break
            pos <= cur,
            cur <= toks.len(),
            list_start == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_select_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == verified_stmt_prec::select_list_prepend(
                    verified_stmt::view_select_list(select@),
                    list_start,
                    verified_stmt_prec::sparse_control_select_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos <= cur,
            cur <= toks.len(),
            list_start == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_select_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == (Some(verified_stmt::view_select_list(select@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_select_list(select@);
        let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => {
                proof {
                    if sized {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_select_list, 1);
                        assert(verified_stmt_prec::sparse_control_select_list(cur_v).0 is None);
                        assert(whole.0 is None);
                    }
                }
                return (None, pos, eerr);
            },
        };
        let ghost r_after_expr = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_precedence::sparse_prec(cur_v, 0, verified_stmt_prec::expr_fuel(cur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            if sized && c < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, c as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int));
            }
        }
        cur = c;

        let is_as = cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As));
        let is_ident = cur < toks.len() && matches!(toks[cur], Token::Ident(_));
        let mut alias: Option<String> = None;
        if is_as || is_ident {
            if matches!(expr, ast::Expression::All) {
                return (None, pos, Some(ParseError::CantAliasStar));
            }
            if is_as {
                cur = cur + 1;
                if cur >= toks.len() {
                    proof {
                        verified_roundtrip::token_views_len(
                            toks@.subrange(cur as int, toks@.len() as int));
                    }
                    return (None, pos, Some(ParseError::UnexpectedEof));
                }
                proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
            }
            match &toks[cur] {
                Token::Ident(name) => {
                    alias = Some(name.clone());
                    cur = cur + 1;
                },
                _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
            }
        }
        let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        proof {
            if sized {
                reveal(verified_production::token_view);
                assert(verified_stmt_prec::sparse_control_select_alias(
                    verified_roundtrip::view_expr(expr), r_after_expr)
                    == Some((alias, r1)));
            }
        }
        let ghost old_select = select@;
        select.push((expr, alias));
        proof {
            verified_stmt_prec::lemma_view_select_list_append(old_select, seq![(expr, alias)]);
            verified_stmt_prec::lemma_view_select_list_single(expr, alias);
            assert(select@ == old_select + seq![(expr, alias)]);
            assert(verified_stmt::view_select_list(select@)
                == done_v + seq![(verified_roundtrip::view_expr(expr), alias)]);
        }

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    verified_stmt_prec::lemma_select_list_step(
                        cur_v, verified_roundtrip::view_expr(expr), alias, r_after_expr, r1);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r1.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    assert(whole == verified_stmt_prec::select_list_prepend(
                        done_v, list_start, verified_stmt_prec::sparse_control_select_list(cur_v)));
                    assert(verified_stmt_prec::sparse_control_select_list(cur_v)
                        == verified_stmt_prec::select_list_prepend(
                            seq![(verified_roundtrip::view_expr(expr), alias)], cur_v,
                            verified_stmt_prec::sparse_control_select_list(r1.drop_first())));
                    verified_stmt_prec::lemma_select_list_resume_step(
                        list_start, cur_v, r1.drop_first(),
                        done_v, verified_roundtrip::view_expr(expr), alias, whole);
                    assert(verified_stmt::view_select_list(select@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), alias)]);
                    assert(whole == verified_stmt_prec::select_list_prepend(
                        verified_stmt::view_select_list(select@),
                        list_start,
                        verified_stmt_prec::sparse_control_select_list(
                            verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)))));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_select_list_last(
                        cur_v, verified_roundtrip::view_expr(expr), alias, r_after_expr, r1);
                    assert(verified_stmt_prec::sparse_control_select_list(cur_v)
                        == (Some(seq![(verified_roundtrip::view_expr(expr), alias)]), r1));
                    assert(whole == (Some(done_v
                        + seq![(verified_roundtrip::view_expr(expr), alias)]), r1));
                    assert(verified_stmt::view_select_list(select@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), alias)]);
                    assert(whole == (Some(verified_stmt::view_select_list(select@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
            break;
        }
    }
    (Some(select), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(900000)]
fn parse_from_clause_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<Vec<ast::From>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_from(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_stmt::view_froms(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); reveal(verified_production::token_view); }
    }
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::From)) {
        let empty: Vec<ast::From> = Vec::new();
        proof {
            reveal_with_fuel(verified_stmt::view_froms, 1);
            assert(empty@ =~= Seq::<ast::From>::empty());
            assert(verified_stmt::view_froms(empty@) =~= Seq::<verified_stmt::SFrom>::empty());
        }
        return (Some(empty), pos, None);
    }
    let ghost list_start = verified_production::token_views(toks@.subrange((pos + 1) as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_from_list(list_start);
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        assert(input[0] == verified_production::TokenView::Keyword(Keyword::From));
        assert(list_start == input.drop_first());
    }
    let mut cur = pos + 1;
    let mut from: Vec<ast::From> = Vec::new();
    loop
        invariant_except_break
            pos < cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Keyword(Keyword::From),
            list_start == input.drop_first(),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 1) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_from_list(list_start),
            sized ==>
                whole == verified_stmt_prec::from_list_prepend(
                    verified_stmt::view_froms(from@),
                    list_start,
                    verified_stmt_prec::sparse_control_from_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos < cur,
            cur <= toks.len(),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Keyword(Keyword::From),
            list_start == input.drop_first(),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 1) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_from_list(list_start),
            sized ==>
                whole == (Some(verified_stmt::view_froms(from@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost outer_start = cur;
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_froms(from@);
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (topt, tc, terr) = parse_from_table_at(toks, cur);
        let mut from_item = match topt {
            Some(t) => t,
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_from_table(cur_v).0 is None);
                        assert(verified_stmt_prec::sparse_control_from_item(cur_v).0 is None);
                        assert(verified_stmt_prec::sparse_control_from_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        assert(verified_stmt_prec::sparse_control_from(input)
                            == verified_stmt_prec::sparse_control_from_list(list_start));
                    }
                }
                return (None, pos, terr);
            },
        };
        let ghost base_v = verified_stmt::view_from(from_item);
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_from_table(cur_v)
                    == (Some(base_v), verified_production::token_views(
                        toks@.subrange(tc as int, toks@.len() as int))));
            }
        }
        proof {
            if sized {
                assert(whole == verified_stmt_prec::from_list_prepend(
                    done_v, list_start, verified_stmt_prec::sparse_control_from_list(cur_v)));
            }
        }
        cur = tc;
        proof {
            assert(cur_v == verified_production::token_views(
                toks@.subrange(outer_start as int, toks@.len() as int)));
        }

        let ghost item_start = cur;
        loop
            invariant_except_break
                pos < cur,
                outer_start < item_start <= cur,
                cur <= toks.len(),
                sized == (toks.len() <= (usize::MAX - 3) / 2),
                input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
                input.len() >= 1,
                input[0] == verified_production::TokenView::Keyword(Keyword::From),
                list_start == input.drop_first(),
                whole == verified_stmt_prec::sparse_control_from_list(list_start),
                sized ==> whole == verified_stmt_prec::from_list_prepend(
                    done_v, list_start,
                    verified_stmt_prec::sparse_control_from_list(
                        verified_production::token_views(toks@.subrange(outer_start as int, toks@.len() as int)))),
                sized ==> verified_stmt_prec::sparse_control_from_table(
                    verified_production::token_views(toks@.subrange(outer_start as int, toks@.len() as int)))
                    == (Some(base_v), verified_production::token_views(
                        toks@.subrange(item_start as int, toks@.len() as int))),
                sized ==>
                    verified_stmt_prec::sparse_control_from_joins(
                        base_v,
                        verified_production::token_views(toks@.subrange(item_start as int, toks@.len() as int)))
                    == verified_stmt_prec::sparse_control_from_joins(
                        verified_stmt::view_from(from_item),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
            ensures
                pos < cur,
                outer_start < item_start <= cur,
                cur <= toks.len(),
                sized ==> verified_stmt_prec::sparse_control_from_table(
                    verified_production::token_views(toks@.subrange(outer_start as int, toks@.len() as int)))
                    == (Some(base_v), verified_production::token_views(
                        toks@.subrange(item_start as int, toks@.len() as int))),
                sized ==>
                    verified_stmt_prec::sparse_control_from_joins(
                        base_v,
                        verified_production::token_views(toks@.subrange(item_start as int, toks@.len() as int)))
                    == (Some(verified_stmt::view_from(from_item)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
            decreases toks.len() - cur,
        {
            let ghost jcur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                        assert(jcur_v.len() == 0);
                        assert(!verified_stmt_prec::is_join_start(jcur_v));
                        verified_stmt_prec::lemma_from_joins_stop(verified_stmt::view_from(from_item), jcur_v);
                    }
                }
                break;
            }
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
            let ghost jt_v: ast::JoinType;
            let ghost needs_on_v: bool;
            let join_type: ast::JoinType;
            let jc: usize;
            match &toks[cur] {
                Token::Keyword(Keyword::Join) => {
                    join_type = ast::JoinType::Inner;
                    jc = cur + 1;
                    proof { jt_v = ast::JoinType::Inner; needs_on_v = true; }
                },
                Token::Keyword(Keyword::Cross) => {
                    if cur + 1 >= toks.len() {
                        proof { if sized { verified_roundtrip::token_views_suffix(toks@, cur as int); verified_roundtrip::token_views_len(toks@.subrange((cur + 1) as int, toks@.len() as int)); assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); verified_roundtrip::token_views_suffix(toks@, (cur + 1) as int); reveal(verified_production::token_view); }
                    if !matches!(toks[cur + 1], Token::Keyword(Keyword::Join)) {
                        proof { if sized { assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[cur + 1].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Cross;
                    jc = cur + 2;
                    proof { jt_v = ast::JoinType::Cross; needs_on_v = false; }
                },
                Token::Keyword(Keyword::Inner) => {
                    if cur + 1 >= toks.len() {
                        proof { if sized { verified_roundtrip::token_views_suffix(toks@, cur as int); verified_roundtrip::token_views_len(toks@.subrange((cur + 1) as int, toks@.len() as int)); assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); verified_roundtrip::token_views_suffix(toks@, (cur + 1) as int); reveal(verified_production::token_view); }
                    if !matches!(toks[cur + 1], Token::Keyword(Keyword::Join)) {
                        proof { if sized { assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[cur + 1].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Inner;
                    jc = cur + 2;
                    proof { jt_v = ast::JoinType::Inner; needs_on_v = true; }
                },
                Token::Keyword(Keyword::Left) => {
                    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
                    let mut c = cur + 1;
                    proof { if c < toks.len() { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); } }
                    if c < toks.len() && matches!(toks[c], Token::Keyword(Keyword::Outer)) {
                        c = c + 1;
                        proof { if c <= toks.len() { verified_roundtrip::token_views_suffix(toks@, (c - 1) as int); if c < toks.len() { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); } } }
                    }
                    if c >= toks.len() {
                        proof { if sized { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    proof { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); }
                    if !matches!(toks[c], Token::Keyword(Keyword::Join)) {
                        proof { if sized { assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[c].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Left;
                    jc = c + 1;
                    proof { jt_v = ast::JoinType::Left; needs_on_v = true; }
                },
                Token::Keyword(Keyword::Right) => {
                    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
                    let mut c = cur + 1;
                    proof { if c < toks.len() { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); } }
                    if c < toks.len() && matches!(toks[c], Token::Keyword(Keyword::Outer)) {
                        c = c + 1;
                        proof { if c <= toks.len() { verified_roundtrip::token_views_suffix(toks@, (c - 1) as int); if c < toks.len() { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); } } }
                    }
                    if c >= toks.len() {
                        proof { if sized { verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int)); assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::UnexpectedEof));
                    }
                    proof { verified_roundtrip::token_views_suffix(toks@, c as int); reveal(verified_production::token_view); }
                    if !matches!(toks[c], Token::Keyword(Keyword::Join)) {
                        proof { if sized { assert(verified_stmt_prec::sparse_control_join_head(jcur_v) is None); from_kw_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input); } }
                        return (None, pos, Some(ParseError::ExpectedToken(
                            Token::Keyword(Keyword::Join),
                            toks[c].clone(),
                        )));
                    }
                    join_type = ast::JoinType::Right;
                    jc = c + 1;
                    proof { jt_v = ast::JoinType::Right; needs_on_v = true; }
                },
                _ => {
                    proof {
                        if sized {
                            assert(!verified_stmt_prec::is_join_start(jcur_v));
                            verified_stmt_prec::lemma_from_joins_stop(verified_stmt::view_from(from_item), jcur_v);
                        }
                    }
                    break;
                },
            }
            let ghost after_kw_v = verified_production::token_views(toks@.subrange(jc as int, toks@.len() as int));
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_join_head(jcur_v)
                        == Some((jt_v, needs_on_v, after_kw_v)));
                    assert(join_type == jt_v);
                }
            }

            proof { verified_roundtrip::token_views_len(toks@.subrange(jc as int, toks@.len() as int)); }
            let (ropt, rc, rerr) = parse_from_table_at(toks, jc);
            let right = match ropt {
                Some(t) => t,
                None => {
                    proof {
                        if sized {
                            assert(verified_stmt_prec::sparse_control_from_table(after_kw_v).0 is None);
                            assert(verified_stmt_prec::sparse_control_from_step(jcur_v) is None);
                            assert(verified_stmt_prec::is_join_start(jcur_v));
                            from_joins_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input);
                        }
                    }
                    return (None, pos, rerr);
                },
            };
            let ghost right_v = verified_stmt::view_from(right);
            let ghost after_table_v = verified_production::token_views(toks@.subrange(rc as int, toks@.len() as int));
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_from_table(after_kw_v)
                        == (Some(right_v), after_table_v));
                }
            }
            let mut cur2 = rc;

            let mut predicate: Option<ast::Expression> = None;
            let ghost pred_v: Option<verified_roundtrip::SExpr>;
            let ghost after_pred_v: Seq<verified_production::TokenView>;
            if !matches!(join_type, ast::JoinType::Cross) {
                proof { if cur2 < toks.len() { verified_roundtrip::token_views_suffix(toks@, cur2 as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(cur2 as int, toks@.len() as int)); } }
                if cur2 >= toks.len() {
                    proof {
                        if sized {
                            assert(verified_stmt_prec::sparse_control_from_step(jcur_v) is None);
                            assert(verified_stmt_prec::is_join_start(jcur_v));
                            from_joins_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input);
                        }
                    }
                    return (None, pos, Some(ParseError::UnexpectedEof));
                }
                if !matches!(toks[cur2], Token::Keyword(Keyword::On)) {
                    proof {
                        if sized {
                            assert(verified_stmt_prec::sparse_control_from_step(jcur_v) is None);
                            assert(verified_stmt_prec::is_join_start(jcur_v));
                            from_joins_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input);
                        }
                    }
                    return (None, pos, Some(ParseError::ExpectedToken(
                        Token::Keyword(Keyword::On),
                        toks[cur2].clone(),
                    )));
                }
                proof { verified_roundtrip::token_views_suffix(toks@, cur2 as int); reveal(verified_production::token_view); }
                cur2 = cur2 + 1;
                let ghost after_on_v = verified_production::token_views(toks@.subrange(cur2 as int, toks@.len() as int));
                proof {
                    verified_roundtrip::token_views_suffix(toks@, (cur2 - 1) as int);
                    assert(after_on_v == after_table_v.drop_first());
                    verified_roundtrip::token_views_len(toks@.subrange(cur2 as int, toks@.len() as int));
                }
                let (opt, c, perr) = parse_clause_expr_at(toks, cur2);
                match opt {
                    Some(e) => {
                        predicate = Some(e);
                        proof {
                            pred_v = Some(verified_roundtrip::view_expr(e));
                            after_pred_v = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
                            if sized {
                                assert(verified_precedence::sparse_prec(after_on_v, 0, verified_stmt_prec::expr_fuel(after_on_v))
                                    == (Some(verified_roundtrip::view_expr(e)), after_pred_v));
                            }
                        }
                        cur2 = c;
                    },
                    None => {
                        proof {
                            if sized {
                                assert(verified_stmt_prec::sparse_control_from_step(jcur_v) is None);
                                assert(verified_stmt_prec::is_join_start(jcur_v));
                                from_joins_reject_here(toks, from_item, item_start, cur, base_v, outer_start, list_start, done_v, whole, input);
                            }
                        }
                        return (None, pos, perr);
                    },
                }
            } else {
                proof { pred_v = None; after_pred_v = after_table_v; }
            }

            let ghost old_from_item = from_item;
            let ghost step_v = verified_stmt::SJoinStep { join_type, right: right_v, predicate: pred_v };
            from_item = ast::From::Join {
                left: Box::new(from_item),
                right: Box::new(right),
                join_type,
                predicate,
            };
            cur = cur2;
            proof {
                if sized {
                    reveal_with_fuel(verified_stmt::view_from, 2);
                    assert(verified_stmt::view_from(from_item)
                        == verified_stmt::apply_step(verified_stmt::view_from(old_from_item), step_v));
                    assert(verified_stmt_prec::sparse_control_from_step(jcur_v)
                        == Some((step_v, after_pred_v)));
                    assert(after_pred_v == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    verified_stmt_prec::lemma_from_joins_step(
                        verified_stmt::view_from(old_from_item), jcur_v, step_v, after_pred_v);
                    assert(verified_stmt_prec::sparse_control_from_joins(
                        verified_stmt::view_from(old_from_item), jcur_v)
                        == verified_stmt_prec::sparse_control_from_joins(
                            verified_stmt::view_from(from_item),
                            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
        }
        let ghost item_v = verified_stmt::view_from(from_item);
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_from_item(cur_v)
                    == verified_stmt_prec::sparse_control_from_joins(base_v,
                        verified_production::token_views(toks@.subrange(item_start as int, toks@.len() as int))));
                assert(verified_stmt_prec::sparse_control_from_item(cur_v)
                    == (Some(item_v), verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int))));
            }
        }
        let ghost old_from = from@;
        from.push(from_item);
        proof {
            verified_stmt_prec::lemma_view_froms_append(old_from, seq![from_item]);
            verified_stmt_prec::lemma_view_froms_single(from_item);
            assert(from@ == old_from + seq![from_item]);
            assert(verified_stmt::view_froms(from@) == done_v + seq![item_v]);
        }

        proof { if cur < toks.len() { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); } else { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); } }
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                if sized {
                    verified_stmt_prec::lemma_from_list_step(cur_v, item_v,
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                if sized {
                    verified_stmt_prec::lemma_from_list_resume_step(
                        list_start, cur_v,
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                        done_v, item_v, whole);
                    assert(verified_stmt::view_froms(from@) == done_v + seq![item_v]);
                }
            }
        } else {
            proof {
                if sized {
                    verified_stmt_prec::lemma_from_list_last(cur_v, item_v,
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                    assert(verified_stmt_prec::sparse_control_from_list(cur_v)
                        == (Some(seq![item_v]), verified_production::token_views(
                            toks@.subrange(cur as int, toks@.len() as int))));
                    assert(whole == (Some(done_v + seq![item_v]),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                    assert(verified_stmt::view_froms(from@) == done_v + seq![item_v]);
                }
            }
            break;
        }
    }
    proof {
        if sized {
            assert(verified_stmt_prec::sparse_control_from(input)
                == verified_stmt_prec::sparse_control_from_list(list_start));
        }
    }
    (Some(from), cur, None)
}

proof fn from_joins_reject_here(
    toks: &Vec<Token>,
    from_item: ast::From,
    item_start: usize,
    cur: usize,
    base_v: verified_stmt::SFrom,
    cur_start: usize,
    list_start: Seq<verified_production::TokenView>,
    done_v: Seq<verified_stmt::SFrom>,
    whole: (Option<Seq<verified_stmt::SFrom>>, Seq<verified_production::TokenView>),
    input: Seq<verified_production::TokenView>,
)
    requires
        cur_start <= item_start <= cur <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        input.len() >= 1,
        input[0] == verified_production::TokenView::Keyword(Keyword::From),
        list_start == input.drop_first(),
        whole == verified_stmt_prec::sparse_control_from_list(list_start),
        verified_stmt_prec::sparse_control_from_table(
            verified_production::token_views(toks@.subrange(cur_start as int, toks@.len() as int)))
            == (Some(base_v), verified_production::token_views(
                toks@.subrange(item_start as int, toks@.len() as int))),
        verified_stmt_prec::sparse_control_from_joins(
            base_v,
            verified_production::token_views(toks@.subrange(item_start as int, toks@.len() as int)))
        == verified_stmt_prec::sparse_control_from_joins(
            verified_stmt::view_from(from_item),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        verified_stmt_prec::is_join_start(
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        verified_stmt_prec::sparse_control_from_step(
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))) is None,
        whole == verified_stmt_prec::from_list_prepend(
            done_v, list_start,
            verified_stmt_prec::sparse_control_from_list(
                verified_production::token_views(toks@.subrange(cur_start as int, toks@.len() as int)))),
    ensures
        whole.0 is None,
        verified_stmt_prec::sparse_control_from(input).0 is None,
{
    let cur_v = verified_production::token_views(toks@.subrange(cur_start as int, toks@.len() as int));
    verified_stmt_prec::lemma_from_joins_reject(
        verified_stmt::view_from(from_item),
        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
    assert(verified_stmt_prec::sparse_control_from_item(cur_v).0 is None);
    assert(verified_stmt_prec::sparse_control_from_list(cur_v).0 is None);
    assert(verified_stmt_prec::sparse_control_from(input)
        == verified_stmt_prec::sparse_control_from_list(list_start));
}

proof fn from_kw_reject_here(
    toks: &Vec<Token>,
    from_item: ast::From,
    item_start: usize,
    cur: usize,
    base_v: verified_stmt::SFrom,
    cur_start: usize,
    list_start: Seq<verified_production::TokenView>,
    done_v: Seq<verified_stmt::SFrom>,
    whole: (Option<Seq<verified_stmt::SFrom>>, Seq<verified_production::TokenView>),
    input: Seq<verified_production::TokenView>,
)
    requires
        cur_start <= item_start <= cur <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        input.len() >= 1,
        input[0] == verified_production::TokenView::Keyword(Keyword::From),
        list_start == input.drop_first(),
        whole == verified_stmt_prec::sparse_control_from_list(list_start),
        verified_stmt_prec::sparse_control_from_table(
            verified_production::token_views(toks@.subrange(cur_start as int, toks@.len() as int)))
            == (Some(base_v), verified_production::token_views(
                toks@.subrange(item_start as int, toks@.len() as int))),
        verified_stmt_prec::sparse_control_from_joins(
            base_v,
            verified_production::token_views(toks@.subrange(item_start as int, toks@.len() as int)))
        == verified_stmt_prec::sparse_control_from_joins(
            verified_stmt::view_from(from_item),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        verified_stmt_prec::is_join_start(
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        verified_stmt_prec::sparse_control_join_head(
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))) is None,
        whole == verified_stmt_prec::from_list_prepend(
            done_v, list_start,
            verified_stmt_prec::sparse_control_from_list(
                verified_production::token_views(toks@.subrange(cur_start as int, toks@.len() as int)))),
    ensures
        whole.0 is None,
        verified_stmt_prec::sparse_control_from(input).0 is None,
{
    assert(verified_stmt_prec::sparse_control_from_step(
        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))) is None);
    from_joins_reject_here(toks, from_item, item_start, cur, base_v, cur_start,
        list_start, done_v, whole, input);
}

fn parse_from_table_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::From>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_from_table(input);
            match r.0 {
                Some(f) => sopt is Some
                    && verified_stmt::view_from(f) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    let name = match &toks[pos] {
        Token::Ident(n) => n.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone()))),
    };
    proof { reveal(verified_production::token_view); }
    let mut cur = pos + 1;
    let ghost r_after_name = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        assert(r_after_name == input.drop_first());
    }

    let is_as = cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As));
    let is_ident = cur < toks.len() && matches!(toks[cur], Token::Ident(_));
    proof {
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        } else {
            verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        }
    }
    let mut alias: Option<String> = None;
    if is_as || is_ident {
        if is_as {
            cur = cur + 1;
            if cur >= toks.len() {
                proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof { verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int); }
        }
        proof {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
            reveal(verified_production::token_view);
        }
        match &toks[cur] {
            Token::Ident(n) => {
                alias = Some(n.clone());
                cur = cur + 1;
            },
            _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
        }
    }
    proof {
        if cur < toks.len() {
            verified_roundtrip::token_views_suffix(toks@, cur as int);
        } else {
            verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
        }
    }
    (Some(ast::From::Table { name, alias }), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_group_by_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<Vec<ast::Expression>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_group_by(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_roundtrip::view_args(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    }
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::Group)) {
        return (Some(Vec::new()), pos, None);
    }
    let mut cur = pos + 1;
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::By)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::By),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    proof {
        assert(toks@[pos as int] == Token::Keyword(Keyword::Group));
        assert(toks@[(pos + 1) as int] == Token::Keyword(Keyword::By));
    }
    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_group_list(list_start);
    proof {
        order_by_input_head(toks, pos);
        assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
        assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
        assert(list_start == input.drop_first().drop_first());
    }
    let mut group_by: Vec<ast::Expression> = Vec::new();
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Group),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_group_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == verified_stmt_prec::group_list_prepend(
                    verified_roundtrip::view_args(group_by@),
                    list_start,
                    verified_stmt_prec::sparse_control_group_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Group),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_group_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == (Some(verified_roundtrip::view_args(group_by@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_roundtrip::view_args(group_by@);
        let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => {
                proof {
                    if sized {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_group_list, 1);
                        assert(verified_stmt_prec::sparse_control_group_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        order_by_input_head(toks, pos);
                        group_by_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, eerr);
            },
        };
        let ghost r_after_expr = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_precedence::sparse_prec(cur_v, 0, verified_stmt_prec::expr_fuel(cur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            if sized && c < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, c as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int));
            }
        }
        cur = c;
        let ghost old_group = group_by@;
        group_by.push(expr);
        proof {
            verified_stmt_prec::lemma_view_args_append(old_group, seq![expr]);
            verified_stmt_prec::lemma_view_args_single(expr);
            assert(group_by@ == old_group + seq![expr]);
            assert(verified_roundtrip::view_args(group_by@)
                == done_v + seq![verified_roundtrip::view_expr(expr)]);
        }

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    verified_stmt_prec::lemma_group_list_step(
                        cur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_after_expr.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    assert(whole == verified_stmt_prec::group_list_prepend(
                        done_v, list_start, verified_stmt_prec::sparse_control_group_list(cur_v)));
                    assert(verified_stmt_prec::sparse_control_group_list(cur_v)
                        == verified_stmt_prec::group_list_prepend(
                            seq![verified_roundtrip::view_expr(expr)], cur_v,
                            verified_stmt_prec::sparse_control_group_list(r_after_expr.drop_first())));
                    verified_stmt_prec::lemma_group_list_resume_step(
                        list_start, cur_v, r_after_expr.drop_first(),
                        done_v, verified_roundtrip::view_expr(expr), whole);
                    assert(verified_roundtrip::view_args(group_by@)
                        == done_v + seq![verified_roundtrip::view_expr(expr)]);
                    assert(whole == verified_stmt_prec::group_list_prepend(
                        verified_roundtrip::view_args(group_by@),
                        list_start,
                        verified_stmt_prec::sparse_control_group_list(
                            verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)))));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_group_list_last(
                        cur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                    assert(verified_stmt_prec::sparse_control_group_list(cur_v)
                        == (Some(seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                    assert(whole == (Some(done_v
                        + seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                    assert(verified_roundtrip::view_args(group_by@)
                        == done_v + seq![verified_roundtrip::view_expr(expr)]);
                    assert(whole == (Some(verified_roundtrip::view_args(group_by@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
            break;
        }
    }
    proof {
        if toks.len() <= (usize::MAX - 3) / 2 {
            group_by_conclude_some(toks, pos, cur, list_start, whole,
                verified_roundtrip::view_args(group_by@));
        }
    }
    (Some(group_by), cur, None)
}

proof fn order_by_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 2 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 2,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
}

proof fn order_by_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<(verified_roundtrip::SExpr, ast::Direction)>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Order),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_order_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_order_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

proof fn order_by_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<(verified_roundtrip::SExpr, ast::Direction)>>, Seq<verified_production::TokenView>),
    items: Seq<(verified_roundtrip::SExpr, ast::Direction)>,
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Order),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_order_list(list_start),
        whole == (Some(items),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_order_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(items),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

proof fn group_by_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_roundtrip::SExpr>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Group),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_group_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_group_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

proof fn group_by_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_roundtrip::SExpr>>, Seq<verified_production::TokenView>),
    items: Seq<verified_roundtrip::SExpr>,
)
    requires
        pos + 2 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Group),
        toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
        list_start == verified_production::token_views(
            toks@.subrange((pos + 2) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_group_list(list_start),
        whole == (Some(items),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_group_by(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(items),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    order_by_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Group));
    assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
    assert(list_start == input.drop_first().drop_first());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_order_by_at(toks: &Vec<Token>, pos: usize) -> (r: (
    Option<Vec<(ast::Expression, ast::Direction)>>,
    usize,
    Option<ParseError>,
))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_order_by(input);
            match r.0 {
                Some(v) => sopt is Some
                    && verified_stmt::view_order_list(v@) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    }
    if pos >= toks.len() || !matches!(toks[pos], Token::Keyword(Keyword::Order)) {
        return (Some(Vec::new()), pos, None);
    }
    let mut cur = pos + 1;
    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::By)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::By),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    proof {
        assert(toks@[pos as int] == Token::Keyword(Keyword::Order));
        assert(toks@[(pos + 1) as int] == Token::Keyword(Keyword::By));
    }
    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_order_list(list_start);
    proof {
        order_by_input_head(toks, pos);
        assert(input[0] == verified_production::TokenView::Keyword(Keyword::Order));
        assert(input[1] == verified_production::TokenView::Keyword(Keyword::By));
        assert(list_start == input.drop_first().drop_first());
    }
    let mut order_by: Vec<(ast::Expression, ast::Direction)> = Vec::new();
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Order),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_order_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == verified_stmt_prec::order_list_prepend(
                    verified_stmt::view_order_list(order_by@),
                    list_start,
                    verified_stmt_prec::sparse_control_order_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
                ),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            toks@[pos as int] == Token::Keyword(Keyword::Order),
            toks@[(pos + 1) as int] == Token::Keyword(Keyword::By),
            list_start == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_order_list(list_start),
            toks.len() <= (usize::MAX - 3) / 2 ==>
                whole == (Some(verified_stmt::view_order_list(order_by@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_order_list(order_by@);
        let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, c, eerr) = parse_clause_expr_at(toks, cur);
        let expr = match opt {
            Some(e) => e,
            None => {
                proof {
                    if sized {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_order_list, 1);
                        assert(verified_stmt_prec::sparse_control_order_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        order_by_input_head(toks, pos);
                        order_by_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, eerr);
            },
        };
        let ghost r_after_expr = verified_production::token_views(toks@.subrange(c as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_precedence::sparse_prec(cur_v, 0, verified_stmt_prec::expr_fuel(cur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            if sized && c < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, c as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(c as int, toks@.len() as int));
            }
        }
        cur = c;

        let mut direction = ast::Direction::Ascending;
        let ghost c_head_is_dir: bool = r_after_expr.len() >= 1
            && (r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Asc)
                || r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Desc));
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
            match &toks[cur] {
                Token::Keyword(Keyword::Asc) => {
                    direction = ast::Direction::Ascending;
                    cur = cur + 1;
                },
                Token::Keyword(Keyword::Desc) => {
                    direction = ast::Direction::Descending;
                    cur = cur + 1;
                },
                _ => {},
            }
        } else {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        }
        let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        proof {
            if sized {
                if c_head_is_dir {
                    assert(r1 == r_after_expr.drop_first());
                    assert(r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Asc)
                        ==> direction == ast::Direction::Ascending);
                    assert(r_after_expr[0] == verified_production::TokenView::Keyword(Keyword::Desc)
                        ==> direction == ast::Direction::Descending);
                } else {
                    assert(r1 == r_after_expr);
                    assert(direction == ast::Direction::Ascending);
                }
            }
        }
        let ghost old_order = order_by@;
        order_by.push((expr, direction));
        proof {
            verified_stmt_prec::lemma_view_order_list_append(old_order, seq![(expr, direction)]);
            verified_stmt_prec::lemma_view_order_list_single(expr, direction);
            assert(order_by@ == old_order + seq![(expr, direction)]);
            assert(verified_stmt::view_order_list(order_by@)
                == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
        }

        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    verified_stmt_prec::lemma_order_list_step(
                        cur_v, verified_roundtrip::view_expr(expr), direction, r_after_expr, r1);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r1.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    assert(whole == verified_stmt_prec::order_list_prepend(
                        done_v, list_start, verified_stmt_prec::sparse_control_order_list(cur_v)));
                    assert(verified_stmt_prec::sparse_control_order_list(cur_v)
                        == verified_stmt_prec::order_list_prepend(
                            seq![(verified_roundtrip::view_expr(expr), direction)], cur_v,
                            verified_stmt_prec::sparse_control_order_list(r1.drop_first())));
                    verified_stmt_prec::lemma_order_list_resume_step(
                        list_start, cur_v, r1.drop_first(),
                        done_v, verified_roundtrip::view_expr(expr), direction, whole);
                    assert(verified_stmt::view_order_list(order_by@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
                    assert(whole == verified_stmt_prec::order_list_prepend(
                        verified_stmt::view_order_list(order_by@),
                        list_start,
                        verified_stmt_prec::sparse_control_order_list(
                            verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)))));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_order_list_last(
                        cur_v, verified_roundtrip::view_expr(expr), direction, r_after_expr, r1);
                    assert(verified_stmt_prec::sparse_control_order_list(cur_v)
                        == (Some(seq![(verified_roundtrip::view_expr(expr), direction)]), r1));
                    assert(whole == (Some(done_v
                        + seq![(verified_roundtrip::view_expr(expr), direction)]), r1));
                    assert(verified_stmt::view_order_list(order_by@)
                        == done_v + seq![(verified_roundtrip::view_expr(expr), direction)]);
                    assert(whole == (Some(verified_stmt::view_order_list(order_by@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                }
            }
            break;
        }
    }
    proof {
        if toks.len() <= (usize::MAX - 3) / 2 {
            order_by_conclude_some(toks, pos, cur, list_start, whole,
                verified_stmt::view_order_list(order_by@));
        }
    }
    (Some(order_by), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_create_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_create(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }

    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); reveal(verified_production::token_view); }
    if !matches!(toks[pos], Token::Keyword(Keyword::Table)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Table),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    let name = match &toks[cur] {
        Token::Ident(n) => n.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    proof { assert(input[1] == verified_production::TokenView::Ident(name)); }
    cur = cur + 1;

    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    if !matches!(toks[cur], Token::OpenParen) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::OpenParen,
            toks[cur].clone(),
        )));
    }
    proof { assert(input[2] == verified_production::TokenView::OpenParen); }
    cur = cur + 1;

    let ghost list_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost whole = verified_stmt_prec::sparse_control_column_list(list_start);
    proof {
        assert(cur == pos + 3);
        create_input_head(toks, pos);
        assert(list_start == input.drop_first().drop_first().drop_first());
    }

    let mut columns: Vec<ast::Column> = Vec::new();
    loop
        invariant_except_break
            pos + 3 <= cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            input[0] == verified_production::TokenView::Keyword(Keyword::Table),
            input[1] == verified_production::TokenView::Ident(name),
            input[2] == verified_production::TokenView::OpenParen,
            toks@[pos as int] == Token::Keyword(Keyword::Table),
            toks@[(pos + 2) as int] == Token::OpenParen,
            list_start == verified_production::token_views(
                toks@.subrange((pos + 3) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_column_list(list_start),
            sized ==> whole == verified_stmt_prec::column_list_prepend(
                verified_stmt::view_columns(columns@),
                list_start,
                verified_stmt_prec::sparse_control_column_list(
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
        ensures
            pos + 3 <= cur,
            cur <= toks.len(),
            input[0] == verified_production::TokenView::Keyword(Keyword::Table),
            input[1] == verified_production::TokenView::Ident(name),
            input[2] == verified_production::TokenView::OpenParen,
            list_start == verified_production::token_views(
                toks@.subrange((pos + 3) as int, toks@.len() as int)),
            whole == verified_stmt_prec::sparse_control_column_list(list_start),
            sized ==> whole == (Some(verified_stmt::view_columns(columns@)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_columns(columns@);
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (copt, ncur, cerr) = parse_create_column_at(toks, cur);
        let column = match copt {
            Some(c) => c,
            None => {
                proof {
                    if sized {
                        assert(verified_stmt_prec::sparse_control_column(cur_v).0 is None);
                        assert(verified_stmt_prec::sparse_control_column_list(cur_v).0 is None);
                        assert(whole.0 is None);
                        create_conclude_none(toks, pos, list_start, whole);
                    }
                }
                return (None, pos, cerr);
            },
        };
        let ghost r_after_col = verified_production::token_views(toks@.subrange(ncur as int, toks@.len() as int));
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_column(cur_v)
                    == (Some(verified_stmt::view_column(column)), r_after_col));
            }
        }
        cur = ncur;
        let ghost old_cols = columns@;
        columns.push(column);
        proof {
            verified_stmt_prec::lemma_view_columns_append(old_cols, seq![column]);
            verified_stmt_prec::lemma_view_columns_single(column);
            assert(columns@ == old_cols + seq![column]);
            assert(verified_stmt::view_columns(columns@)
                == done_v + seq![verified_stmt::view_column(column)]);
        }
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                if sized {
                    verified_stmt_prec::lemma_column_list_step(
                        cur_v, verified_stmt::view_column(column), r_after_col);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_after_col.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    verified_stmt_prec::lemma_column_list_resume_step(
                        list_start, cur_v, r_after_col.drop_first(),
                        done_v, verified_stmt::view_column(column), whole);
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                    reveal(verified_production::token_view);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_column_list_last(
                        cur_v, verified_stmt::view_column(column), r_after_col);
                    assert(verified_stmt_prec::sparse_control_column_list(cur_v)
                        == (Some(seq![verified_stmt::view_column(column)]), r_after_col));
                }
            }
            break;
        }
    }
    let ghost after_list = cur;

    proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
    if cur >= toks.len() {
        proof {
            if sized {
                create_conclude_reject_close(toks, pos, cur, list_start, whole,
                    verified_stmt::view_columns(columns@));
            }
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
    if !matches!(toks[cur], Token::CloseParen) {
        proof {
            if sized {
                create_conclude_reject_close(toks, pos, cur, list_start, whole,
                    verified_stmt::view_columns(columns@));
            }
        }
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::CloseParen,
            toks[cur].clone(),
        )));
    }
    let ghost close_at = cur;
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    cur = cur + 1;

    proof {
        if sized {
            create_conclude_some(toks, pos, close_at, cur, list_start, whole,
                verified_stmt::view_columns(columns@), name);
        }
    }
    (Some(ast::Statement::CreateTable { name, columns }), cur, None)
}

proof fn create_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 3 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 3,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[2]
            == verified_production::token_view(toks@[(pos + 2) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 3) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 2) as int);
}

proof fn create_conclude_none(
    toks: &Vec<Token>,
    pos: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
)
    requires
        pos + 3 <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 2) as int] == Token::OpenParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
}

proof fn create_conclude_reject_close(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
    cols: Seq<verified_stmt::SColumn>,
)
    requires
        pos + 3 <= toks.len(),
        cur <= toks.len(),
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 2) as int] == Token::OpenParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole == (Some(cols),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        !(cur < toks.len() && toks@[cur as int] == Token::CloseParen),
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
    let r3 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
    if cur < toks.len() {
        verified_roundtrip::token_views_suffix(toks@, cur as int);
        assert(r3[0] == verified_production::token_view(toks@[cur as int]));
        assert(r3[0] != verified_production::TokenView::CloseParen);
    } else {
        assert(r3.len() == 0);
    }
}

proof fn create_conclude_some(
    toks: &Vec<Token>,
    pos: usize,
    close_at: usize,
    cur: usize,
    list_start: Seq<verified_production::TokenView>,
    whole: (Option<Seq<verified_stmt::SColumn>>, Seq<verified_production::TokenView>),
    cols: Seq<verified_stmt::SColumn>,
    name: String,
)
    requires
        pos + 3 <= toks.len(),
        close_at < toks.len(),
        cur == close_at + 1,
        toks@[pos as int] == Token::Keyword(Keyword::Table),
        toks@[(pos + 1) as int] == Token::Ident(name),
        toks@[(pos + 2) as int] == Token::OpenParen,
        toks@[close_at as int] == Token::CloseParen,
        list_start == verified_production::token_views(
            toks@.subrange((pos + 3) as int, toks@.len() as int)),
        whole == verified_stmt_prec::sparse_control_column_list(list_start),
        whole == (Some(cols),
            verified_production::token_views(toks@.subrange(close_at as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_create(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(verified_stmt::SStmt::CreateTable { name, columns: cols }),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    create_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(input[0] == verified_production::TokenView::Keyword(Keyword::Table));
    assert(input[1] == verified_production::TokenView::Ident(name));
    assert(input[2] == verified_production::TokenView::OpenParen);
    assert(list_start == input.drop_first().drop_first().drop_first());
    let r3 = verified_production::token_views(toks@.subrange(close_at as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, close_at as int);
    assert(r3[0] == verified_production::TokenView::CloseParen);
    assert(r3.drop_first() == verified_production::token_views(
        toks@.subrange(cur as int, toks@.len() as int)));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100000)]
fn parse_create_column_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Column>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_column(input);
            match r.0 {
                Some(c) => sopt is Some
                    && verified_stmt::view_column(c) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }

    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); reveal(verified_production::token_view); }
    let name = match &toks[pos] {
        Token::Ident(n) => n.clone(),
        _ => {
            proof { assert(!(input[0] is Ident)); }
            return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone())));
        },
    };
    proof { assert(input[0] == verified_production::TokenView::Ident(name)); }
    let mut cur = pos + 1;

    if cur >= toks.len() {
        proof {
            verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
            verified_roundtrip::token_views_suffix(toks@, pos as int);
            assert(input.drop_first() == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        verified_roundtrip::token_views_suffix(toks@, cur as int);
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        reveal(verified_production::token_view);
        assert(input.drop_first() == verified_production::token_views(
            toks@.subrange(cur as int, toks@.len() as int)));
        assert(input[1] == verified_production::token_view(toks@[cur as int]));
    }
    let datatype = match &toks[cur] {
        Token::Keyword(Keyword::Bool) | Token::Keyword(Keyword::Boolean) => DataType::Boolean,
        Token::Keyword(Keyword::Float) | Token::Keyword(Keyword::Double) => DataType::Float,
        Token::Keyword(Keyword::Int) | Token::Keyword(Keyword::Integer) => DataType::Integer,
        Token::Keyword(Keyword::String)
        | Token::Keyword(Keyword::Text)
        | Token::Keyword(Keyword::Varchar) => DataType::String,
        _ => {
            proof { assert(verified_stmt_prec::parse_column_datatype_kw(input[1]) is None); }
            return (None, pos, Some(ParseError::UnexpectedToken(toks[cur].clone())));
        },
    };
    proof {
        reveal(verified_production::token_view);
        assert(verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_view(toks@[cur as int])) == Some(datatype));
    }
    cur = cur + 1;

    let ghost cstart = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost cwhole = verified_stmt_prec::sparse_control_col_constraints(
        cstart, name, datatype, verified_stmt_prec::col_acc_empty());
    proof {
        assert(cur == pos + 2);
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
        assert(cstart == input.drop_first().drop_first());
        assert(input[0] == verified_production::token_view(toks@[pos as int]));
        assert(input[1] == verified_production::token_view(toks@[(pos + 1) as int]));
        assert(input[0] == verified_production::TokenView::Ident(name));
        assert(verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype));
    }

    let mut primary_key = false;
    let mut nullable: Option<bool> = None;
    let mut default: Option<ast::Expression> = None;
    let mut unique = false;
    let mut index = false;
    let mut references: Option<String> = None;
    loop
        invariant_except_break
            pos + 2 <= cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(
                toks@.subrange(pos as int, toks@.len() as int)),
            cstart == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            cwhole == verified_stmt_prec::sparse_control_col_constraints(
                cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
            input[0] == verified_production::TokenView::Ident(name),
            verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype),
            sized ==> cwhole == verified_stmt_prec::sparse_control_col_constraints(
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                name, datatype,
                verified_stmt_prec::ColAcc {
                    primary_key,
                    nullable,
                    default: verified_stmt_prec::opt_view_expr(default),
                    unique,
                    index,
                    references,
                }),
        ensures
            pos + 2 <= cur,
            cur <= toks.len(),
            cstart == verified_production::token_views(
                toks@.subrange((pos + 2) as int, toks@.len() as int)),
            input[0] == verified_production::TokenView::Ident(name),
            verified_stmt_prec::parse_column_datatype_kw(input[1]) == Some(datatype),
            sized ==> cwhole == (
                Some(verified_stmt::view_column(ast::Column {
                    name, datatype, primary_key, nullable, default, unique, index, references,
                })),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost acc_cur = verified_stmt_prec::ColAcc {
            primary_key,
            nullable,
            default: verified_stmt_prec::opt_view_expr(default),
            unique,
            index,
            references,
        };
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        if cur >= toks.len() {
            proof {
                if sized {
                    assert(cur_v.len() == 0);
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == (Some(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)), cur_v));
                    assert(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)
                        == verified_stmt::view_column(ast::Column {
                            name, datatype, primary_key, nullable, default, unique, index, references,
                        }));
                }
            }
            break;
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); reveal(verified_production::token_view); }
        let keyword = match &toks[cur] {
            Token::Keyword(k) => *k,
            _ => {
                proof {
                    if sized {
                        assert(!(cur_v[0] is Keyword));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                            == (Some(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)), cur_v));
                        assert(verified_stmt_prec::col_from_acc(name, datatype, acc_cur)
                            == verified_stmt::view_column(ast::Column {
                                name, datatype, primary_key, nullable, default, unique, index, references,
                            }));
                    }
                }
                break;
            },
        };
        proof { assert(cur_v[0] == verified_production::TokenView::Keyword(keyword)); }
        let ghost r_after_kw = verified_production::token_views(toks@.subrange((cur + 1) as int, toks@.len() as int));
        proof { assert(cur_v.drop_first() == r_after_kw); }
        cur = cur + 1;
        if matches!(keyword, Keyword::Primary) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            if !matches!(toks[cur], Token::Keyword(Keyword::Key)) {
                proof {
                    if sized {
                        assert(r_after_kw[0] != verified_production::TokenView::Keyword(Keyword::Key));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::ExpectedToken(
                    Token::Keyword(Keyword::Key),
                    toks[cur].clone(),
                )));
            }
            proof {
                assert(r_after_kw[0] == verified_production::TokenView::Keyword(Keyword::Key));
                verified_roundtrip::token_views_suffix(toks@, cur as int);
            }
            cur = cur + 1;
            primary_key = true;
            proof {
                if sized {
                    assert(r_after_kw.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw.drop_first(), name, datatype,
                            verified_stmt_prec::ColAcc { primary_key: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Null) {
            if nullable.is_some() {
                proof {
                    if sized {
                        assert(acc_cur.nullable is Some);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::NullabilityAlreadySet(name.clone())));
            }
            nullable = Some(true);
            proof {
                if sized {
                    assert(!(acc_cur.nullable is Some));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { nullable: Some(true), ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Not) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            if !matches!(toks[cur], Token::Keyword(Keyword::Null)) {
                proof {
                    if sized {
                        assert(r_after_kw[0] != verified_production::TokenView::Keyword(Keyword::Null));
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::ExpectedToken(
                    Token::Keyword(Keyword::Null),
                    toks[cur].clone(),
                )));
            }
            proof { assert(r_after_kw[0] == verified_production::TokenView::Keyword(Keyword::Null)); }
            cur = cur + 1;
            if nullable.is_some() {
                proof {
                    if sized {
                        assert(acc_cur.nullable is Some);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::NullabilityAlreadySet(name.clone())));
            }
            nullable = Some(false);
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                if sized {
                    assert(!(acc_cur.nullable is Some));
                    assert(r_after_kw.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw.drop_first(), name, datatype,
                            verified_stmt_prec::ColAcc { nullable: Some(false), ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Default) {
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                proof { assert(!sized); }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            let (opt, consumed, derr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            match opt {
                Some(expr) => {
                    proof {
                        if sized {
                            let r_e = verified_production::token_views(toks@.subrange(consumed as int, toks@.len() as int));
                            assert(fuel == verified_stmt_prec::expr_fuel(r_after_kw));
                            assert(verified_precedence::sparse_prec(r_after_kw, 0, verified_stmt_prec::expr_fuel(r_after_kw))
                                == (Some(verified_roundtrip::view_expr(expr)), r_e));
                        }
                    }
                    default = Some(expr);
                    cur = consumed;
                    proof {
                        if sized {
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                                == verified_stmt_prec::sparse_control_col_constraints(
                                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                                    name, datatype,
                                    verified_stmt_prec::ColAcc {
                                        default: Some(verified_roundtrip::view_expr(expr)), ..acc_cur }));
                        }
                    }
                },
                None => {
                    proof {
                        if sized {
                            assert(verified_precedence::sparse_prec(r_after_kw, 0, verified_stmt_prec::expr_fuel(r_after_kw)).0 is None);
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                            col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                        }
                    }
                    return (None, pos, derr);
                },
            }
        } else if matches!(keyword, Keyword::Unique) {
            unique = true;
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { unique: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::Index) {
            index = true;
            proof {
                if sized {
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                        == verified_stmt_prec::sparse_control_col_constraints(
                            r_after_kw, name, datatype,
                            verified_stmt_prec::ColAcc { index: true, ..acc_cur }));
                }
            }
        } else if matches!(keyword, Keyword::References) {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            if cur >= toks.len() {
                proof {
                    if sized {
                        assert(r_after_kw.len() < 1);
                        assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                        col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                    }
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                reveal(verified_production::token_view);
                assert(r_after_kw == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
                assert(r_after_kw[0] == verified_production::token_view(toks@[cur as int]));
            }
            match &toks[cur] {
                Token::Ident(nm) => {
                    let ghost nmv = nm@;
                    references = Some(nm.clone());
                    proof { assert(r_after_kw[0] == verified_production::TokenView::Ident(*nm)); }
                    cur = cur + 1;
                    proof {
                        verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                        if sized {
                            assert(r_after_kw.drop_first() == verified_production::token_views(
                                toks@.subrange(cur as int, toks@.len() as int)));
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur)
                                == verified_stmt_prec::sparse_control_col_constraints(
                                    r_after_kw.drop_first(), name, datatype,
                                    verified_stmt_prec::ColAcc { references: references, ..acc_cur }));
                        }
                    }
                },
                _ => {
                    proof {
                        if sized {
                            assert(!(r_after_kw[0] is Ident));
                            assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                            col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                        }
                    }
                    return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone())));
                },
            }
        } else {
            proof {
                if sized {
                    assert(keyword != Keyword::Primary && keyword != Keyword::Null
                        && keyword != Keyword::Not && keyword != Keyword::Default
                        && keyword != Keyword::Unique && keyword != Keyword::Index
                        && keyword != Keyword::References);
                    assert(verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None);
                    col_constraints_reject(toks, pos, cstart, cwhole, cur_v, name, datatype, acc_cur);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedKeyword(keyword)));
        }
    }

    let column = ast::Column {
        name,
        datatype,
        primary_key,
        nullable,
        default,
        unique,
        index,
        references,
    };
    proof {
        if sized {
            col_constraints_accept(toks, pos, cur, cstart, cwhole, name, datatype, column);
        }
    }
    (Some(column), cur, None)
}

proof fn col_constraints_reject(
    toks: &Vec<Token>,
    pos: usize,
    cstart: Seq<verified_production::TokenView>,
    cwhole: (Option<verified_stmt::SColumn>, Seq<verified_production::TokenView>),
    cur_v: Seq<verified_production::TokenView>,
    name: String,
    datatype: DataType,
    acc_cur: verified_stmt_prec::ColAcc,
)
    requires
        pos + 2 <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        cstart == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::TokenView::Ident(name),
        verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]) == Some(datatype),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(
            cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur),
        verified_stmt_prec::sparse_control_col_constraints(cur_v, name, datatype, acc_cur).0 is None,
    ensures
        verified_stmt_prec::sparse_control_column(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))).0 is None,
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    col_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(cstart == input.drop_first().drop_first());
    assert(cwhole.0 is None);
}

proof fn col_constraints_accept(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    cstart: Seq<verified_production::TokenView>,
    cwhole: (Option<verified_stmt::SColumn>, Seq<verified_production::TokenView>),
    name: String,
    datatype: DataType,
    column: ast::Column,
)
    requires
        pos + 2 <= toks.len(),
        cur <= toks.len(),
        toks.len() <= (usize::MAX - 3) / 2,
        cstart == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::TokenView::Ident(name),
        verified_stmt_prec::parse_column_datatype_kw(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]) == Some(datatype),
        cwhole == verified_stmt_prec::sparse_control_col_constraints(
            cstart, name, datatype, verified_stmt_prec::col_acc_empty()),
        column.name == name,
        column.datatype == datatype,
        cwhole == (
            Some(verified_stmt::view_column(column)),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_column(
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)))
            == (Some(verified_stmt::view_column(column)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
    let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    col_input_head(toks, pos);
    reveal(verified_production::token_view);
    assert(cstart == input.drop_first().drop_first());
}

proof fn col_input_head(toks: &Vec<Token>, pos: usize)
    requires
        pos + 2 <= toks.len(),
    ensures
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)).len() >= 2,
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[0]
            == verified_production::token_view(toks@[pos as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))[1]
            == verified_production::token_view(toks@[(pos + 1) as int]),
        verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            .drop_first().drop_first()
            == verified_production::token_views(toks@.subrange((pos + 2) as int, toks@.len() as int)),
{
    verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
    verified_roundtrip::token_views_suffix(toks@, pos as int);
    verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(900000)]
fn parse_update_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_update(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    if pos >= toks.len() {
        proof {
            verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
            assert(input.len() == 0);
            assert(verified_stmt_prec::sparse_control_update(input).0 is None);
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    let table = match &toks[pos] {
        Token::Ident(name) => name.clone(),
        _ => {
            proof {
                reveal(verified_production::token_view);
                assert(input.len() >= 1);
                assert(input[0] == verified_production::token_view(toks@[pos as int]));
                assert(match input[0] {
                    verified_production::TokenView::Ident(_) => false,
                    _ => true,
                });
                assert(verified_stmt_prec::sparse_control_update(input).0 is None);
            }
            return (None, pos, Some(ParseError::ExpectedIdent(toks[pos].clone())));
        },
    };
    let mut cur = pos + 1;
    let ghost r0 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        assert(r0 == input.drop_first());
        assert(input[0] == verified_production::TokenView::Ident(table));
    }

    if cur >= toks.len() {
        proof {
            verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
            assert(r0.len() == 0);
            assert(verified_stmt_prec::sparse_control_update(input).0 is None);
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::Set)) {
        proof {
            reveal(verified_production::token_view);
            assert(r0.len() >= 1);
            assert(r0[0] == verified_production::token_view(toks@[cur as int]));
            assert(r0[0] != verified_production::TokenView::Keyword(Keyword::Set));
            assert(verified_stmt_prec::sparse_control_update(input).0 is None);
        }
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Set),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost al_whole = verified_stmt_prec::sparse_control_assign_list(r1);
    proof {
        verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
        assert(r1 == r0.drop_first());
        assert(r0[0] == verified_production::TokenView::Keyword(Keyword::Set));
    }

    let mut set: BTreeMap<String, Option<ast::Expression>> = BTreeMap::new();
    let ghost mut done: Seq<(String, Option<ast::Expression>)> = Seq::empty();
    proof {
        verified_stmt::axiom_string_obeys_cmp();
        assert(set@ == vstd::map::Map::<String, Option<ast::Expression>>::empty());
    }
    loop
        invariant_except_break
            pos < cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Ident(table),
            r0 == input.drop_first(),
            r0.len() >= 1,
            r0[0] == verified_production::TokenView::Keyword(Keyword::Set),
            r1 == r0.drop_first(),
            al_whole == verified_stmt_prec::sparse_control_assign_list(r1),
            set@.dom().finite(),
            forall|i: int, j: int| 0 <= i < j < done.len() ==> done[i].0 != done[j].0,
            forall|i: int| 0 <= i < done.len() ==> #[trigger] set@.dom().contains(done[i].0)
                && set@[done[i].0] == done[i].1,
            forall|k: String| set@.dom().contains(k)
                ==> exists|i: int| 0 <= i < done.len() && (#[trigger] done[i]).0 == k,
            sized ==> al_whole == verified_stmt_prec::assign_list_prepend(
                verified_stmt::view_assign_pairs(done),
                r1,
                verified_stmt_prec::sparse_control_assign_list(
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
        ensures
            pos < cur,
            cur <= toks.len(),
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Ident(table),
            r0 == input.drop_first(),
            r0[0] == verified_production::TokenView::Keyword(Keyword::Set),
            r1 == r0.drop_first(),
            al_whole == verified_stmt_prec::sparse_control_assign_list(r1),
            set@.dom().finite(),
            forall|i: int, j: int| 0 <= i < j < done.len() ==> done[i].0 != done[j].0,
            forall|i: int| 0 <= i < done.len() ==> #[trigger] set@.dom().contains(done[i].0)
                && set@[done[i].0] == done[i].1,
            forall|k: String| set@.dom().contains(k)
                ==> exists|i: int| 0 <= i < done.len() && (#[trigger] done[i]).0 == k,
            done.len() >= 1,
            sized ==> al_whole == (Some(verified_stmt::view_assign_pairs(done)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_assign_pairs(done);
        if cur >= toks.len() {
            proof {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                if sized {
                    assert(cur_v.len() < 2);
                    reveal_with_fuel(verified_stmt_prec::sparse_control_assign_list, 1);
                    assert(verified_stmt_prec::sparse_control_assign(cur_v).0 is None);
                    assert(verified_stmt_prec::sparse_control_assign_list(cur_v).0 is None);
                    assert(r1 == input.drop_first().drop_first());
                    assert(al_whole == verified_stmt_prec::sparse_control_assign_list(r1));
                    assert(al_whole.0 is None);
                    assert(r1 == input.drop_first().drop_first());
                    assert(verified_stmt_prec::sparse_control_assign_list(
                        input.drop_first().drop_first()).0 is None);
                    verified_stmt_prec::lemma_update_reject_on_list_none(input, table);
                    assert(verified_stmt_prec::sparse_control_update(input).0 is None);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        let column = match &toks[cur] {
            Token::Ident(name) => name.clone(),
            _ => {
                proof {
                    reveal(verified_production::token_view);
                    if sized {
                        assert(cur_v[0] == verified_production::token_view(toks@[cur as int]));
                        assert(match cur_v[0] {
                            verified_production::TokenView::Ident(_) => false,
                            _ => true,
                        });
                        assert(verified_stmt_prec::sparse_control_assign(cur_v).0 is None);
                        assert(verified_stmt_prec::sparse_control_assign_list(cur_v).0 is None);
                        assert(al_whole.0 is None);
                        verified_stmt_prec::lemma_update_reject_on_list_none(input, table);
                    }
                }
                return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone())));
            },
        };
        cur = cur + 1;
        proof { verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int); }

        if cur >= toks.len() {
            proof {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                if sized {
                    assert(cur_v.len() < 2);
                    assert(verified_stmt_prec::sparse_control_assign(cur_v).0 is None);
                    assert(verified_stmt_prec::sparse_control_assign_list(cur_v).0 is None);
                    assert(al_whole.0 is None);
                    verified_stmt_prec::lemma_update_reject_on_list_none(input, table);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Equal) {
            proof {
                reveal(verified_production::token_view);
                if sized {
                    assert(cur_v.len() >= 2);
                    assert(cur_v[1] == verified_production::token_view(toks@[cur as int]));
                    assert(cur_v[1] != verified_production::TokenView::Equal);
                    assert(verified_stmt_prec::sparse_control_assign(cur_v).0 is None);
                    assert(verified_stmt_prec::sparse_control_assign_list(cur_v).0 is None);
                    assert(al_whole.0 is None);
                    verified_stmt_prec::lemma_update_reject_on_list_none(input, table);
                }
            }
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::Equal,
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        let ghost rest_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 2) as int);
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            if sized {
                assert(cur_v.len() >= 2);
                assert(cur_v[0] == verified_production::TokenView::Ident(column));
                assert(cur_v[1] == verified_production::TokenView::Equal);
                assert(rest_v == cur_v.drop_first().drop_first());
            }
        }

        let value: Option<ast::Expression>;
        let ghost r_after_val: Seq<verified_production::TokenView>;
        if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Default)) {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
            cur = cur + 1;
            value = None;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                r_after_val = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
                if sized {
                    assert(rest_v.len() >= 1);
                    assert(rest_v[0] == verified_production::TokenView::Keyword(Keyword::Default));
                    assert(r_after_val == rest_v.drop_first());
                    assert(verified_stmt_prec::sparse_control_assign(cur_v)
                        == (Some((column, None::<SExpr>)), r_after_val));
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
            }
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                assert(!sized);
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            let (opt, consumed, verr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            match opt {
                Some(expr) => {
                    value = Some(expr);
                    proof {
                        r_after_val = verified_production::token_views(
                            toks@.subrange(consumed as int, toks@.len() as int));
                        if sized {
                            assert(!(rest_v.len() >= 1
                                && rest_v[0] == verified_production::TokenView::Keyword(Keyword::Default)));
                            assert(verified_precedence::sparse_prec(rest_v, 0,
                                verified_stmt_prec::expr_fuel(rest_v))
                                == (Some(verified_roundtrip::view_expr(expr)), r_after_val));
                            assert(verified_stmt_prec::sparse_control_assign(cur_v)
                                == (Some((column, Some(verified_roundtrip::view_expr(expr)))), r_after_val));
                        }
                    }
                    cur = consumed;
                },
                None => {
                    proof {
                        if sized {
                            assert(!(rest_v.len() >= 1
                                && rest_v[0] == verified_production::TokenView::Keyword(Keyword::Default)));
                            assert(verified_precedence::sparse_prec(rest_v, 0,
                                verified_stmt_prec::expr_fuel(rest_v)).0 is None);
                            assert(verified_stmt_prec::sparse_control_assign(cur_v).0 is None);
                            assert(verified_stmt_prec::sparse_control_assign_list(cur_v).0 is None);
                            assert(al_whole.0 is None);
                            verified_stmt_prec::lemma_update_reject_on_list_none(input, table);
                        }
                    }
                    return (None, pos, verr);
                },
            }
        }
        let ghost a: (String, Option<SExpr>) = (column, verified_stmt::view_opt(value));
        proof {
            if sized {
                assert(verified_stmt_prec::sparse_control_assign(cur_v) == (Some(a), r_after_val));
            }
        }

        proof { verified_stmt::axiom_string_obeys_cmp(); }
        if set.contains_key(&column) {
            proof {
                verified_stmt::axiom_string_obeys_cmp();
                broadcast use vstd::std_specs::btree::group_btree_axioms;
                assert(set@.contains_key(column));
                if sized {
                    let di = choose|i: int| 0 <= i < done.len() && (#[trigger] done[i]).0 == column;
                    assert(done[di].0 == column);
                    verified_stmt::view_assign_pairs_index(done);
                    assert(done_v[di].0 == done[di].0);
                    assert(a.0 == column);
                    verified_stmt_prec::lemma_update_reject_on_duplicate(
                        input, table, cur_v, a, r_after_val, done_v, di);
                }
            }
            return (None, pos, Some(ParseError::DuplicateColumn(column.clone())));
        }
        proof {
            verified_stmt::axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert(!set@.contains_key(column));
        }
        let ghost old_set = set@;
        let ghost old_done = done;
        set.insert(column, value);
        proof {
            done = old_done + seq![(column, value)];
            verified_stmt::axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert(set@ == old_set.insert(column, value));
            assert(forall|i: int, j: int| 0 <= i < j < done.len() ==> done[i].0 != done[j].0) by {
                assert forall|i: int, j: int| 0 <= i < j < done.len() implies done[i].0 != done[j].0 by {
                    if j < old_done.len() {
                    } else {
                        assert(j == old_done.len());
                        assert(done[j].0 == column);
                        assert(done[i] == old_done[i]);
                        assert(old_set.dom().contains(old_done[i].0));
                        assert(!old_set.dom().contains(column));
                    }
                }
            }
            assert forall|i: int| 0 <= i < done.len() implies #[trigger] set@.dom().contains(done[i].0)
                && set@[done[i].0] == done[i].1 by {
                if i < old_done.len() {
                    assert(done[i] == old_done[i]);
                    assert(old_done[i].0 != column) by {
                        assert(old_set.dom().contains(old_done[i].0));
                    }
                } else {
                    assert(done[i] == (column, value));
                }
            }
            assert forall|k: String| set@.dom().contains(k) implies
                exists|i: int| 0 <= i < done.len() && (#[trigger] done[i]).0 == k by {
                if k == column {
                    assert(done[old_done.len() as int].0 == column);
                } else {
                    assert(old_set.dom().contains(k));
                    let oi = choose|i: int| 0 <= i < old_done.len() && (#[trigger] old_done[i]).0 == k;
                    assert(done[oi] == old_done[oi]);
                }
            }
            verified_stmt::view_assign_pairs_index(done);
            verified_stmt::view_assign_pairs_index(old_done);
            assert(verified_stmt::view_assign_pairs(done)
                =~= verified_stmt::view_assign_pairs(old_done) + seq![a]);
        }

        let ghost r_before_comma = r_after_val;
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    assert(r_after_val == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(r_after_val.len() >= 1);
                    assert(r_after_val[0] == verified_production::TokenView::Comma);
                    verified_stmt_prec::lemma_assign_list_step(cur_v, a, r_after_val);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_before_comma.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    verified_stmt_prec::lemma_assign_list_resume_step(
                        r1, cur_v, r_before_comma.drop_first(),
                        done_v, a, al_whole);
                    assert(verified_stmt::view_assign_pairs(done) == done_v + seq![a]);
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    assert(r_after_val == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    assert(!(r_after_val.len() >= 1 && r_after_val[0] == verified_production::TokenView::Comma));
                    verified_stmt_prec::lemma_assign_list_last(cur_v, a, r_after_val);
                    assert(verified_stmt_prec::sparse_control_assign_list(cur_v) == (Some(seq![a]), r_after_val));
                    assert(al_whole == (Some(done_v + seq![a]), r_after_val));
                    assert(verified_stmt::view_assign_pairs(done) == done_v + seq![a]);
                }
            }
            break;
        }
    }

    let ghost items_v = verified_stmt::view_assign_pairs(done);
    let ghost al_rest = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            assert(al_whole == (Some(items_v), al_rest));
            verified_stmt::view_assign_pairs_index(done);
            assert(verified_stmt_prec::assign_keys_distinct(items_v)) by {
                assert forall|i: int, j: int| 0 <= i < j < items_v.len()
                    implies items_v[i].0 != items_v[j].0 by {
                    assert(items_v[i].0 == done[i].0);
                    assert(items_v[j].0 == done[j].0);
                }
            }
        }
    }

    let mut where_clause: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        let ghost we_in = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            if sized {
                assert(al_rest.len() >= 1);
                assert(al_rest[0] == verified_production::TokenView::Keyword(Keyword::Where));
                assert(we_in == al_rest.drop_first());
            }
        }
        let n = toks.len() - cur;
        if n > (usize::MAX - 3) / 2 {
            assert(!sized);
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        let fuel = 2 * n + 3;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, consumed, werr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
        match opt {
            Some(expr) => {
                where_clause = Some(expr);
                proof {
                    if sized {
                        assert(verified_precedence::sparse_prec(we_in, 0,
                            verified_stmt_prec::expr_fuel(we_in))
                            == (Some(verified_roundtrip::view_expr(expr)),
                                verified_production::token_views(
                                    toks@.subrange(consumed as int, toks@.len() as int))));
                    }
                }
                cur = consumed;
            },
            None => {
                proof {
                    if sized {
                        assert(verified_precedence::sparse_prec(we_in, 0,
                            verified_stmt_prec::expr_fuel(we_in)).0 is None);
                        assert(al_whole == (Some(items_v), al_rest));
                        assert(we_in == al_rest.drop_first());
                        verified_stmt_prec::lemma_update_reject_on_where_none(
                            input, table, items_v, al_rest);
                    }
                }
                return (None, pos, werr);
            },
        }
        let ghost we = verified_roundtrip::view_expr(where_clause->0);
        proof {
            if sized {
                verified_stmt::lemma_update_view_boundary(table, set@, done, where_clause);
                verified_stmt::view_assign_pairs_index(done);
                assert(verified_stmt::view_opt(where_clause) == Some(we));
                assert(verified_stmt_prec::sparse_control_update(input)
                    == (Some(verified_stmt_prec::assign_list_to_sstmt(table, items_v, Some(we))),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))));
                assert(verified_stmt::view_update_arm(table, set@, where_clause)
                    == verified_stmt_prec::assign_list_to_sstmt(table, items_v, Some(we))) by {
                    if done.len() == 1 {
                        assert(items_v[0] == (done[0].0, verified_stmt::view_opt(done[0].1)));
                    }
                }
            }
        }
        return (Some(ast::Statement::Update { table, set, where_clause }), cur, None);
    }

    proof {
        if sized {
            if cur < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
            }
            assert(al_rest == verified_production::token_views(
                toks@.subrange(cur as int, toks@.len() as int)));
            assert(!(al_rest.len() >= 1
                && al_rest[0] == verified_production::TokenView::Keyword(Keyword::Where)));
            verified_stmt::lemma_update_view_boundary(table, set@, done, where_clause);
            verified_stmt::view_assign_pairs_index(done);
            assert(where_clause is None);
            assert(verified_stmt::view_opt(where_clause) == None::<SExpr>);
            assert(verified_stmt_prec::sparse_control_update(input)
                == (Some(verified_stmt_prec::assign_list_to_sstmt(table, items_v, None)), al_rest));
            assert(verified_stmt::view_update_arm(table, set@, where_clause)
                == verified_stmt_prec::assign_list_to_sstmt(table, items_v, None)) by {
                if done.len() == 1 {
                    assert(items_v[0] == (done[0].0, verified_stmt::view_opt(done[0].1)));
                }
            }
        }
    }
    (Some(ast::Statement::Update { table, set, where_clause }), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200000)]
fn parse_insert_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_insert(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    let ghost sized = toks.len() <= (usize::MAX - 3) / 2;
    if pos >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], Token::Keyword(Keyword::Into)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Into),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;
    let ghost r0 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        assert(r0 == input.drop_first());
    }

    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    let table = match &toks[cur] {
        Token::Ident(name) => name.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    cur = cur + 1;
    let ghost r1 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
        assert(r1 == r0.drop_first());
        assert(r0[0] == verified_production::TokenView::Ident(table));
    }

    let mut columns: Option<Vec<String>> = None;
    if cur < toks.len() && matches!(toks[cur], Token::OpenParen) {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        let ghost cl_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost cl_whole = verified_stmt_prec::sparse_control_ident_list(cl_start);
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r1.len() >= 1);
            assert(r1[0] == verified_production::TokenView::OpenParen);
            assert(cl_start == r1.drop_first());
        }
        let mut cols: Vec<String> = Vec::new();
        loop
            invariant_except_break
                pos < cur,
                cur <= toks.len(),
                input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
                input.len() >= 1,
                input[0] == verified_production::TokenView::Keyword(Keyword::Into),
                r0 == input.drop_first(),
                r0.len() >= 1,
                r0[0] == verified_production::TokenView::Ident(table),
                r1 == r0.drop_first(),
                r1.len() >= 1,
                r1[0] == verified_production::TokenView::OpenParen,
                cl_start == r1.drop_first(),
                cl_whole == verified_stmt_prec::sparse_control_ident_list(cl_start),
                cl_whole == verified_stmt_prec::ident_list_prepend(
                    cols@,
                    cl_start,
                    verified_stmt_prec::sparse_control_ident_list(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
            ensures
                pos < cur,
                cur <= toks.len(),
                cl_whole == verified_stmt_prec::sparse_control_ident_list(cl_start),
                cl_whole == (Some(cols@),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
            decreases toks.len() - cur,
        {
            let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
            let ghost done_v = cols@;
            if cur >= toks.len() {
                proof {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                    assert(verified_stmt_prec::sparse_control_ident_list(cur_v).0 is None);
                    assert(cl_whole.0 is None);
                    assert(verified_stmt_prec::sparse_control_opt_columns(r1).is_none());
                    insert_conclude_none_cols(input, r0, r1, cl_start, table);
                }
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
            let name = match &toks[cur] {
                Token::Ident(name) => name.clone(),
                _ => {
                    proof {
                        assert(verified_stmt_prec::sparse_control_ident_list(cur_v).0 is None);
                        assert(cl_whole.0 is None);
                        assert(verified_stmt_prec::sparse_control_opt_columns(r1).is_none());
                        insert_conclude_none_cols(input, r0, r1, cl_start, table);
                    }
                    return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone())));
                },
            };
            proof { assert(cur_v[0] == verified_production::TokenView::Ident(name)); }
            let ghost r_after_name = verified_production::token_views(toks@.subrange((cur + 1) as int, toks@.len() as int));
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                assert(r_after_name == cur_v.drop_first());
            }
            let ghost old_cols = cols@;
            cols.push(name);
            cur = cur + 1;
            proof {
                assert(cols@ == old_cols + seq![name]);
            }
            if cur < toks.len() && matches!(toks[cur], Token::Comma) {
                proof {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                    verified_stmt_prec::lemma_ident_list_step(cur_v, name, r_after_name);
                }
                cur = cur + 1;
                proof {
                    verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                    assert(r_after_name.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    verified_stmt_prec::lemma_ident_list_resume_step(
                        cl_start, cur_v, r_after_name.drop_first(), done_v, name, cl_whole);
                    assert(cols@ == done_v + seq![name]);
                }
            } else {
                proof {
                    if cur < toks.len() {
                        verified_roundtrip::token_views_suffix(toks@, cur as int);
                    } else {
                        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                    }
                    verified_stmt_prec::lemma_ident_list_last(cur_v, name, r_after_name);
                    assert(verified_stmt_prec::sparse_control_ident_list(cur_v)
                        == (Some(seq![name]), r_after_name));
                    assert(cl_whole == (Some(done_v + seq![name]), r_after_name));
                    assert(cols@ == done_v + seq![name]);
                }
                break;
            }
        }
        let ghost rc = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        if cur >= toks.len() {
            proof {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                assert(rc.len() == 0);
                assert(cl_whole == (Some(cols@), rc));
                assert(verified_stmt_prec::sparse_control_opt_columns(r1).is_none());
                insert_conclude_none_cols(input, r0, r1, cl_start, table);
            }
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::CloseParen) {
            proof {
                assert(rc[0] != verified_production::TokenView::CloseParen);
                assert(cl_whole == (Some(cols@), rc));
                assert(verified_stmt_prec::sparse_control_opt_columns(r1).is_none());
                insert_conclude_none_cols(input, r0, r1, cl_start, table);
            }
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::CloseParen,
                toks[cur].clone(),
            )));
        }
        proof { assert(rc[0] == verified_production::TokenView::CloseParen); }
        cur = cur + 1;
        columns = Some(cols);
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(cl_start == r1.drop_first());
            assert(verified_stmt_prec::sparse_control_ident_list(r1.drop_first()) == cl_whole);
            assert(rc == cl_whole.1);
            assert(verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))
                == rc.drop_first());
            assert(verified_stmt_prec::sparse_control_opt_columns(r1)
                == Some((Some(cols@),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))));
        }
    } else {
        proof {
            if cur < toks.len() {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
            } else {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
            }
            assert(verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)) == r1);
            assert(!(r1.len() >= 1 && r1[0] == verified_production::TokenView::OpenParen));
            assert(verified_stmt_prec::sparse_control_opt_columns(r1)
                == Some((None::<Seq<String>>,
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))));
        }
    }
    let ghost r2 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost cols_view: Option<Seq<String>> = match columns {
        Some(ref v) => Some(v@),
        None => None,
    };
    proof {
        assert(verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)));
    }

    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    if !matches!(toks[cur], Token::Keyword(Keyword::Values)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Values),
            toks[cur].clone(),
        )));
    }
    cur = cur + 1;
    let ghost vals_start = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost vals_whole = verified_stmt_prec::sparse_control_values(vals_start);
    proof {
        verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
        assert(vals_start == r2.drop_first());
        reveal_with_fuel(verified_stmt::view_rows, 1);
        assert(verified_stmt::view_rows(Seq::<Vec<ast::Expression>>::empty())
            == Seq::<Seq<verified_roundtrip::SExpr>>::empty());
        match vals_whole.0 {
            Some(m) => { assert(Seq::<Seq<verified_roundtrip::SExpr>>::empty() + m == m); },
            None => {},
        }
    }

    let mut values: Vec<Vec<ast::Expression>> = Vec::new();
    loop
        invariant_except_break
            pos < cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Keyword(Keyword::Into),
            r0 == input.drop_first(),
            r0.len() >= 1,
            r0[0] == verified_production::TokenView::Ident(table),
            r1 == r0.drop_first(),
            verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
            r2.len() >= 1,
            r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
            vals_start == r2.drop_first(),
            vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
            sized ==>
                vals_whole == verified_stmt_prec::values_prepend(
                    verified_stmt::view_rows(values@),
                    vals_start,
                    verified_stmt_prec::sparse_control_values(
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
        ensures
            pos < cur,
            cur <= toks.len(),
            sized == (toks.len() <= (usize::MAX - 3) / 2),
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            input.len() >= 1,
            input[0] == verified_production::TokenView::Keyword(Keyword::Into),
            r0 == input.drop_first(),
            r0.len() >= 1,
            r0[0] == verified_production::TokenView::Ident(table),
            r1 == r0.drop_first(),
            verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
            r2.len() >= 1,
            r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
            vals_start == r2.drop_first(),
            vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
            sized ==>
                vals_whole == (Some(verified_stmt::view_rows(values@)),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let ghost cur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost done_v = verified_stmt::view_rows(values@);
        if cur >= toks.len() {
            proof {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                reveal_with_fuel(verified_stmt_prec::sparse_control_values, 1);
                assert(verified_stmt_prec::sparse_control_row(cur_v).0 is None);
                assert(verified_stmt_prec::sparse_control_values(cur_v).0 is None);
                if sized {
                    assert(vals_whole.0 is None);
                    insert_conclude_none(input, r0, r1, r2, vals_start, vals_whole, table, cols_view);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::OpenParen) {
            proof {
                reveal_with_fuel(verified_stmt_prec::sparse_control_values, 1);
                assert(cur_v[0] != verified_production::TokenView::OpenParen);
                assert(verified_stmt_prec::sparse_control_row(cur_v).0 is None);
                assert(verified_stmt_prec::sparse_control_values(cur_v).0 is None);
                if sized {
                    assert(vals_whole.0 is None);
                    insert_conclude_none(input, r0, r1, r2, vals_start, vals_whole, table, cols_view);
                }
            }
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::OpenParen,
                toks[cur].clone(),
            )));
        }
        proof { assert(cur_v[0] == verified_production::TokenView::OpenParen); }
        let ghost cur_v_outer = cur_v;
        let ghost done_v_outer = done_v;
        cur = cur + 1;
        let ghost row_start = cur;
        let ghost rstart_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost row_whole = verified_stmt_prec::sparse_control_group_list(rstart_v);
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(rstart_v == cur_v.drop_first());
        }
        let mut row: Vec<ast::Expression> = Vec::new();
        loop
            invariant_except_break
                pos < row_start <= cur,
                cur <= toks.len(),
                sized == (toks.len() <= (usize::MAX - 3) / 2),
                cur_v_outer.len() >= 1,
                cur_v_outer[0] == verified_production::TokenView::OpenParen,
                rstart_v == cur_v_outer.drop_first(),
                rstart_v == verified_production::token_views(
                    toks@.subrange(row_start as int, toks@.len() as int)),
                row_whole == verified_stmt_prec::sparse_control_group_list(rstart_v),
                input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
                input.len() >= 1,
                input[0] == verified_production::TokenView::Keyword(Keyword::Into),
                r0 == input.drop_first(),
                r0.len() >= 1,
                r0[0] == verified_production::TokenView::Ident(table),
                r1 == r0.drop_first(),
                verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
                r2.len() >= 1,
                r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
                vals_start == r2.drop_first(),
                vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
                sized ==>
                    vals_whole == verified_stmt_prec::values_prepend(
                        done_v_outer, vals_start,
                        verified_stmt_prec::sparse_control_values(cur_v_outer)),
                sized ==>
                    row_whole == verified_stmt_prec::group_list_prepend(
                        verified_roundtrip::view_args(row@),
                        rstart_v,
                        verified_stmt_prec::sparse_control_group_list(
                            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)))),
            ensures
                pos < row_start <= cur,
                cur <= toks.len(),
                sized == (toks.len() <= (usize::MAX - 3) / 2),
                cur_v_outer.len() >= 1,
                cur_v_outer[0] == verified_production::TokenView::OpenParen,
                rstart_v == cur_v_outer.drop_first(),
                rstart_v == verified_production::token_views(
                    toks@.subrange(row_start as int, toks@.len() as int)),
                row_whole == verified_stmt_prec::sparse_control_group_list(rstart_v),
                input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
                input.len() >= 1,
                input[0] == verified_production::TokenView::Keyword(Keyword::Into),
                r0 == input.drop_first(),
                r0.len() >= 1,
                r0[0] == verified_production::TokenView::Ident(table),
                r1 == r0.drop_first(),
                verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
                r2.len() >= 1,
                r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
                vals_start == r2.drop_first(),
                vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
                cur_v_outer.len() >= 1,
                cur_v_outer[0] == verified_production::TokenView::OpenParen,
                rstart_v == cur_v_outer.drop_first(),
                sized ==>
                    vals_whole == verified_stmt_prec::values_prepend(
                        done_v_outer, vals_start,
                        verified_stmt_prec::sparse_control_values(cur_v_outer)),
                sized ==>
                    row_whole == (Some(verified_roundtrip::view_args(row@)),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
            decreases toks.len() - cur,
        {
            let ghost rcur_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
            let ghost rdone_v = verified_roundtrip::view_args(row@);
            let n = toks.len() - cur;
            if n > (usize::MAX - 3) / 2 {
                return (None, pos, Some(ParseError::UnexpectedEof));
            }
            let fuel = 2 * n + 3;
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
            let (opt, consumed, verr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
            let expr = match opt {
                Some(e) => e,
                None => {
                    proof {
                        reveal_with_fuel(verified_stmt_prec::sparse_control_group_list, 1);
                        assert(verified_precedence::sparse_prec(rcur_v, 0, fuel as nat).0 is None);
                        assert(verified_stmt_prec::sparse_control_group_list(rcur_v).0 is None);
                        if sized {
                            assert(row_whole.0 is None);
                            insert_row_whole_reject(rstart_v, cur_v_outer, row_whole);
                            reveal_with_fuel(verified_stmt_prec::sparse_control_values, 1);
                            assert(verified_stmt_prec::sparse_control_values(cur_v_outer).0 is None);
                            assert(vals_whole.0 is None);
                            insert_conclude_none(input, r0, r1, r2, vals_start, vals_whole, table, cols_view);
                        }
                    }
                    return (None, pos, verr);
                },
            };
            let ghost r_after_expr = verified_production::token_views(toks@.subrange(consumed as int, toks@.len() as int));
            proof {
                assert(fuel as nat == verified_stmt_prec::expr_fuel(rcur_v));
                assert(verified_precedence::sparse_prec(rcur_v, 0, verified_stmt_prec::expr_fuel(rcur_v))
                    == (Some(verified_roundtrip::view_expr(expr)), r_after_expr));
            }
            let ghost old_row = row@;
            row.push(expr);
            cur = consumed;
            proof {
                verified_stmt_prec::lemma_view_args_append(old_row, seq![expr]);
                verified_stmt_prec::lemma_view_args_single(expr);
                assert(row@ == old_row + seq![expr]);
                assert(verified_roundtrip::view_args(row@)
                    == rdone_v + seq![verified_roundtrip::view_expr(expr)]);
            }
            if cur < toks.len() && matches!(toks[cur], Token::Comma) {
                proof {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                    if sized {
                        verified_stmt_prec::lemma_group_list_step(
                            rcur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                    }
                }
                cur = cur + 1;
                proof {
                    verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                    assert(r_after_expr.drop_first() == verified_production::token_views(
                        toks@.subrange(cur as int, toks@.len() as int)));
                    if sized {
                        verified_stmt_prec::lemma_group_list_resume_step(
                            rstart_v, rcur_v, r_after_expr.drop_first(),
                            rdone_v, verified_roundtrip::view_expr(expr), row_whole);
                        assert(verified_roundtrip::view_args(row@)
                            == rdone_v + seq![verified_roundtrip::view_expr(expr)]);
                    }
                }
            } else {
                proof {
                    if cur < toks.len() {
                        verified_roundtrip::token_views_suffix(toks@, cur as int);
                    } else {
                        verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                    }
                    if sized {
                        verified_stmt_prec::lemma_group_list_last(
                            rcur_v, verified_roundtrip::view_expr(expr), r_after_expr);
                        assert(verified_stmt_prec::sparse_control_group_list(rcur_v)
                            == (Some(seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                        assert(row_whole == (Some(rdone_v
                            + seq![verified_roundtrip::view_expr(expr)]), r_after_expr));
                        assert(verified_roundtrip::view_args(row@)
                            == rdone_v + seq![verified_roundtrip::view_expr(expr)]);
                    }
                }
                break;
            }
        }
        let ghost r_after_row_exprs = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        if cur >= toks.len() {
            proof {
                verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                assert(r_after_row_exprs.len() == 0);
                if sized {
                    insert_row_reject(rstart_v, cur_v_outer, verified_roundtrip::view_args(row@), r_after_row_exprs);
                    assert(verified_stmt_prec::sparse_control_row(cur_v_outer).0 is None);
                    reveal_with_fuel(verified_stmt_prec::sparse_control_values, 1);
                    assert(verified_stmt_prec::sparse_control_values(cur_v_outer).0 is None);
                    assert(vals_whole.0 is None);
                    insert_conclude_none(input, r0, r1, r2, vals_start, vals_whole, table, cols_view);
                }
            }
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::CloseParen) {
            proof {
                assert(r_after_row_exprs[0] != verified_production::TokenView::CloseParen);
                if sized {
                    insert_row_reject(rstart_v, cur_v_outer, verified_roundtrip::view_args(row@), r_after_row_exprs);
                    assert(verified_stmt_prec::sparse_control_row(cur_v_outer).0 is None);
                    reveal_with_fuel(verified_stmt_prec::sparse_control_values, 1);
                    assert(verified_stmt_prec::sparse_control_values(cur_v_outer).0 is None);
                    assert(vals_whole.0 is None);
                    insert_conclude_none(input, r0, r1, r2, vals_start, vals_whole, table, cols_view);
                }
            }
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::CloseParen,
                toks[cur].clone(),
            )));
        }
        proof { assert(r_after_row_exprs[0] == verified_production::TokenView::CloseParen); }
        cur = cur + 1;
        let ghost old_values = values@;
        values.push(row);
        let ghost r_after_row = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
        let ghost row_view = verified_roundtrip::view_args(row@);
        proof {
            verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
            assert(r_after_row == r_after_row_exprs.drop_first());
            verified_stmt_prec::lemma_view_rows_append(old_values, seq![row]);
            verified_stmt_prec::lemma_view_rows_single(row);
            assert(values@ == old_values + seq![row]);
            assert(verified_stmt::view_rows(values@)
                == done_v + seq![row_view]);
            if sized {
                insert_row_accept(rstart_v, cur_v_outer, row_view, r_after_row_exprs, r_after_row);
            }
        }
        if cur < toks.len() && matches!(toks[cur], Token::Comma) {
            proof {
                verified_roundtrip::token_views_suffix(toks@, cur as int);
                if sized {
                    verified_stmt_prec::lemma_values_step(cur_v_outer, row_view, r_after_row);
                }
            }
            cur = cur + 1;
            proof {
                verified_roundtrip::token_views_suffix(toks@, (cur - 1) as int);
                assert(r_after_row.drop_first() == verified_production::token_views(
                    toks@.subrange(cur as int, toks@.len() as int)));
                if sized {
                    verified_stmt_prec::lemma_values_resume_step(
                        vals_start, cur_v_outer, r_after_row.drop_first(),
                        done_v, row_view, vals_whole);
                    assert(verified_stmt::view_rows(values@) == done_v + seq![row_view]);
                }
            }
        } else {
            proof {
                if cur < toks.len() {
                    verified_roundtrip::token_views_suffix(toks@, cur as int);
                } else {
                    verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                }
                if sized {
                    verified_stmt_prec::lemma_values_last(cur_v_outer, row_view, r_after_row);
                    assert(verified_stmt_prec::sparse_control_values(cur_v_outer)
                        == (Some(seq![row_view]), r_after_row));
                    assert(vals_whole == (Some(done_v + seq![row_view]), r_after_row));
                    assert(verified_stmt::view_rows(values@) == done_v + seq![row_view]);
                }
            }
            break;
        }
    }
    let ghost r3 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    proof {
        if sized {
            insert_conclude(toks, pos, cur, input, r0, r1, r2, vals_start, vals_whole,
                table, cols_view, verified_stmt::view_rows(values@));
            assert(cols_view == match columns {
                Some(ref v) => Some(v@),
                None => None::<Seq<String>>,
            });
            assert(verified_stmt::view_stmt(ast::Statement::Insert { table, columns, values })
                == verified_stmt::SStmt::Insert {
                    table,
                    columns: cols_view,
                    values: verified_stmt::view_rows(values@),
                });
        }
    }
    (Some(ast::Statement::Insert { table, columns, values }), cur, None)
}

proof fn insert_row_whole_reject(
    rstart_v: Seq<verified_production::TokenView>,
    cur_v: Seq<verified_production::TokenView>,
    row_whole: (Option<Seq<verified_roundtrip::SExpr>>, Seq<verified_production::TokenView>),
)
    requires
        cur_v.len() >= 1,
        cur_v[0] == verified_production::TokenView::OpenParen,
        rstart_v == cur_v.drop_first(),
        row_whole == verified_stmt_prec::sparse_control_group_list(rstart_v),
        row_whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_row(cur_v).0 is None,
{
}

proof fn insert_row_reject(
    rstart_v: Seq<verified_production::TokenView>,
    cur_v: Seq<verified_production::TokenView>,
    exprs: Seq<verified_roundtrip::SExpr>,
    r: Seq<verified_production::TokenView>,
)
    requires
        cur_v.len() >= 1,
        cur_v[0] == verified_production::TokenView::OpenParen,
        rstart_v == cur_v.drop_first(),
        verified_stmt_prec::sparse_control_group_list(rstart_v) == (Some(exprs), r),
        !(r.len() >= 1 && r[0] == verified_production::TokenView::CloseParen),
    ensures
        verified_stmt_prec::sparse_control_row(cur_v).0 is None,
{
}

proof fn insert_row_accept(
    rstart_v: Seq<verified_production::TokenView>,
    cur_v: Seq<verified_production::TokenView>,
    exprs: Seq<verified_roundtrip::SExpr>,
    r: Seq<verified_production::TokenView>,
    r_next: Seq<verified_production::TokenView>,
)
    requires
        cur_v.len() >= 1,
        cur_v[0] == verified_production::TokenView::OpenParen,
        rstart_v == cur_v.drop_first(),
        verified_stmt_prec::sparse_control_group_list(rstart_v) == (Some(exprs), r),
        r.len() >= 1,
        r[0] == verified_production::TokenView::CloseParen,
        r_next == r.drop_first(),
    ensures
        verified_stmt_prec::sparse_control_row(cur_v) == (Some(exprs), r_next),
{
}

proof fn insert_conclude(
    toks: &Vec<Token>,
    pos: usize,
    cur: usize,
    input: Seq<verified_production::TokenView>,
    r0: Seq<verified_production::TokenView>,
    r1: Seq<verified_production::TokenView>,
    r2: Seq<verified_production::TokenView>,
    vals_start: Seq<verified_production::TokenView>,
    vals_whole: (Option<Seq<Seq<verified_roundtrip::SExpr>>>, Seq<verified_production::TokenView>),
    table: String,
    cols_view: Option<Seq<String>>,
    rows: Seq<Seq<verified_roundtrip::SExpr>>,
)
    requires
        pos < cur <= toks.len(),
        input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
        input.len() >= 1,
        input[0] == verified_production::TokenView::Keyword(Keyword::Into),
        r0 == input.drop_first(),
        r0.len() >= 1,
        r0[0] == verified_production::TokenView::Ident(table),
        r1 == r0.drop_first(),
        verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
        r2.len() >= 1,
        r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
        vals_start == r2.drop_first(),
        vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
        vals_whole == (Some(rows),
            verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
    ensures
        verified_stmt_prec::sparse_control_insert(input)
            == (Some(verified_stmt::SStmt::Insert { table, columns: cols_view, values: rows }),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
{
}

proof fn insert_conclude_none_cols(
    input: Seq<verified_production::TokenView>,
    r0: Seq<verified_production::TokenView>,
    r1: Seq<verified_production::TokenView>,
    cl_start: Seq<verified_production::TokenView>,
    table: String,
)
    requires
        input.len() >= 1,
        input[0] == verified_production::TokenView::Keyword(Keyword::Into),
        r0 == input.drop_first(),
        r0.len() >= 1,
        r0[0] == verified_production::TokenView::Ident(table),
        r1 == r0.drop_first(),
        verified_stmt_prec::sparse_control_opt_columns(r1).is_none(),
    ensures
        verified_stmt_prec::sparse_control_insert(input).0 is None,
{
}

proof fn insert_conclude_none(
    input: Seq<verified_production::TokenView>,
    r0: Seq<verified_production::TokenView>,
    r1: Seq<verified_production::TokenView>,
    r2: Seq<verified_production::TokenView>,
    vals_start: Seq<verified_production::TokenView>,
    vals_whole: (Option<Seq<Seq<verified_roundtrip::SExpr>>>, Seq<verified_production::TokenView>),
    table: String,
    cols_view: Option<Seq<String>>,
)
    requires
        input.len() >= 1,
        input[0] == verified_production::TokenView::Keyword(Keyword::Into),
        r0 == input.drop_first(),
        r0.len() >= 1,
        r0[0] == verified_production::TokenView::Ident(table),
        r1 == r0.drop_first(),
        verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)),
        r2.len() >= 1,
        r2[0] == verified_production::TokenView::Keyword(Keyword::Values),
        vals_start == r2.drop_first(),
        vals_whole == verified_stmt_prec::sparse_control_values(vals_start),
        vals_whole.0 is None,
    ensures
        verified_stmt_prec::sparse_control_insert(input).0 is None,
{
    assert(verified_stmt_prec::sparse_control_opt_columns(r1) == Some((cols_view, r2)));
    assert(verified_stmt_prec::sparse_control_values(r2.drop_first()) == vals_whole);
    assert(verified_stmt_prec::sparse_control_insert(input)
        == (None::<verified_stmt::SStmt>, input));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
fn parse_delete_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        toks.len() <= (usize::MAX - 3) / 2 ==> ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_delete(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    if pos >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], Token::Keyword(Keyword::From)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::From),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    if cur >= toks.len() {
        proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    let table = match &toks[cur] {
        Token::Ident(name) => name.clone(),
        _ => return (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    };
    cur = cur + 1;

    let ghost r_spec = input.drop_first().drop_first();
    proof {
        verified_roundtrip::token_views_suffix(toks@, pos as int);
        verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int);
        assert(r_spec == verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)));
    }

    let mut where_clause: Option<ast::Expression> = None;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Where)) {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        let n = toks.len() - cur;
        if n > (usize::MAX - 3) / 2 {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        let fuel = 2 * n + 3;
        proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        let (opt, consumed, werr) = verified_precedence::parse_expression_at(toks, cur, 0, fuel);
        match opt {
            Some(expr) => {
                where_clause = Some(expr);
                cur = consumed;
            },
            None => return (None, pos, werr),
        }
    } else {
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        } else {
            proof { verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int)); }
        }
    }

    (Some(ast::Statement::Delete { table, where_clause }), cur, None)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
fn parse_drop_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_drop(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    if pos >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
    if !matches!(toks[pos], Token::Keyword(Keyword::Table)) {
        return (None, pos, Some(ParseError::ExpectedToken(
            Token::Keyword(Keyword::Table),
            toks[pos].clone(),
        )));
    }
    let mut cur = pos + 1;

    let mut if_exists = false;
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::If)) {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); verified_roundtrip::token_views_suffix(toks@, cur as int); }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); verified_roundtrip::token_views_suffix(toks@, (pos + 1) as int); verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Exists)) {
            return (None, pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Exists),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if_exists = true;
    } else {
        proof { verified_roundtrip::token_views_suffix(toks@, pos as int); }
        if cur < toks.len() {
            proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        }
    }

    if cur >= toks.len() {
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    match &toks[cur] {
        Token::Ident(name) => (
            Some(ast::Statement::DropTable { name: name.clone(), if_exists }),
            cur + 1,
            None,
        ),
        _ => (None, pos, Some(ParseError::ExpectedIdent(toks[cur].clone()))),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80000)]
fn parse_begin_at(toks: &Vec<Token>, pos: usize) -> (r: (Option<ast::Statement>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = verified_stmt_prec::sparse_control_begin(input);
            match r.0 {
                Some(s) => sopt is Some
                    && verified_stmt::view_stmt(s) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    proof { verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int)); }
    let begin_pos = pos;
    let mut cur = pos;

    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Transaction)) {
        cur = cur + 1;
    }
    let ghost r0 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));

    let mut read_only = false;
    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::Read)) {
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        match &toks[cur] {
            Token::Keyword(Keyword::Only) => {
                read_only = true;
                cur = cur + 1;
            },
            Token::Keyword(Keyword::Write) => {
                cur = cur + 1;
            },
            _ => return (None, begin_pos, Some(ParseError::UnexpectedToken(toks[cur].clone()))),
        }
    }
    let ghost r2 = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));

    let mut as_of: Option<u64> = None;
    if cur < toks.len() {
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
    }
    if cur < toks.len() && matches!(toks[cur], Token::Keyword(Keyword::As)) {
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Of)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Of),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::System)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::System),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        if !matches!(toks[cur], Token::Keyword(Keyword::Time)) {
            return (None, begin_pos, Some(ParseError::ExpectedToken(
                Token::Keyword(Keyword::Time),
                toks[cur].clone(),
            )));
        }
        cur = cur + 1;
        if cur >= toks.len() {
            return (None, begin_pos, Some(ParseError::UnexpectedEof));
        }
        proof { verified_roundtrip::token_views_suffix(toks@, cur as int); }
        match &toks[cur] {
            Token::Number(n) => match verified_integer::parse_u64(n.as_slice()) {
                Some(version) => {
                    as_of = Some(version);
                    cur = cur + 1;
                },
                None => return (None, begin_pos, Some(ParseError::InvalidSystemTime(n.clone()))),
            },
            _ => return (None, begin_pos, Some(ParseError::WantedNumber(toks[cur].clone()))),
        }
    }

    (Some(ast::Statement::Begin { read_only, as_of }), cur, None)
}

}
