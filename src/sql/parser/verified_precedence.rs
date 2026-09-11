//! Verified expression parser (precedence climbing).
//!
//! The exec `parse_expression_at` is fully functionally refined against the
//! `sparse_prec` spec: accept produces the matching AST and residual position,
//! reject agrees with the spec.
//!
//! Limit: `sparse_prec` is a same-author spec twin, so this pins exec/spec
//! agreement, not conformance to SQL's precedence rules per se (see
//! `verified_minparen` for the precedence-table caveat).

#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::parse_error::ParseError;
#[allow(unused_imports)]
use super::verified_expression::{BinaryTag, UnaryTag};
#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::{
    IsLit, SExpr, binary_tag_exec, build_binary, build_unary, parse_literal_exec, prefix_op_exec,
};
#[allow(unused_imports)]
use super::{
    Keyword, Token, ast, float_trust, verified_expression, verified_integer, verified_production,
};

verus! {



pub open spec fn binary_prec_s(tag: BinaryTag) -> u8 {
    match tag {
        BinaryTag::Or => 1,
        BinaryTag::And => 2,
        BinaryTag::Equal => 4,
        BinaryTag::NotEqual => 4,
        BinaryTag::Like => 4,
        BinaryTag::GreaterThan => 5,
        BinaryTag::GreaterThanOrEqual => 5,
        BinaryTag::LessThan => 5,
        BinaryTag::LessThanOrEqual => 5,
        BinaryTag::Add => 6,
        BinaryTag::Subtract => 6,
        BinaryTag::Multiply => 7,
        BinaryTag::Divide => 7,
        BinaryTag::Remainder => 7,
        BinaryTag::Exponentiate => 8,
    }
}

pub open spec fn binary_assoc_s(tag: BinaryTag) -> u8 {
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

pub open spec fn prefix_prec_s(tag: UnaryTag) -> u8 {
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity => 10,
        UnaryTag::Negate => 10,
    }
}

pub fn binary_prec(tag: BinaryTag) -> (r: u8)
    ensures 1 <= r <= 8, r == binary_prec_s(tag),
{
    match tag {
        BinaryTag::Or => 1,
        BinaryTag::And => 2,
        BinaryTag::Equal | BinaryTag::NotEqual | BinaryTag::Like => 4,
        BinaryTag::GreaterThan
        | BinaryTag::GreaterThanOrEqual
        | BinaryTag::LessThan
        | BinaryTag::LessThanOrEqual => 5,
        BinaryTag::Add | BinaryTag::Subtract => 6,
        BinaryTag::Multiply | BinaryTag::Divide | BinaryTag::Remainder => 7,
        BinaryTag::Exponentiate => 8,
    }
}

pub fn binary_assoc(tag: BinaryTag) -> (r: u8)
    ensures r <= 1, r == binary_assoc_s(tag),
{
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

pub fn prefix_prec(tag: UnaryTag) -> (r: u8)
    ensures 3 <= r <= 10, r == prefix_prec_s(tag),
{
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity | UnaryTag::Negate => 10,
    }
}


pub enum PostfixOp {
    Factorial,
    Is { negated: bool, nan: bool },
}

pub proof fn token_views_shift(s: Seq<Token>, pos: int, k: int)
    requires
        0 <= pos,
        0 <= k,
        pos + k <= s.len(),
    ensures
        verified_production::token_views(s.subrange(pos, s.len() as int)).subrange(
            k,
            (s.len() - pos) as int,
        ) == verified_production::token_views(s.subrange(pos + k, s.len() as int)),
    decreases k,
{
    super::verified_roundtrip::token_views_len(s.subrange(pos, s.len() as int));
    if k == 0 {
        assert(verified_production::token_views(s.subrange(pos, s.len() as int)).subrange(
            0,
            (s.len() - pos) as int,
        ) =~= verified_production::token_views(s.subrange(pos, s.len() as int)));
    } else {
        super::verified_roundtrip::token_views_suffix(s, pos);
        token_views_shift(s, pos + 1, k - 1);
        assert(verified_production::token_views(s.subrange(pos, s.len() as int)).subrange(
            k,
            (s.len() - pos) as int,
        ) =~= verified_production::token_views(s.subrange(pos, s.len() as int)).drop_first().subrange(
            k - 1,
            (s.len() - pos - 1) as int,
        ));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
pub fn parse_postfix_at(toks: &Vec<Token>, pos: usize, min_prec: u8) -> (r: (Option<PostfixOp>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.1 == pos,
        forall|lhs: SExpr| #[trigger] sparse_postfix_loop(
            lhs,
            verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            min_prec,
        ) == postfix_after(r, lhs, toks@, min_prec),
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    if pos >= toks.len() {
        proof {
            super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
            assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                == postfix_after((None::<PostfixOp>, pos), lhs, toks@, min_prec) by {
                reveal_with_fuel(sparse_postfix_loop, 1);
            }
        }
        return (None, pos);
    }
    proof {
        super::verified_roundtrip::token_views_suffix(toks@, pos as int);
    }
    match &toks[pos] {
        Token::Keyword(Keyword::Is) => {
            if 4 < min_prec {
                proof {
                    assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                        == postfix_after((None::<PostfixOp>, pos), lhs, toks@, min_prec) by {
                        reveal_with_fuel(sparse_postfix_loop, 1);
                    }
                }
                return (None, pos);
            }
            let mut p = pos + 1;
            let negated = if p < toks.len() && matches!(toks[p], Token::Keyword(Keyword::Not)) {
                proof {
                    super::verified_roundtrip::token_views_suffix(toks@, pos as int + 1);
                }
                p = p + 1;
                true
            } else {
                if p < toks.len() {
                    proof {
                        super::verified_roundtrip::token_views_suffix(toks@, pos as int + 1);
                    }
                }
                false
            };
            let ghost sp: int = if negated { 2 } else { 1 };
            if p < toks.len() {
                proof {
                    assert(p as int == pos as int + sp);
                    super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
                    super::verified_roundtrip::token_views_suffix(toks@, p as int);
                    if pos + 1 < toks.len() {
                        super::verified_roundtrip::token_views_suffix(toks@, pos as int + 1);
                    }
                    token_views_shift(toks@, pos as int, sp);
                    token_views_shift(toks@, pos as int, sp + 1);
                }
                let res = match &toks[p] {
                    Token::Keyword(Keyword::NaN) => (Some(PostfixOp::Is { negated, nan: true }), p + 1),
                    Token::Keyword(Keyword::Null) => {
                        (Some(PostfixOp::Is { negated, nan: false }), p + 1)
                    },
                    _ => (None, pos),
                };
                proof {
                    assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                        == postfix_after(res, lhs, toks@, min_prec) by {
                        reveal_with_fuel(sparse_postfix_loop, 1);
                    }
                }
                res
            } else {
                proof {
                    super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
                    assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                        == postfix_after((None::<PostfixOp>, pos), lhs, toks@, min_prec) by {
                        reveal_with_fuel(sparse_postfix_loop, 1);
                    }
                }
                (None, pos)
            }
        },
        Token::Exclamation => {
            if 9 < min_prec {
                proof {
                    assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                        == postfix_after((None::<PostfixOp>, pos), lhs, toks@, min_prec) by {
                        reveal_with_fuel(sparse_postfix_loop, 1);
                    }
                }
                (None, pos)
            } else {
                let res = (Some(PostfixOp::Factorial), pos + 1);
                proof {
                    assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                        == postfix_after(res, lhs, toks@, min_prec) by {
                        reveal_with_fuel(sparse_postfix_loop, 1);
                    }
                }
                res
            }
        },
        _ => {
            proof {
                assert forall|lhs: SExpr| #[trigger] sparse_postfix_loop(lhs, input, min_prec)
                    == postfix_after((None::<PostfixOp>, pos), lhs, toks@, min_prec) by {
                    reveal_with_fuel(sparse_postfix_loop, 1);
                    reveal(verified_production::token_view);
                }
            }
            (None, pos)
        },
    }
}

pub open spec fn postfix_view(op: PostfixOp, lhs: SExpr) -> SExpr {
    match op {
        PostfixOp::Factorial => SExpr::Factorial(Box::new(lhs)),
        PostfixOp::Is { negated, nan } => {
            let lit = if nan { IsLit::NaN } else { IsLit::Null };
            let is = SExpr::Is(Box::new(lhs), lit);
            if negated {
                SExpr::Unary(UnaryTag::Not, Box::new(is))
            } else {
                is
            }
        },
    }
}

pub open spec fn postfix_after(
    r: (Option<PostfixOp>, usize),
    lhs: SExpr,
    toks: Seq<Token>,
    min_prec: u8,
) -> (SExpr, Seq<TokenView>) {
    let rest = verified_production::token_views(toks.subrange(r.1 as int, toks.len() as int));
    match r.0 {
        Some(op) => sparse_postfix_loop(postfix_view(op, lhs), rest, min_prec),
        None => (lhs, rest),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30000)]
pub fn build_postfix(op: PostfixOp, lhs: ast::Expression) -> (r: ast::Expression)
    ensures
        super::verified_roundtrip::view_expr(r) == postfix_view(op, super::verified_roundtrip::view_expr(lhs)),
{
    proof {
        reveal_with_fuel(super::verified_roundtrip::view_expr, 2);
    }
    match op {
        PostfixOp::Factorial => {
            ast::Expression::Operator(ast::Operator::Factorial(Box::new(lhs)))
        },
        PostfixOp::Is { negated, nan } => {
            let value = if nan {
                ast::Literal::Float(float_trust::canonical_nan())
            } else {
                ast::Literal::Null
            };
            let is = ast::Expression::Operator(ast::Operator::Is(Box::new(lhs), value));
            if negated {
                ast::Expression::Operator(ast::Operator::Not(Box::new(is)))
            } else {
                is
            }
        },
    }
}


fn all_ascii_digits(n: &Vec<u8>) -> bool {
    let mut i = 0;
    while i < n.len()
        invariant
            i <= n.len(),
        decreases n.len() - i,
    {
        if n[i] < b'0' || n[i] > b'9' {
            return false;
        }
        i = i + 1;
    }
    true
}

#[verifier::spinoff_prover]
#[verifier::rlimit(600000)]
pub fn parse_atom(toks: &Vec<Token>, pos: usize, fuel: usize) -> (r: (
    Option<ast::Expression>,
    usize,
    Option<super::parse_error::ParseError>,
))
    requires
        pos <= toks.len(),
        fuel >= 2 * (toks.len() - pos) + 2,
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = sparse_atom(input, fuel as nat);
            match r.0 {
                Some(e) => sopt is Some
                    && super::verified_roundtrip::view_expr(e) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
    decreases fuel, 3int,
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    reveal_with_fuel(sparse_atom, 1);
    proof {
        reveal_with_fuel(super::verified_roundtrip::view_expr, 2);
        reveal(verified_production::parse_literal_views);
    }
    if fuel == 0 || pos >= toks.len() {
        proof {
            super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        super::verified_roundtrip::token_views_suffix(toks@, pos as int);
    }
    match &toks[pos] {
        Token::Asterisk => (Some(ast::Expression::All), pos + 1, None),
        Token::Number(n) => {
            match parse_literal_exec(&toks[pos]) {
                Some(l) => (Some(ast::Expression::Literal(l)), pos + 1, None),
                None => if all_ascii_digits(n) {
                    (None, pos, Some(ParseError::NumberTooLarge))
                } else {
                    (None, pos, Some(ParseError::InvalidFloatLiteral(n.clone())))
                },
            }
        },
        Token::String(_) => {
            match parse_literal_exec(&toks[pos]) {
                Some(l) => (Some(ast::Expression::Literal(l)), pos + 1, None),
                None => (None, pos, Some(ParseError::ExpectedAtom(toks[pos].clone()))),
            }
        },
        Token::Keyword(Keyword::True) => {
            (Some(ast::Expression::Literal(ast::Literal::Boolean(true))), pos + 1, None)
        },
        Token::Keyword(Keyword::False) => {
            (Some(ast::Expression::Literal(ast::Literal::Boolean(false))), pos + 1, None)
        },
        Token::Keyword(Keyword::Infinity) => {
            (
                Some(ast::Expression::Literal(ast::Literal::Float(float_trust::infinity()))),
                pos + 1,
                None,
            )
        },
        Token::Keyword(Keyword::NaN) => {
            (
                Some(ast::Expression::Literal(ast::Literal::Float(float_trust::canonical_nan()))),
                pos + 1,
                None,
            )
        },
        Token::Keyword(Keyword::Null) => {
            (Some(ast::Expression::Literal(ast::Literal::Null)), pos + 1, None)
        },
        Token::Ident(name) => {
            if pos + 1 < toks.len() {
                proof {
                    super::verified_roundtrip::token_views_suffix(toks@, pos as int + 1);
                }
            } else {
                proof {
                    super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
                }
            }
            if pos + 1 < toks.len() && matches!(toks[pos + 1], Token::OpenParen) {
                let fname = name.clone();
                proof {
                    assert(input[0] == verified_production::token_view(toks@[pos as int]));
                    assert(input[0] == TokenView::Ident(fname));
                }
                let (fopt, fpos, ferr) = parse_function_call(toks, fname, pos + 2, fuel);
                proof {
                    super::verified_roundtrip::token_views_len(
                        toks@.subrange(pos as int, toks@.len() as int));
                    token_views_shift(toks@, pos as int, 2);
                    assert(input.subrange(2, input.len() as int)
                        == verified_production::token_views(toks@.subrange(pos as int + 2, toks@.len() as int)));
                }
                (fopt, fpos, ferr)
            } else if pos + 1 < toks.len() && matches!(toks[pos + 1], Token::Period) {
                let table = name.clone();
                if pos + 2 < toks.len() {
                    proof {
                        super::verified_roundtrip::token_views_suffix(toks@, pos as int + 2);
                    }
                    match &toks[pos + 2] {
                        Token::Ident(column) => {
                            proof {
                                token_views_shift(toks@, pos as int, 3);
                            }
                            (
                                Some(ast::Expression::Column(Some(table), column.clone())),
                                pos + 3,
                                None,
                            )
                        },
                        _ => (None, pos, Some(ParseError::ExpectedIdent(toks[pos + 2].clone()))),
                    }
                } else {
                    proof {
                        super::verified_roundtrip::token_views_len(toks@.subrange(pos as int + 2, toks@.len() as int));
                    }
                    (None, pos, Some(ParseError::UnexpectedEof))
                }
            } else {
                (Some(ast::Expression::Column(None, name.clone())), pos + 1, None)
            }
        },
        Token::OpenParen => {
            let (inner, ipos, ierr) = parse_expression_at(toks, pos + 1, 0, fuel - 1);
            match inner {
                Some(expr) => {
                    if ipos < toks.len() && matches!(toks[ipos], Token::CloseParen) {
                        proof {
                            super::verified_roundtrip::token_views_suffix(toks@, ipos as int);
                        }
                        (Some(expr), ipos + 1, None)
                    } else {
                        if ipos < toks.len() {
                            proof {
                                super::verified_roundtrip::token_views_suffix(toks@, ipos as int);
                            }
                            (
                                None,
                                pos,
                                Some(ParseError::ExpectedToken(Token::CloseParen, toks[ipos].clone())),
                            )
                        } else {
                            proof {
                                super::verified_roundtrip::token_views_len(toks@.subrange(ipos as int, toks@.len() as int));
                            }
                            (None, pos, Some(ParseError::UnexpectedEof))
                        }
                    }
                },
                None => (None, pos, ierr),
            }
        },
        _ => (None, pos, Some(ParseError::ExpectedAtom(toks[pos].clone()))),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50000)]
pub fn parse_fn_args_exec(toks: &Vec<Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<ast::Expression>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
        fuel >= 2 * (toks.len() - pos) + 4,
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (aopt, arest) = sparse_fn_args(input, fuel as nat);
            match r.0 {
                Some(args) => aopt is Some
                    && super::verified_roundtrip::view_args(args@) == aopt.unwrap()
                    && arest == verified_production::token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => aopt is None,
            }
        }),
    decreases fuel, 1int,
{
    reveal_with_fuel(sparse_fn_args, 1);
    if pos >= toks.len() {
        proof {
            super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        super::verified_roundtrip::token_views_suffix(toks@, pos as int);
    }
    if matches!(toks[pos], Token::CloseParen) {
        let v: Vec<ast::Expression> = Vec::new();
        assert(super::verified_roundtrip::view_args(v@) == Seq::<SExpr>::empty());
        (Some(v), pos, None)
    } else {
        parse_fn_args_ne_exec(toks, pos, fuel)
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50000)]
pub fn parse_fn_args_ne_exec(toks: &Vec<Token>, pos: usize, fuel: usize)
    -> (r: (Option<Vec<ast::Expression>>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
        fuel >= 2 * (toks.len() - pos) + 4,
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (aopt, arest) = sparse_fn_args_nonempty(input, fuel as nat);
            match r.0 {
                Some(args) => aopt is Some
                    && super::verified_roundtrip::view_args(args@) == aopt.unwrap()
                    && arest == verified_production::token_views(toks@.subrange(r.1 as int, toks@.len() as int)),
                None => aopt is None,
            }
        }),
    decreases fuel, 0int,
{
    reveal_with_fuel(sparse_fn_args_nonempty, 1);
    if pos >= toks.len() {
        proof {
            super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    let (eopt, npos, eerr) = parse_expression_at(toks, pos, 0, fuel - 1);
    match eopt {
        Some(expr) => {
            if npos >= toks.len() {
                proof {
                    super::verified_roundtrip::token_views_len(toks@.subrange(npos as int, toks@.len() as int));
                }
                (None, pos, Some(ParseError::UnexpectedEof))
            } else {
                proof {
                    super::verified_roundtrip::token_views_suffix(toks@, npos as int);
                }
                if matches!(toks[npos], Token::CloseParen) {
                    let mut v: Vec<ast::Expression> = Vec::new();
                    v.push(expr);
                    proof {
                        super::verified_roundtrip::view_args_step(v@);
                        assert(v@.drop_first() =~= Seq::<ast::Expression>::empty());
                    }
                    (Some(v), npos, None)
                } else if matches!(toks[npos], Token::Comma) {
                    let (more, mpos, merr) = parse_fn_args_ne_exec(toks, npos + 1, fuel - 1);
                    match more {
                        Some(mut mv) => {
                            let ghost old_mv = mv@;
                            mv.insert(0, expr);
                            proof {
                                super::verified_roundtrip::view_args_step(mv@);
                                assert(mv@.drop_first() =~= old_mv);
                            }
                            (Some(mv), mpos, None)
                        },
                        None => (None, pos, merr),
                    }
                } else {
                    (None, pos, Some(ParseError::ExpectedToken(Token::Comma, toks[npos].clone())))
                }
            }
        },
        None => (None, pos, eerr),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50000)]
pub fn parse_function_call(toks: &Vec<Token>, name: String, pos: usize, fuel: usize)
    -> (r: (Option<ast::Expression>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
        fuel >= 2 * (toks.len() - pos) + 4,
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (aopt, arest) = sparse_fn_args(input, fuel as nat);
            match r.0 {
                Some(e) => aopt is Some && arest.len() > 0 && arest[0] == TokenView::CloseParen
                    && super::verified_roundtrip::view_expr(e) == SExpr::Function(name, aopt.unwrap())
                    && verified_production::token_views(toks@.subrange(r.1 as int, toks@.len() as int))
                        == arest.drop_first(),
                None => !(aopt is Some && arest.len() > 0 && arest[0] == TokenView::CloseParen),
            }
        }),
    decreases fuel, 2int,
{
    let (aopt, apos, aerr) = parse_fn_args_exec(toks, pos, fuel);
    match aopt {
        Some(args) => {
            if apos < toks.len() && matches!(toks[apos], Token::CloseParen) {
                proof {
                    super::verified_roundtrip::token_views_suffix(toks@, apos as int);
                    reveal_with_fuel(super::verified_roundtrip::view_expr, 1);
                }
                (Some(ast::Expression::Function(name, args)), apos + 1, None)
            } else {
                if apos < toks.len() {
                    proof {
                        super::verified_roundtrip::token_views_suffix(toks@, apos as int);
                    }
                    (
                        None,
                        pos,
                        Some(ParseError::ExpectedToken(Token::CloseParen, toks[apos].clone())),
                    )
                } else {
                    proof {
                        super::verified_roundtrip::token_views_len(toks@.subrange(apos as int, toks@.len() as int));
                    }
                    (None, pos, Some(ParseError::UnexpectedEof))
                }
            }
        },
        None => (None, pos, aerr),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(400000)]
pub fn parse_expression_at(toks: &Vec<Token>, pos: usize, min_prec: u8, fuel: usize)
    -> (r: (Option<ast::Expression>, usize, Option<ParseError>))
    requires
        pos <= toks.len(),
        fuel >= 2 * (toks.len() - pos) + 3,
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
        r.0 is None ==> r.2 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
            let (sopt, srest) = sparse_prec(input, min_prec, fuel as nat);
            match r.0 {
                Some(e) => sopt is Some
                    && super::verified_roundtrip::view_expr(e) == sopt.unwrap()
                    && srest == verified_production::token_views(
                        toks@.subrange(r.1 as int, toks@.len() as int)),
                None => sopt is None,
            }
        }),
    decreases fuel, 4int,
{
    let ghost input = verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int));
    reveal_with_fuel(sparse_prec, 1);
    if fuel == 0 || pos >= toks.len() {
        proof {
            super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        }
        return (None, pos, Some(ParseError::UnexpectedEof));
    }
    proof {
        super::verified_roundtrip::token_views_suffix(toks@, pos as int);
    }
    let ghost lhs_opt_s = prec_lhs_phase(input, min_prec, fuel as nat).0;
    let ghost after_lhs_s = prec_lhs_phase(input, min_prec, fuel as nat).1;
    let popt = prefix_op_exec(&toks[pos]);
    let (lhs_opt, lhs_pos, lhs_err) = if popt.is_some() && prefix_prec(popt.unwrap()) >= min_prec {
        let tag = popt.unwrap();
        let next_prec = prefix_prec(tag);
        proof {
            super::verified_roundtrip::token_views_suffix(toks@, pos as int);
        }
        let (rhs, rpos, rerr) = parse_expression_at(toks, pos + 1, next_prec, fuel - 1);
        let res = match rhs {
            Some(inner) => (Some(build_unary(tag, inner)), rpos, None),
            None => (None, pos, rerr),
        };
        proof {
            assert(verified_expression::prefix_operator(input[0]) == Some(tag));
            assert(input.drop_first() == verified_production::token_views(
                toks@.subrange(pos as int + 1, toks@.len() as int)));
        }
        res
    } else {
        parse_atom(toks, pos, fuel - 1)
    };
    proof {
        assert(match lhs_opt {
            Some(e) => lhs_opt_s is Some
                && super::verified_roundtrip::view_expr(e) == lhs_opt_s.unwrap()
                && verified_production::token_views(toks@.subrange(lhs_pos as int, toks@.len() as int)) == after_lhs_s,
            None => lhs_opt_s is None,
        });
    }
    let mut lhs = match lhs_opt {
        Some(expr) => expr,
        None => return (None, pos, lhs_err),
    };
    let mut cur = lhs_pos;
    let ghost lhs0_view = super::verified_roundtrip::view_expr(lhs);
    let ghost after_lhs_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost (lhs1_s, cur1_s) = sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec);

    loop
        invariant
            pos < cur <= toks.len(),
            sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec)
                == sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec),
        ensures
            sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec)
                == (super::verified_roundtrip::view_expr(lhs),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let (op, npos) = parse_postfix_at(toks, cur, min_prec);
        match op {
            Some(op) => {
                proof {
                    assert(sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec)
                        == postfix_after((Some(op), npos), super::verified_roundtrip::view_expr(lhs), toks@, min_prec));
                }
                lhs = build_postfix(op, lhs);
                cur = npos;
            },
            None => {
                proof {
                    assert(sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec)
                        == postfix_after((None::<PostfixOp>, npos),
                            super::verified_roundtrip::view_expr(lhs), toks@, min_prec));
                }
                break;
            },
        }
    }
    let ghost target_infix = sparse_infix_loop(lhs1_s, cur1_s, min_prec, fuel as nat);
    let ghost mut gfuel: nat = fuel as nat;

    loop
        invariant
            pos < cur <= toks.len(),
            fuel > 0,
            gfuel <= fuel,
            2 * (toks.len() - cur) + 3 <= gfuel,
            input == verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int)),
            lhs_opt_s == prec_lhs_phase(input, min_prec, fuel as nat).0,
            after_lhs_s == prec_lhs_phase(input, min_prec, fuel as nat).1,
            lhs_opt_s == Some(lhs0_view),
            after_lhs_s == after_lhs_v,
            lhs1_s == sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec).0,
            cur1_s == sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec).1,
            target_infix == sparse_infix_loop(lhs1_s, cur1_s, min_prec, fuel as nat),
            sparse_infix_loop(super::verified_roundtrip::view_expr(lhs),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec, gfuel)
                == target_infix,
        ensures
            target_infix == (Some(super::verified_roundtrip::view_expr(lhs)),
                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        if cur >= toks.len() {
            proof {
                super::verified_roundtrip::token_views_len(toks@.subrange(cur as int, toks@.len() as int));
                lemma_infix_stop(super::verified_roundtrip::view_expr(lhs),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec, gfuel);
            }
            break;
        }
        proof {
            super::verified_roundtrip::token_views_suffix(toks@, cur as int);
        }
        match binary_tag_exec(&toks[cur]) {
            Some(tag) if binary_prec(tag) >= min_prec => {
                let next_prec = binary_prec(tag) + binary_assoc(tag);
                proof {
                    super::verified_roundtrip::token_views_len(toks@.subrange(cur as int + 1, toks@.len() as int));
                }
                let (rhs, rpos, rerr) = parse_expression_at(toks, cur + 1, next_prec, fuel - 1);
                match rhs {
                    Some(right) => {
                        proof {
                            lemma_prec_fuel(
                                verified_production::token_views(toks@.subrange(cur as int + 1, toks@.len() as int)),
                                next_prec, (fuel - 1) as nat, (gfuel - 1) as nat);
                            lemma_infix_step(super::verified_roundtrip::view_expr(lhs), tag,
                                verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)),
                                super::verified_roundtrip::view_expr(right),
                                verified_production::token_views(toks@.subrange(rpos as int, toks@.len() as int)),
                                min_prec, gfuel);
                        }
                        lhs = build_binary(tag, lhs, right);
                        cur = rpos;
                        proof {
                            gfuel = (gfuel - 1) as nat;
                        }
                    },
                    None => {
                        let ghost cv = verified_production::token_views(
                            toks@.subrange(cur as int, toks@.len() as int));
                        proof {
                            assert(sparse_infix_loop(super::verified_roundtrip::view_expr(lhs), cv, min_prec, gfuel)
                                == target_infix);
                            super::verified_roundtrip::token_views_suffix(toks@, cur as int);
                            super::verified_roundtrip::token_views_len(
                                toks@.subrange(cur as int, toks@.len() as int));
                            super::verified_roundtrip::token_views_len(
                                toks@.subrange(cur as int + 1, toks@.len() as int));
                            lemma_prec_fuel(
                                verified_production::token_views(toks@.subrange(cur as int + 1, toks@.len() as int)),
                                next_prec, (fuel - 1) as nat, (gfuel - 1) as nat);
                            assert(next_prec == (binary_prec_s(tag) + binary_assoc_s(tag)) as u8);
                            assert(sparse_prec(verified_production::token_views(
                                toks@.subrange(cur as int + 1, toks@.len() as int)), next_prec,
                                (fuel - 1) as nat).0 is None);
                            assert(cv.drop_first() == verified_production::token_views(
                                toks@.subrange(cur as int + 1, toks@.len() as int)));
                            assert(sparse_prec(cv.drop_first(),
                                (binary_prec_s(tag) + binary_assoc_s(tag)) as u8, (gfuel - 1) as nat).0 is None);
                            assert(cv.len() > 0);
                            assert(cv[0] == verified_production::token_view(toks@[cur as int]));
                            assert(verified_expression::binary_from_token(cv[0]) == Some(tag)) by {
                                reveal(verified_expression::binary_from_token);
                            }
                            assert(binary_prec_s(tag) >= min_prec);
                            assert(gfuel > 0);
                            lemma_infix_step_none(super::verified_roundtrip::view_expr(lhs), tag, cv, min_prec, gfuel);
                            assert(target_infix.0 is None);
                            super::verified_roundtrip::token_views_len(
                                toks@.subrange(pos as int, toks@.len() as int));
                            assert(input.len() > 0);
                            lemma_prec_none(input, min_prec, fuel as nat, lhs0_view, after_lhs_v);
                        }
                        return (None, pos, rerr);
                    },
                }
            },
            _ => {
                proof {
                    lemma_infix_stop(super::verified_roundtrip::view_expr(lhs),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec, gfuel);
                }
                break;
            },
        }
    }
    let ghost lhs2_view = super::verified_roundtrip::view_expr(lhs);
    let ghost after2_v = verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int));
    let ghost (lhs3_v, cur3_v) = sparse_postfix_loop(lhs2_view, after2_v, min_prec);

    loop
        invariant
            pos < cur <= toks.len(),
            sparse_postfix_loop(lhs2_view, after2_v, min_prec)
                == sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec),
        ensures
            sparse_postfix_loop(lhs2_view, after2_v, min_prec)
                == (super::verified_roundtrip::view_expr(lhs),
                    verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int))),
        decreases toks.len() - cur,
    {
        let (op, npos) = parse_postfix_at(toks, cur, min_prec);
        match op {
            Some(op) => {
                proof {
                    assert(sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec)
                        == postfix_after((Some(op), npos), super::verified_roundtrip::view_expr(lhs), toks@, min_prec));
                }
                lhs = build_postfix(op, lhs);
                cur = npos;
            },
            None => {
                proof {
                    assert(sparse_postfix_loop(super::verified_roundtrip::view_expr(lhs),
                        verified_production::token_views(toks@.subrange(cur as int, toks@.len() as int)), min_prec)
                        == postfix_after((None::<PostfixOp>, npos),
                            super::verified_roundtrip::view_expr(lhs), toks@, min_prec));
                }
                break;
            },
        }
    }
    proof {
        reveal_with_fuel(sparse_prec, 1);
        assert(lhs_opt_s == Some(lhs0_view));
        assert(after_lhs_s == after_lhs_v);
        assert(sparse_postfix_loop(lhs0_view, after_lhs_v, min_prec) == (lhs1_s, cur1_s));
        assert(target_infix == (Some(lhs2_view), after2_v));
        assert(lhs3_v == super::verified_roundtrip::view_expr(lhs));
        assert(cur3_v == verified_production::token_views(
            toks@.subrange(cur as int, toks@.len() as int)));
        assert(sparse_prec(input, min_prec, fuel as nat)
            == (Some::<SExpr>(lhs3_v), cur3_v));
    }

    (Some(lhs), cur, None)
}

pub fn parse_expression_full(toks: &Vec<Token>) -> (r: (
    Option<ast::Expression>,
    Option<ParseError>,
))
    ensures
        r.0 is None ==> r.1 is Some,
        ({
            let input = verified_production::token_views(toks@.subrange(0, toks@.len() as int));
            let (sopt, srest) = sparse_prec(input, 0, (2 * toks.len() + 3) as nat);
            (toks.len() <= (usize::MAX - 3) / 2 && sopt is Some && srest.len() == 0)
                ==> (r.0 is Some && super::verified_roundtrip::view_expr(r.0.unwrap()) == sopt.unwrap())
        }),
{
    if toks.len() > (usize::MAX - 3) / 2 {
        return (None, Some(ParseError::UnexpectedEof));
    }
    let fuel = 2 * toks.len() + 3;
    let (opt, consumed, err) = parse_expression_at(toks, 0, 0, fuel);
    proof {
        if consumed <= toks.len() {
            super::verified_roundtrip::token_views_len(
                toks@.subrange(consumed as int, toks@.len() as int));
        }
    }
    match opt {
        Some(expr) => {
            if consumed == toks.len() {
                (Some(expr), None)
            } else {
                (None, Some(ParseError::UnexpectedToken(toks[consumed].clone())))
            }
        },
        None => (None, err),
    }
}

pub open spec fn sparse_prec(input: Seq<TokenView>, min_prec: u8, fuel: nat)
    -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 3nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        let (lhs_opt, after_lhs) = match verified_expression::prefix_operator(input[0]) {
            Some(tag) => if prefix_prec_s(tag) >= min_prec {
                match sparse_prec(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat) {
                    (Some(inner), rest) => (Some(SExpr::Unary(tag, Box::new(inner))), rest),
                    (None, _) => (None::<SExpr>, input),
                }
            } else {
                sparse_atom(input, (fuel - 1) as nat)
            },
            None => sparse_atom(input, (fuel - 1) as nat),
        };
        match lhs_opt {
            None => (None, input),
            Some(lhs0) => {
                let (lhs1, cur1) = sparse_postfix_loop(lhs0, after_lhs, min_prec);
                match sparse_infix_loop(lhs1, cur1, min_prec, fuel) {
                    (None, _) => (None, input),
                    (Some(lhs2), cur2) => {
                        let (lhs3, cur3) = sparse_postfix_loop(lhs2, cur2, min_prec);
                        (Some(lhs3), cur3)
                    },
                }
            },
        }
    }
}

pub open spec fn sparse_atom(input: Seq<TokenView>, fuel: nat)
    -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 3nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Asterisk => (Some(SExpr::All), input.drop_first()),
            TokenView::Number(bytes) =>
                match verified_production::parse_literal_views(seq![TokenView::Number(bytes)]) {
                    Some(lit) => (Some(SExpr::Literal(lit)), input.drop_first()),
                    None => (None, input),
                },
            TokenView::String(value) =>
                (Some(SExpr::Literal(ast::Literal::String(value))), input.drop_first()),
            TokenView::Keyword(Keyword::True) =>
                (Some(SExpr::Literal(ast::Literal::Boolean(true))), input.drop_first()),
            TokenView::Keyword(Keyword::False) =>
                (Some(SExpr::Literal(ast::Literal::Boolean(false))), input.drop_first()),
            TokenView::Keyword(Keyword::Infinity) =>
                (Some(SExpr::Literal(ast::Literal::Float(float_trust::spec_infinity()))), input.drop_first()),
            TokenView::Keyword(Keyword::NaN) =>
                (Some(SExpr::Literal(ast::Literal::Float(float_trust::spec_canonical_nan()))), input.drop_first()),
            TokenView::Keyword(Keyword::Null) =>
                (Some(SExpr::Literal(ast::Literal::Null)), input.drop_first()),
            TokenView::Ident(name) => {
                if input.len() >= 2 && input[1] == TokenView::OpenParen {
                    match sparse_fn_args(input.subrange(2, input.len() as int), fuel) {
                        (Some(args), rest) if rest.len() > 0 && rest[0] == TokenView::CloseParen =>
                            (Some(SExpr::Function(name, args)), rest.drop_first()),
                        _ => (None, input),
                    }
                } else if input.len() >= 2 && input[1] == TokenView::Period {
                    if input.len() >= 3 {
                        match input[2] {
                            TokenView::Ident(column) =>
                                (Some(SExpr::Column(Some(name), column)), input.subrange(3, input.len() as int)),
                            _ => (None, input),
                        }
                    } else {
                        (None, input)
                    }
                } else {
                    (Some(SExpr::Column(None, name)), input.drop_first())
                }
            },
            TokenView::OpenParen =>
                match sparse_prec(input.drop_first(), 0, (fuel - 1) as nat) {
                    (Some(e), rest) => if rest.len() > 0 && rest[0] == TokenView::CloseParen {
                        (Some(e), rest.drop_first())
                    } else {
                        (None, input)
                    },
                    (None, _) => (None, input),
                },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_infix_loop(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 2nat,
{
    if fuel == 0 || input.len() == 0 {
        (Some(lhs), input)
    } else {
        match verified_expression::binary_from_token(input[0]) {
            Some(tag) => if binary_prec_s(tag) >= min_prec {
                let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
                match sparse_prec(input.drop_first(), next_prec, (fuel - 1) as nat) {
                    (Some(right), rest) => sparse_infix_loop(
                        SExpr::Binary(tag, Box::new(lhs), Box::new(right)),
                        rest,
                        min_prec,
                        (fuel - 1) as nat,
                    ),
                    (None, _) => (None, input),
                }
            } else {
                (Some(lhs), input)
            },
            None => (Some(lhs), input),
        }
    }
}

pub open spec fn sparse_postfix_loop(lhs: SExpr, input: Seq<TokenView>, min_prec: u8)
    -> (SExpr, Seq<TokenView>)
    decreases input.len(),
{
    if input.len() == 0 {
        (lhs, input)
    } else if input[0] == TokenView::Exclamation {
        if 9 >= min_prec {
            sparse_postfix_loop(SExpr::Factorial(Box::new(lhs)), input.drop_first(), min_prec)
        } else {
            (lhs, input)
        }
    } else if input[0] == TokenView::Keyword(Keyword::Is) {
        if 4 >= min_prec {
            let negated = input.len() >= 2 && input[1] == TokenView::Keyword(Keyword::Not);
            let p: int = if negated { 2 } else { 1 };
            if input.len() > p && (input[p] == TokenView::Keyword(Keyword::NaN)
                || input[p] == TokenView::Keyword(Keyword::Null)) {
                let lit = if input[p] == TokenView::Keyword(Keyword::NaN) {
                    IsLit::NaN
                } else {
                    IsLit::Null
                };
                let is_expr = SExpr::Is(Box::new(lhs), lit);
                let new_lhs = if negated {
                    SExpr::Unary(UnaryTag::Not, Box::new(is_expr))
                } else {
                    is_expr
                };
                sparse_postfix_loop(new_lhs, input.subrange(p + 1, input.len() as int), min_prec)
            } else {
                (lhs, input)
            }
        } else {
            (lhs, input)
        }
    } else {
        (lhs, input)
    }
}

pub open spec fn sparse_fn_args(input: Seq<TokenView>, fuel: nat)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases fuel, 2nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else if input[0] == TokenView::CloseParen {
        (Some(Seq::empty()), input)
    } else {
        sparse_fn_args_nonempty(input, fuel)
    }
}

pub open spec fn sparse_fn_args_nonempty(input: Seq<TokenView>, fuel: nat)
    -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases fuel, 1nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match sparse_prec(input, 0, (fuel - 1) as nat) {
            (Some(e), rest) => {
                if rest.len() == 0 {
                    (None, input)
                } else if rest[0] == TokenView::CloseParen {
                    (Some(seq![e]), rest)
                } else if rest[0] == TokenView::Comma {
                    match sparse_fn_args_nonempty(rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), rest2) => (Some(seq![e] + more), rest2),
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


pub proof fn lemma_postfix_slen(lhs: SExpr, input: Seq<TokenView>, min_prec: u8)
    ensures
        sparse_postfix_loop(lhs, input, min_prec).1.len() <= input.len(),
    decreases input.len(),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
    if input.len() == 0 {
    } else if input[0] == TokenView::Exclamation {
        if 9 >= min_prec {
            lemma_postfix_slen(SExpr::Factorial(Box::new(lhs)), input.drop_first(), min_prec);
        }
    } else if input[0] == TokenView::Keyword(Keyword::Is) {
        if 4 >= min_prec {
            let negated = input.len() >= 2 && input[1] == TokenView::Keyword(Keyword::Not);
            let p: int = if negated { 2 } else { 1 };
            if input.len() > p && (input[p] == TokenView::Keyword(Keyword::NaN)
                || input[p] == TokenView::Keyword(Keyword::Null)) {
                let lit = if input[p] == TokenView::Keyword(Keyword::NaN) {
                    IsLit::NaN
                } else {
                    IsLit::Null
                };
                let is_expr = SExpr::Is(Box::new(lhs), lit);
                let new_lhs = if negated {
                    SExpr::Unary(UnaryTag::Not, Box::new(is_expr))
                } else {
                    is_expr
                };
                lemma_postfix_slen(new_lhs, input.subrange(p + 1, input.len() as int), min_prec);
            }
        }
    }
}

pub proof fn lemma_infix_slen(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel).1.len() <= input.len(),
    decreases fuel, 2nat,
{
    reveal_with_fuel(sparse_infix_loop, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match verified_expression::binary_from_token(input[0]) {
            Some(tag) => if binary_prec_s(tag) >= min_prec {
                let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
                match sparse_prec(input.drop_first(), next_prec, (fuel - 1) as nat) {
                    (Some(right), rest) => {
                        lemma_prec_slen(input.drop_first(), next_prec, (fuel - 1) as nat);
                        lemma_infix_slen(
                            SExpr::Binary(tag, Box::new(lhs), Box::new(right)),
                            rest,
                            min_prec,
                            (fuel - 1) as nat,
                        );
                    },
                    (None, _) => {},
                }
            } else {
            },
            None => {},
        }
    }
}

pub proof fn lemma_fnargs_slen(input: Seq<TokenView>, fuel: nat)
    ensures
        sparse_fn_args(input, fuel).1.len() <= input.len(),
    decreases fuel, 2nat,
{
    reveal_with_fuel(sparse_fn_args, 1);
    if fuel == 0 || input.len() == 0 {
    } else if input[0] == TokenView::CloseParen {
    } else {
        lemma_fnargs_ne_slen(input, fuel);
    }
}

pub proof fn lemma_fnargs_ne_slen(input: Seq<TokenView>, fuel: nat)
    ensures
        sparse_fn_args_nonempty(input, fuel).1.len() <= input.len(),
    decreases fuel, 1nat,
{
    reveal_with_fuel(sparse_fn_args_nonempty, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match sparse_prec(input, 0, (fuel - 1) as nat) {
            (Some(e), rest) => {
                lemma_prec_slen(input, 0, (fuel - 1) as nat);
                if rest.len() == 0 {
                } else if rest[0] == TokenView::CloseParen {
                } else if rest[0] == TokenView::Comma {
                    match sparse_fn_args_nonempty(rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), rest2) => {
                            lemma_fnargs_ne_slen(rest.drop_first(), (fuel - 1) as nat);
                        },
                        (None, _) => {},
                    }
                } else {
                }
            },
            (None, _) => {},
        }
    }
}

pub proof fn lemma_atom_slen(input: Seq<TokenView>, fuel: nat)
    ensures
        sparse_atom(input, fuel).1.len() <= input.len(),
    decreases fuel, 3nat,
{
    reveal_with_fuel(sparse_atom, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                if input.len() >= 2 && input[1] == TokenView::OpenParen {
                    lemma_fnargs_slen(input.subrange(2, input.len() as int), fuel);
                } else if input.len() >= 3 && input[1] == TokenView::Period {
                } else {
                }
            },
            TokenView::OpenParen => {
                lemma_prec_slen(input.drop_first(), 0, (fuel - 1) as nat);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_prec_slen(input: Seq<TokenView>, min_prec: u8, fuel: nat)
    ensures
        sparse_prec(input, min_prec, fuel).1.len() <= input.len(),
    decreases fuel, 3nat,
{
    reveal_with_fuel(sparse_prec, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match verified_expression::prefix_operator(input[0]) {
            Some(tag) => if prefix_prec_s(tag) >= min_prec {
                lemma_prec_slen(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat);
            } else {
                lemma_atom_slen(input, (fuel - 1) as nat);
            },
            None => {
                lemma_atom_slen(input, (fuel - 1) as nat);
            },
        }
        let (lhs_opt, after_lhs) = match verified_expression::prefix_operator(input[0]) {
            Some(tag) => if prefix_prec_s(tag) >= min_prec {
                match sparse_prec(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat) {
                    (Some(inner), rest) => (Some(SExpr::Unary(tag, Box::new(inner))), rest),
                    (None, _) => (None::<SExpr>, input),
                }
            } else {
                sparse_atom(input, (fuel - 1) as nat)
            },
            None => sparse_atom(input, (fuel - 1) as nat),
        };
        match lhs_opt {
            None => {},
            Some(lhs0) => {
                let (lhs1, cur1) = sparse_postfix_loop(lhs0, after_lhs, min_prec);
                lemma_postfix_slen(lhs0, after_lhs, min_prec);
                match sparse_infix_loop(lhs1, cur1, min_prec, fuel) {
                    (None, _) => {},
                    (Some(lhs2), cur2) => {
                        lemma_infix_slen(lhs1, cur1, min_prec, fuel);
                        lemma_postfix_slen(lhs2, cur2, min_prec);
                    },
                }
            },
        }
    }
}


pub proof fn lemma_atom_fuel(input: Seq<TokenView>, f: nat, g: nat)
    requires
        f >= 2 * input.len() + 2,
        g >= 2 * input.len() + 2,
    ensures
        sparse_atom(input, f) == sparse_atom(input, g),
    decreases input.len(), 1nat,
{
    reveal_with_fuel(sparse_atom, 1);
    if input.len() == 0 {
    } else {
        match input[0] {
            TokenView::Ident(name) => {
                if input.len() >= 2 && input[1] == TokenView::OpenParen {
                    lemma_fnargs_fuel(input.subrange(2, input.len() as int), f, g);
                } else if input.len() >= 3 && input[1] == TokenView::Period {
                } else {
                }
            },
            TokenView::OpenParen => {
                lemma_prec_fuel(input.drop_first(), 0, (f - 1) as nat, (g - 1) as nat);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_infix_fuel(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, f: nat, g: nat)
    requires
        f >= 2 * input.len() + 3,
        g >= 2 * input.len() + 3,
    ensures
        sparse_infix_loop(lhs, input, min_prec, f) == sparse_infix_loop(lhs, input, min_prec, g),
    decreases input.len(), 0nat,
{
    reveal_with_fuel(sparse_infix_loop, 1);
    if input.len() == 0 {
    } else {
        match verified_expression::binary_from_token(input[0]) {
            Some(tag) => if binary_prec_s(tag) >= min_prec {
                let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
                lemma_prec_fuel(input.drop_first(), next_prec, (f - 1) as nat, (g - 1) as nat);
                match sparse_prec(input.drop_first(), next_prec, (f - 1) as nat) {
                    (Some(right), rest) => {
                        lemma_prec_slen(input.drop_first(), next_prec, (f - 1) as nat);
                        lemma_infix_fuel(
                            SExpr::Binary(tag, Box::new(lhs), Box::new(right)),
                            rest,
                            min_prec,
                            (f - 1) as nat,
                            (g - 1) as nat,
                        );
                    },
                    (None, _) => {},
                }
            } else {
            },
            None => {},
        }
    }
}

pub proof fn lemma_fnargs_fuel(input: Seq<TokenView>, f: nat, g: nat)
    requires
        f >= 2 * input.len() + 4,
        g >= 2 * input.len() + 4,
    ensures
        sparse_fn_args(input, f) == sparse_fn_args(input, g),
    decreases input.len(), 4nat,
{
    reveal_with_fuel(sparse_fn_args, 1);
    if input.len() == 0 {
    } else if input[0] == TokenView::CloseParen {
    } else {
        lemma_fnargs_ne_fuel(input, f, g);
    }
}

pub proof fn lemma_fnargs_ne_fuel(input: Seq<TokenView>, f: nat, g: nat)
    requires
        f >= 2 * input.len() + 4,
        g >= 2 * input.len() + 4,
    ensures
        sparse_fn_args_nonempty(input, f) == sparse_fn_args_nonempty(input, g),
    decreases input.len(), 3nat,
{
    reveal_with_fuel(sparse_fn_args_nonempty, 1);
    if input.len() == 0 {
    } else {
        lemma_prec_fuel(input, 0, (f - 1) as nat, (g - 1) as nat);
        match sparse_prec(input, 0, (f - 1) as nat) {
            (Some(e), rest) => {
                lemma_prec_slen(input, 0, (f - 1) as nat);
                if rest.len() == 0 {
                } else if rest[0] == TokenView::CloseParen {
                } else if rest[0] == TokenView::Comma {
                    lemma_fnargs_ne_fuel(rest.drop_first(), (f - 1) as nat, (g - 1) as nat);
                } else {
                }
            },
            (None, _) => {},
        }
    }
}

pub proof fn lemma_prec_fuel(input: Seq<TokenView>, min_prec: u8, f: nat, g: nat)
    requires
        f >= 2 * input.len() + 3,
        g >= 2 * input.len() + 3,
    ensures
        sparse_prec(input, min_prec, f) == sparse_prec(input, min_prec, g),
    decreases input.len(), 2nat,
{
    reveal_with_fuel(sparse_prec, 1);
    if input.len() == 0 {
    } else {
        match verified_expression::prefix_operator(input[0]) {
            Some(tag) => if prefix_prec_s(tag) >= min_prec {
                lemma_prec_fuel(input.drop_first(), prefix_prec_s(tag), (f - 1) as nat, (g - 1) as nat);
                lemma_prec_slen(input.drop_first(), prefix_prec_s(tag), (f - 1) as nat);
            } else {
                lemma_atom_fuel(input, (f - 1) as nat, (g - 1) as nat);
                lemma_atom_slen(input, (f - 1) as nat);
            },
            None => {
                lemma_atom_fuel(input, (f - 1) as nat, (g - 1) as nat);
                lemma_atom_slen(input, (f - 1) as nat);
            },
        }
        let (lhs_opt, after_lhs) = match verified_expression::prefix_operator(input[0]) {
            Some(tag) => if prefix_prec_s(tag) >= min_prec {
                match sparse_prec(input.drop_first(), prefix_prec_s(tag), (f - 1) as nat) {
                    (Some(inner), rest) => (Some(SExpr::Unary(tag, Box::new(inner))), rest),
                    (None, _) => (None::<SExpr>, input),
                }
            } else {
                sparse_atom(input, (f - 1) as nat)
            },
            None => sparse_atom(input, (f - 1) as nat),
        };
        match lhs_opt {
            None => {},
            Some(lhs0) => {
                let (lhs1, cur1) = sparse_postfix_loop(lhs0, after_lhs, min_prec);
                lemma_postfix_slen(lhs0, after_lhs, min_prec);
                lemma_infix_fuel(lhs1, cur1, min_prec, f, g);
            },
        }
    }
}


pub open spec fn prec_boundary(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma
}

pub proof fn infix_halt(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    requires
        input.len() == 0 || verified_expression::binary_from_token(input[0]) is None,
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == (Some(lhs), input),
{
    reveal_with_fuel(sparse_infix_loop, 1);
}

pub proof fn postfix_halt(lhs: SExpr, input: Seq<TokenView>, min_prec: u8)
    requires
        input.len() == 0
            || (input[0] != TokenView::Exclamation && input[0] != TokenView::Keyword(Keyword::Is)),
    ensures
        sparse_postfix_loop(lhs, input, min_prec) == (lhs, input),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
}

pub proof fn lemma_infix_step(
    lhs: SExpr,
    tag: BinaryTag,
    input: Seq<TokenView>,
    rhs: SExpr,
    rest: Seq<TokenView>,
    min_prec: u8,
    fuel: nat,
)
    requires
        fuel > 0,
        input.len() > 0,
        verified_expression::binary_from_token(input[0]) == Some(tag),
        binary_prec_s(tag) >= min_prec,
        sparse_prec(
            input.drop_first(),
            (binary_prec_s(tag) + binary_assoc_s(tag)) as u8,
            (fuel - 1) as nat,
        ) == (Some(rhs), rest),
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == sparse_infix_loop(
            SExpr::Binary(tag, Box::new(lhs), Box::new(rhs)),
            rest,
            min_prec,
            (fuel - 1) as nat,
        ),
{
    reveal_with_fuel(sparse_infix_loop, 1);
}

pub proof fn lemma_infix_stop(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    requires
        input.len() == 0 || match verified_expression::binary_from_token(input[0]) {
            Some(tag) => binary_prec_s(tag) < min_prec,
            None => true,
        },
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == (Some(lhs), input),
{
    reveal_with_fuel(sparse_infix_loop, 1);
}

pub proof fn lemma_infix_step_none(
    lhs: SExpr,
    tag: BinaryTag,
    input: Seq<TokenView>,
    min_prec: u8,
    fuel: nat,
)
    requires
        fuel > 0,
        input.len() > 0,
        verified_expression::binary_from_token(input[0]) == Some(tag),
        binary_prec_s(tag) >= min_prec,
        sparse_prec(
            input.drop_first(),
            (binary_prec_s(tag) + binary_assoc_s(tag)) as u8,
            (fuel - 1) as nat,
        ).0 is None,
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == (None::<SExpr>, input),
{
    reveal_with_fuel(sparse_infix_loop, 1);
}

pub open spec fn prec_lhs_phase(input: Seq<TokenView>, min_prec: u8, fuel: nat)
    -> (Option<SExpr>, Seq<TokenView>) {
    match verified_expression::prefix_operator(input[0]) {
        Some(tag) => if prefix_prec_s(tag) >= min_prec {
            match sparse_prec(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat) {
                (Some(inner), rest) => (Some(SExpr::Unary(tag, Box::new(inner))), rest),
                (None, _) => (None::<SExpr>, input),
            }
        } else {
            sparse_atom(input, (fuel - 1) as nat)
        },
        None => sparse_atom(input, (fuel - 1) as nat),
    }
}

pub proof fn lemma_prec_none(
    input: Seq<TokenView>,
    min_prec: u8,
    fuel: nat,
    lhs0: SExpr,
    after_lhs: Seq<TokenView>,
)
    requires
        fuel > 0,
        input.len() > 0,
        prec_lhs_phase(input, min_prec, fuel).0 == Some(lhs0),
        prec_lhs_phase(input, min_prec, fuel).1 == after_lhs,
        sparse_infix_loop(
            sparse_postfix_loop(lhs0, after_lhs, min_prec).0,
            sparse_postfix_loop(lhs0, after_lhs, min_prec).1,
            min_prec,
            fuel,
        ).0 is None,
    ensures
        sparse_prec(input, min_prec, fuel).0 is None,
{
    reveal_with_fuel(sparse_prec, 1);
}

pub proof fn prec_boundary_halts(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    requires
        prec_boundary(input),
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == (Some(lhs), input),
        sparse_postfix_loop(lhs, input, min_prec) == (lhs, input),
{
    if input.len() == 0 {
        infix_halt(lhs, input, min_prec, fuel);
        postfix_halt(lhs, input, min_prec);
    } else {
        assert(input[0] == TokenView::CloseParen || input[0] == TokenView::Comma);
        assert(verified_expression::binary_from_token(input[0]) is None) by {
            reveal(verified_expression::binary_from_token);
        }
        infix_halt(lhs, input, min_prec, fuel);
        postfix_halt(lhs, input, min_prec);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20000)]
pub proof fn lemma_atom(e: SExpr, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        super::verified_roundtrip::boundary(tail),
        fuel >= super::verified_roundtrip::sprint(e).len(),
    ensures
        sparse_atom(super::verified_roundtrip::sprint(e) + tail, fuel) == (Some(e), tail),
    decreases e, 0nat,
{
    use super::verified_roundtrip::{
        printable_se, sprint, sprint_args, sdepth, slist_depth, boundary, sprint_head, unary_tok,
        binary_tok, islit_tok, unary_tok_prefix, binary_tok_roundtrip,
    };
    reveal(printable_se);
    reveal_with_fuel(sparse_atom, 1);
    reveal_with_fuel(sparse_prec, 1);
    let tokens = sprint(e) + tail;
    match e {
        SExpr::All => {
            assert(tokens[0] == TokenView::Asterisk);
            assert(tokens.drop_first() =~= tail);
        },
        SExpr::Column(table, column) => match table {
            None => {
                assert(tokens[0] == TokenView::Ident(column));
                if tokens.len() >= 2 {
                    assert(tokens[1] == tail[0]);
                }
                assert(tokens.drop_first() =~= tail);
            },
            Some(t) => {
                assert(tokens.len() >= 3);
                assert(tokens[0] == TokenView::Ident(t));
                assert(tokens[1] == TokenView::Period);
                assert(tokens[2] == TokenView::Ident(column));
                assert(tokens.subrange(3, tokens.len() as int) =~= tail);
            },
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            reveal(verified_production::parse_literal_views);
            verified_production::literal_roundtrip(l);
            let lv = verified_production::literal_views(l).unwrap();
            assert(sprint(e) == lv);
            assert(lv.len() == 1);
            assert(seq![tokens[0]] =~= lv);
            assert(tokens.drop_first() =~= tail);
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(_) => {},
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Unary(tag, inner) => {
            unary_tok_prefix(tag);
            let close_tail = seq![TokenView::CloseParen] + tail;
            let body = seq![unary_tok(tag)] + sprint(*inner) + close_tail;
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.drop_first() =~= body);
            lemma_prec(*inner, prefix_prec_s(tag), close_tail, (fuel - 2) as nat);
            assert(body[0] == unary_tok(tag));
            assert(body.drop_first() =~= sprint(*inner) + close_tail);
            prec_boundary_halts(
                SExpr::Unary(tag, inner),
                close_tail,
                0,
                (fuel - 1) as nat,
            );
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
        SExpr::Factorial(inner) => {
            sprint_head(*inner);
            let close_tail = seq![TokenView::CloseParen] + tail;
            let body = sprint(*inner) + seq![TokenView::Exclamation] + close_tail;
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.drop_first() =~= body);
            lemma_atom(*inner, seq![TokenView::Exclamation] + close_tail, (fuel - 2) as nat);
            assert(body =~= sprint(*inner) + (seq![TokenView::Exclamation] + close_tail));
            let after_inner = seq![TokenView::Exclamation] + close_tail;
            assert(after_inner[0] == TokenView::Exclamation);
            assert(after_inner.drop_first() =~= close_tail);
            postfix_step_factorial(*inner, close_tail);
            prec_boundary_halts(SExpr::Factorial(inner), close_tail, 0, (fuel - 1) as nat);
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
        SExpr::Is(inner, lit) => {
            sprint_head(*inner);
            let close_tail = seq![TokenView::CloseParen] + tail;
            let is_tail = seq![TokenView::Keyword(Keyword::Is), islit_tok(lit)] + close_tail;
            let body = sprint(*inner) + is_tail;
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.drop_first() =~= body);
            lemma_atom(*inner, is_tail, (fuel - 2) as nat);
            assert(is_tail[0] == TokenView::Keyword(Keyword::Is));
            assert(is_tail[1] == islit_tok(lit));
            assert(is_tail.subrange(2, is_tail.len() as int) =~= close_tail);
            postfix_step_is(*inner, lit, close_tail);
            prec_boundary_halts(SExpr::Is(inner, lit), close_tail, 0, (fuel - 1) as nat);
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
            match lit {
                IsLit::Null => {},
                IsLit::NaN => {},
            }
        },
        SExpr::Binary(tag, left, right) => {
            binary_tok_roundtrip(tag);
            sprint_head(*left);
            let close_tail = seq![TokenView::CloseParen] + tail;
            let right_part = seq![binary_tok(tag)] + sprint(*right) + close_tail;
            let body = sprint(*left) + right_part;
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.drop_first() =~= body);
            lemma_atom(*left, right_part, (fuel - 2) as nat);
            assert(right_part[0] == binary_tok(tag));
            assert(right_part.drop_first() =~= sprint(*right) + close_tail);
            infix_step_binary(tag, *left, *right, close_tail, (fuel - 1) as nat);
            postfix_halt(*left, right_part, 0);
            prec_boundary_halts(
                SExpr::Binary(tag, left, right),
                close_tail,
                0,
                (fuel - 1) as nat,
            );
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
        SExpr::Function(name, args) => {
            reveal(printable_se);
            let close_tail = seq![TokenView::CloseParen] + tail;
            lemma_fn_args(args, close_tail, fuel);
            assert(tokens[0] == TokenView::Ident(name));
            assert(tokens[1] == TokenView::OpenParen);
            assert(tokens.subrange(2, tokens.len() as int) =~= sprint_args(args) + close_tail);
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
    }
}

pub proof fn lemma_prec(e: SExpr, min_prec: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        prec_boundary(tail),
        fuel >= super::verified_roundtrip::sprint(e).len() + 1,
    ensures
        sparse_prec(super::verified_roundtrip::sprint(e) + tail, min_prec, fuel) == (Some(e), tail),
    decreases e, 1nat,
{
    use super::verified_roundtrip::{printable_se, sprint, sprint_head};
    reveal(printable_se);
    reveal_with_fuel(sparse_prec, 1);
    sprint_head(e);
    let tokens = sprint(e) + tail;
    assert(tokens[0] == sprint(e)[0]);
    lemma_atom(e, tail, (fuel - 1) as nat);
    prec_boundary_halts(e, tail, min_prec, fuel);
}

pub proof fn lemma_fn_args(args: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::all_printable_se(args),
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
        fuel >= super::verified_roundtrip::sprint_args(args).len() + 2,
    ensures
        sparse_fn_args(super::verified_roundtrip::sprint_args(args) + tail, fuel)
            == (Some(args), tail),
    decreases args, 1nat,
{
    use super::verified_roundtrip::{all_printable_se, sprint, sprint_args, sprint_head};
    reveal(all_printable_se);
    reveal_with_fuel(sparse_fn_args, 1);
    if args.len() == 0 {
        assert(sprint_args(args) + tail =~= tail);
        assert(Seq::<SExpr>::empty() =~= args);
    } else {
        sprint_head(args[0]);
        assert((sprint_args(args) + tail)[0] == sprint(args[0])[0]);
        lemma_fn_args_nonempty(args, tail, fuel);
    }
}

pub proof fn lemma_fn_args_nonempty(args: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::all_printable_se(args),
        args.len() > 0,
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
        fuel >= super::verified_roundtrip::sprint_args(args).len() + 2,
    ensures
        sparse_fn_args_nonempty(super::verified_roundtrip::sprint_args(args) + tail, fuel)
            == (Some(args), tail),
    decreases args, 0nat,
{
    use super::verified_roundtrip::{all_printable_se, sprint, sprint_args, sprint_head, slist_depth};
    reveal(all_printable_se);
    reveal_with_fuel(sparse_fn_args_nonempty, 1);
    if args.len() == 1 {
        lemma_prec(args[0], 0, tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + tail);
        assert(seq![args[0]] =~= args);
    } else {
        let rest = args.drop_first();
        let comma_tail = seq![TokenView::Comma] + sprint_args(rest) + tail;
        lemma_prec(args[0], 0, comma_tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + comma_tail);
        assert(comma_tail[0] == TokenView::Comma);
        assert(comma_tail.drop_first() =~= sprint_args(rest) + tail);
        lemma_fn_args_nonempty(rest, tail, (fuel - 1) as nat);
        assert(seq![args[0]] + rest =~= args);
    }
}


pub proof fn postfix_step_factorial(inner: SExpr, close_tail: Seq<TokenView>)
    requires
        close_tail.len() > 0,
        close_tail[0] == TokenView::CloseParen,
    ensures
        sparse_postfix_loop(inner, seq![TokenView::Exclamation] + close_tail, 0)
            == (SExpr::Factorial(Box::new(inner)), close_tail),
{
    reveal_with_fuel(sparse_postfix_loop, 2);
    let input = seq![TokenView::Exclamation] + close_tail;
    assert(input[0] == TokenView::Exclamation);
    assert(input.drop_first() =~= close_tail);
    postfix_halt(SExpr::Factorial(Box::new(inner)), close_tail, 0);
}

pub proof fn postfix_step_is(inner: SExpr, lit: IsLit, close_tail: Seq<TokenView>)
    requires
        close_tail.len() > 0,
        close_tail[0] == TokenView::CloseParen,
    ensures
        sparse_postfix_loop(
            inner,
            seq![TokenView::Keyword(Keyword::Is), super::verified_roundtrip::islit_tok(lit)]
                + close_tail,
            0,
        ) == (SExpr::Is(Box::new(inner), lit), close_tail),
{
    use super::verified_roundtrip::islit_tok;
    reveal_with_fuel(sparse_postfix_loop, 2);
    let input = seq![TokenView::Keyword(Keyword::Is), islit_tok(lit)] + close_tail;
    assert(input[0] == TokenView::Keyword(Keyword::Is));
    assert(input[1] == islit_tok(lit));
    assert(input.subrange(2, input.len() as int) =~= close_tail);
    assert(input[1] != TokenView::Keyword(Keyword::Not)) by {
        match lit {
            IsLit::Null => {},
            IsLit::NaN => {},
        }
    }
    match lit {
        IsLit::Null => {},
        IsLit::NaN => {},
    }
    postfix_halt(SExpr::Is(Box::new(inner), lit), close_tail, 0);
}

pub proof fn infix_step_binary(
    tag: BinaryTag,
    left: SExpr,
    right: SExpr,
    close_tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        super::verified_roundtrip::printable_se(right),
        close_tail.len() > 0,
        close_tail[0] == TokenView::CloseParen,
        fuel >= super::verified_roundtrip::sprint(right).len() + 2,
    ensures
        sparse_infix_loop(
            left,
            seq![super::verified_roundtrip::binary_tok(tag)] + super::verified_roundtrip::sprint(right)
                + close_tail,
            0,
            fuel,
        ) == (Some(SExpr::Binary(tag, Box::new(left), Box::new(right))), close_tail),
    decreases right, 2nat,
{
    use super::verified_roundtrip::{binary_tok, sprint, binary_tok_roundtrip};
    reveal_with_fuel(sparse_infix_loop, 1);
    binary_tok_roundtrip(tag);
    let input = seq![binary_tok(tag)] + sprint(right) + close_tail;
    assert(input[0] == binary_tok(tag));
    assert(input.drop_first() =~= sprint(right) + close_tail);
    let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
    lemma_prec(right, next_prec, close_tail, (fuel - 1) as nat);
    infix_halt(
        SExpr::Binary(tag, Box::new(left), Box::new(right)),
        close_tail,
        0,
        (fuel - 1) as nat,
    );
}

}
