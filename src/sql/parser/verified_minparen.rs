//! Minimal-parenthesization round-trip theorem for expressions.
//!
//! `min_roundtrip` proves the parser inverts the min-parens printer: parsing
//! `sprint_min(e, 0)` recovers `e` exactly.
//!
//! CRITICAL HEDGE: the printer's precedence tables (`bin_prec` / `bin_assoc` /
//! `pre_prec`) are *proved equal* to the parser's tables (`tables_agree`). So
//! the theorem shows "the parser inverts the printer", NOT "the parser
//! implements SQL's precedence" — a consistent permutation of ALL precedence
//! tables (a "consistent-triple-swap") would still verify this round-trip.
//! Conformance to real SQL precedence rests instead on the `cfg(test)`
//! differential oracle and the goldenscripts, not on this theorem.
//!
//! Also: the print half (`sprint_min` / `print_min_*`) is a spec/proof
//! construct and is not part of the shipped binary.

#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::float::FloatBitsProperties;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_expression::{BinaryTag, UnaryTag};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_precedence::{
    binary_assoc_s, binary_prec_s, prefix_prec_s, sparse_atom, sparse_infix_loop,
    sparse_postfix_loop, sparse_prec,
};
#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::{IsLit, SExpr};
#[allow(unused_imports)]
use super::{
    Keyword, Token, ast, float_trust, verified_expression, verified_precedence, verified_production,
};

verus! {


pub open spec fn bin_prec(tag: BinaryTag) -> u8 {
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

pub open spec fn bin_assoc(tag: BinaryTag) -> u8 {
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

pub open spec fn pre_prec(tag: UnaryTag) -> u8 {
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity => 10,
        UnaryTag::Negate => 10,
    }
}

pub open spec fn prec_min(e: SExpr) -> u8 {
    match e {
        SExpr::All => 11,
        SExpr::Column(_, _) => 11,
        SExpr::Literal(_) => 11,
        SExpr::Function(_, _) => 11,
        SExpr::Unary(tag, _) => pre_prec(tag),
        SExpr::Factorial(_) => 9,
        SExpr::Is(_, _) => 4,
        SExpr::Binary(tag, _, _) => bin_prec(tag),
    }
}

pub proof fn tables_agree(btag: BinaryTag, utag: UnaryTag)
    ensures
        bin_prec(btag) == binary_prec_s(btag),
        bin_assoc(btag) == binary_assoc_s(btag),
        pre_prec(utag) == prefix_prec_s(utag),
{
    match btag {
        BinaryTag::Or => {},
        BinaryTag::And => {},
        BinaryTag::Equal => {},
        BinaryTag::NotEqual => {},
        BinaryTag::Like => {},
        BinaryTag::GreaterThan => {},
        BinaryTag::GreaterThanOrEqual => {},
        BinaryTag::LessThan => {},
        BinaryTag::LessThanOrEqual => {},
        BinaryTag::Add => {},
        BinaryTag::Subtract => {},
        BinaryTag::Multiply => {},
        BinaryTag::Divide => {},
        BinaryTag::Remainder => {},
        BinaryTag::Exponentiate => {},
    }
    match utag {
        UnaryTag::Not => {},
        UnaryTag::Identity => {},
        UnaryTag::Negate => {},
    }
}


pub open spec fn bin_tok(tag: BinaryTag) -> TokenView {
    super::verified_roundtrip::binary_tok(tag)
}

pub open spec fn pre_tok(tag: UnaryTag) -> TokenView {
    super::verified_roundtrip::unary_tok(tag)
}

pub open spec fn sprint_body(e: SExpr) -> Seq<TokenView>
    decreases e, 0nat,
{
    match e {
        SExpr::All => seq![TokenView::Asterisk],
        SExpr::Column(None, column) => seq![TokenView::Ident(column)],
        SExpr::Column(Some(table), column) =>
            seq![TokenView::Ident(table), TokenView::Period, TokenView::Ident(column)],
        SExpr::Literal(literal) => verified_production::literal_views(literal).unwrap(),
        SExpr::Function(name, args) =>
            seq![TokenView::Ident(name), TokenView::OpenParen] + sprint_min_args(args)
                + seq![TokenView::CloseParen],
        SExpr::Unary(tag, inner) =>
            seq![pre_tok(tag)] + sprint_min(*inner, pre_prec(tag)),
        SExpr::Factorial(inner) =>
            sprint_min(*inner, 10) + seq![TokenView::Exclamation],
        SExpr::Is(inner, lit) =>
            sprint_min(*inner, 10)
                + seq![TokenView::Keyword(Keyword::Is), super::verified_roundtrip::islit_tok(lit)],
        SExpr::Binary(tag, left, right) =>
            sprint_min(*left, (bin_prec(tag) + 1 - bin_assoc(tag)) as u8) + seq![bin_tok(tag)]
                + sprint_min(*right, (bin_prec(tag) + bin_assoc(tag)) as u8),
    }
}

pub open spec fn sprint_min(e: SExpr, ctx: u8) -> Seq<TokenView>
    decreases e, 1nat,
{
    if prec_min(e) < ctx {
        seq![TokenView::OpenParen] + sprint_body(e) + seq![TokenView::CloseParen]
    } else {
        sprint_body(e)
    }
}

pub open spec fn sprint_min_args(args: Seq<SExpr>) -> Seq<TokenView>
    decreases args, 0nat,
{
    if args.len() == 0 {
        Seq::empty()
    } else if args.len() == 1 {
        sprint_min(args[0], 0)
    } else {
        sprint_min(args[0], 0) + seq![TokenView::Comma] + sprint_min_args(args.drop_first())
    }
}


pub open spec fn neutral_head(t: TokenView) -> bool {
    verified_expression::binary_from_token(t) is None
        && t != TokenView::Exclamation
        && t != TokenView::Keyword(Keyword::Is)
        && t != TokenView::Period
        && t != TokenView::OpenParen
}

pub open spec fn inert(tail: Seq<TokenView>, level: u8) -> bool {
    tail.len() == 0
        || (verified_expression::binary_from_token(tail[0]) is Some
            && binary_prec_s(verified_expression::binary_from_token(tail[0])->Some_0) < level)
        || (tail[0] == TokenView::Exclamation && 9 < level)
        || (tail[0] == TokenView::Keyword(Keyword::Is) && 8 < level)
        || tail[0] == TokenView::CloseParen
        || tail[0] == TokenView::Comma
        || neutral_head(tail[0])
}

pub proof fn inert_boundary(tail: Seq<TokenView>, level: u8)
    requires
        inert(tail, level),
    ensures
        super::verified_roundtrip::boundary(tail),
{
}

pub proof fn inert_halts(lhs: SExpr, tail: Seq<TokenView>, level: u8, fuel: nat)
    requires
        inert(tail, level),
    ensures
        sparse_infix_loop(lhs, tail, level, fuel) == (Some(lhs), tail),
        sparse_postfix_loop(lhs, tail, level) == (lhs, tail),
{
    reveal_with_fuel(sparse_infix_loop, 1);
    reveal_with_fuel(sparse_postfix_loop, 1);
    if tail.len() == 0 {
    } else {
        assert(sparse_infix_loop(lhs, tail, level, fuel) == (Some(lhs), tail)) by {
            match verified_expression::binary_from_token(tail[0]) {
                Some(tag) => { assert(binary_prec_s(tag) < level); },
                None => {},
            }
        }
        assert(sparse_postfix_loop(lhs, tail, level) == (lhs, tail));
    }
}

pub proof fn inert_mono(tail: Seq<TokenView>, level: u8, level2: u8)
    requires
        inert(tail, level),
        level <= level2,
    ensures
        inert(tail, level2),
{
}

pub proof fn boundary_inert(tail: Seq<TokenView>, level: u8)
    requires
        tail.len() == 0 || tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma,
    ensures
        inert(tail, level),
{
    if tail.len() == 0 {
    } else {
        assert(verified_expression::binary_from_token(tail[0]) is None) by {
            reveal(verified_expression::binary_from_token);
        }
    }
}


pub proof fn sprint_min_len(e: SExpr, ctx: u8)
    ensures
        sprint_min(e, ctx).len() == if prec_min(e) < ctx {
            sprint_body(e).len() + 2
        } else {
            sprint_body(e).len()
        },
{
    reveal_with_fuel(sprint_min, 1);
    if prec_min(e) < ctx {
        assert(sprint_min(e, ctx)
            == seq![TokenView::OpenParen] + sprint_body(e) + seq![TokenView::CloseParen]);
    }
}

pub proof fn sprint_body_nonempty(e: SExpr)
    requires
        super::verified_roundtrip::printable_se(e),
    ensures
        sprint_body(e).len() > 0,
    decreases e,
{
    reveal_with_fuel(sprint_body, 1);
    reveal(super::verified_roundtrip::printable_se);
    match e {
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(_) => {},
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Factorial(inner) => {
            sprint_body_nonempty(*inner);
        },
        SExpr::Is(inner, lit) => {
            sprint_body_nonempty(*inner);
        },
        _ => {},
    }
}

pub proof fn sprint_body_head_atomstart(e: SExpr)
    requires
        super::verified_roundtrip::printable_se(e),
    ensures
        sprint_body(e).len() > 0,
        sprint_body(e)[0] != TokenView::CloseParen,
    decreases e, 0nat,
{
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(sprint_min, 1);
    reveal(super::verified_roundtrip::printable_se);
    sprint_body_nonempty(e);
    match e {
        SExpr::All => {},
        SExpr::Column(t, c) => {
            match t {
                None => {},
                Some(_) => {},
            }
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(_) => {},
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Function(name, _) => {},
        SExpr::Unary(tag, inner) => {
            super::verified_roundtrip::unary_tok_prefix(tag);
            assert(sprint_body(e)[0] == pre_tok(tag));
            match tag {
                UnaryTag::Not => {},
                UnaryTag::Identity => {},
                UnaryTag::Negate => {},
            }
        },
        SExpr::Factorial(inner) => {
            sprint_min_head_not_close(*inner, 10);
            assert(sprint_body(e)[0] == sprint_min(*inner, 10)[0]);
        },
        SExpr::Is(inner, lit) => {
            sprint_min_head_not_close(*inner, 10);
            assert(sprint_body(e)[0] == sprint_min(*inner, 10)[0]);
        },
        SExpr::Binary(tag, left, right) => {
            let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
            sprint_min_head_not_close(*left, lc);
            assert(sprint_body(e)[0] == sprint_min(*left, lc)[0]);
        },
    }
}


pub open spec fn descends(l: SExpr, lc: u8) -> bool {
    l is Binary && prec_min(l) >= lc
}

pub open spec fn lleaf(e: SExpr, ctx: u8) -> SExpr
    decreases e,
{
    match e {
        SExpr::Binary(tag, left, right) => {
            let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
            if descends(*left, lc) {
                lleaf(*left, lc)
            } else {
                *left
            }
        },
        _ => e,
    }
}

pub open spec fn lleaf_ctx(e: SExpr, ctx: u8) -> u8
    decreases e,
{
    match e {
        SExpr::Binary(tag, left, right) => {
            let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
            if descends(*left, lc) {
                lleaf_ctx(*left, lc)
            } else {
                lc
            }
        },
        _ => ctx,
    }
}

pub open spec fn after_leaf(e: SExpr, ctx: u8) -> Seq<TokenView>
    decreases e,
{
    match e {
        SExpr::Binary(tag, left, right) => {
            let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
            let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
            let here = seq![bin_tok(tag)] + sprint_min(*right, rc);
            if descends(*left, lc) {
                after_leaf(*left, lc) + here
            } else {
                here
            }
        },
        _ => Seq::empty(),
    }
}

pub proof fn lemma_body_decomp(e: SExpr, ctx: u8)
    requires
        e is Binary,
    ensures
        sprint_body(e) == sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)) + after_leaf(e, ctx),
    decreases e,
{
    reveal_with_fuel(sprint_body, 1);
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
    let here = seq![bin_tok(tag)] + sprint_min(*right, rc);
    assert(sprint_body(e) == sprint_min(*left, lc) + here);
    if descends(*left, lc) {
        lemma_body_decomp(*left, lc);
        reveal_with_fuel(sprint_min, 1);
        assert(prec_min(*left) >= lc);
        assert(sprint_min(*left, lc) == sprint_body(*left));
        assert(sprint_body(*left)
            == sprint_min(lleaf(*left, lc), lleaf_ctx(*left, lc)) + after_leaf(*left, lc));
        assert(lleaf(e, ctx) == lleaf(*left, lc));
        assert(lleaf_ctx(e, ctx) == lleaf_ctx(*left, lc));
        assert(after_leaf(e, ctx) == after_leaf(*left, lc) + here);
        assert(sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)) + after_leaf(e, ctx)
            == (sprint_min(lleaf(*left, lc), lleaf_ctx(*left, lc)) + after_leaf(*left, lc)) + here);
        assert(sprint_min(*left, lc) + here
            == (sprint_min(lleaf(*left, lc), lleaf_ctx(*left, lc)) + after_leaf(*left, lc)) + here)
            by {
                assert(sprint_min(*left, lc)
                    == sprint_min(lleaf(*left, lc), lleaf_ctx(*left, lc)) + after_leaf(*left, lc));
            }
        assert(sprint_body(e) =~= sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)) + after_leaf(e, ctx));
    } else {
        assert(lleaf(e, ctx) == *left);
        assert(lleaf_ctx(e, ctx) == lc);
        assert(after_leaf(e, ctx) == here);
        assert(sprint_body(e) =~= sprint_min(*left, lc) + here);
    }
}


pub proof fn descend_gap(ptag: BinaryTag, l: SExpr)
    requires
        descends(l, (bin_prec(ptag) + 1 - bin_assoc(ptag)) as u8),
    ensures
        ({
            let ltag = l->Binary_0;
            bin_prec(ptag) < (bin_prec(ltag) + bin_assoc(ltag)) as u8
        }),
{
    let ltag = l->Binary_0;
    let bp = bin_prec(ptag);
    let assoc = bin_assoc(ptag);
    assert(prec_min(l) == bin_prec(ltag));
    let lc = (bp + 1 - assoc) as u8;
    assert(bin_prec(ltag) >= lc);
    match ltag {
        BinaryTag::Exponentiate => {
            assert(bin_prec(ltag) == 8);
            assert(bin_assoc(ltag) == 0);
            reveal_prec_assoc_link();
            if bp == 8 {
                assert(bin_assoc(ptag) == 0);
                assert(lc == 9);
                assert(false);
            }
            assert(bp < 8);
        },
        _ => {
            assert(bin_assoc(ltag) == 1);
            assert(bin_prec(ltag) + 1 >= lc + 1);
        },
    }
}

pub proof fn reveal_prec_assoc_link()
    ensures
        forall|t: BinaryTag| #[trigger] bin_prec(t) == 8 ==> bin_assoc(t) == 0,
        forall|t: BinaryTag| #[trigger] bin_assoc(t) == 0 ==> bin_prec(t) == 8,
{
    assert forall|t: BinaryTag| #[trigger] bin_prec(t) == 8 implies bin_assoc(t) == 0 by {
        match t {
            BinaryTag::Exponentiate => {},
            _ => {},
        }
    }
    assert forall|t: BinaryTag| #[trigger] bin_assoc(t) == 0 implies bin_prec(t) == 8 by {
        match t {
            BinaryTag::Exponentiate => {},
            _ => {},
        }
    }
}


pub proof fn lemma_min(e: SExpr, ctx: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        inert(tail, ctx),
        fuel >= 2 * (sprint_min(e, ctx) + tail).len() + 3,
    ensures
        sparse_prec(sprint_min(e, ctx) + tail, ctx, fuel) == (Some(e), tail),
    decreases super::verified_roundtrip::sdepth(e), 8nat,
{
    reveal_with_fuel(sprint_min, 1);
    sprint_min_len(e, ctx);
    sprint_body_nonempty(e);
    if prec_min(e) < ctx {
        reveal_with_fuel(sparse_prec, 1);
        reveal_with_fuel(sparse_atom, 1);
        let close_tail = seq![TokenView::CloseParen] + tail;
        let body = sprint_body(e) + close_tail;
        let input = sprint_min(e, ctx) + tail;
        assert(input =~= seq![TokenView::OpenParen] + body);
        assert(input[0] == TokenView::OpenParen);
        assert(verified_expression::prefix_operator(input[0]) is None) by {
            reveal(verified_expression::prefix_operator);
        }
        assert(input.drop_first() =~= body);
        boundary_inert(close_tail, 0);
        assert(prec_min(e) >= 0);
        lemma_body(e, 0, close_tail, (fuel - 2) as nat);
        assert(sparse_prec(body, 0, (fuel - 2) as nat) == (Some(e), close_tail));
        assert(close_tail[0] == TokenView::CloseParen);
        assert(close_tail.drop_first() =~= tail);
        assert(sparse_atom(input, (fuel - 1) as nat) == (Some(e), tail));
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
            == sparse_atom(input, (fuel - 1) as nat));
        inert_halts(e, tail, ctx, fuel);
        prec_from_lhs(input, ctx, fuel, e, tail);
        assert(final_result_expr(input, ctx, fuel, e, tail) == e) by {
            inert_halts(e, tail, ctx, fuel);
        }
        assert(final_result_rest(input, ctx, fuel, e, tail) == tail) by {
            inert_halts(e, tail, ctx, fuel);
        }
    } else {
        assert(sprint_min(e, ctx) == sprint_body(e));
        lemma_body(e, ctx, tail, fuel);
    }
}

pub proof fn lemma_body(e: SExpr, ctx: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        prec_min(e) >= ctx,
        inert(tail, ctx),
        fuel >= 2 * (sprint_body(e) + tail).len() + 3,
    ensures
        sparse_prec(sprint_body(e) + tail, ctx, fuel) == (Some(e), tail),
    decreases super::verified_roundtrip::sdepth(e), 7nat,
{
    reveal(super::verified_roundtrip::printable_se);
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(sparse_prec, 1);
    reveal_with_fuel(sparse_atom, 1);
    sprint_body_nonempty(e);
    let input = sprint_body(e) + tail;
    match e {
        SExpr::All | SExpr::Column(_, _) | SExpr::Literal(_) | SExpr::Function(_, _) => {
            assert(verified_expression::prefix_operator(input[0]) is None) by {
                reveal(verified_expression::prefix_operator);
                sprint_body_atom_head(e);
            }
            inert_boundary(tail, ctx);
            lemma_atom_min(e, tail, (fuel - 1) as nat);
            inert_halts(e, tail, ctx, fuel);
        },
        SExpr::Unary(tag, inner) => {
            super::verified_roundtrip::unary_tok_prefix(tag);
            assert(pre_prec(tag) == prefix_prec_s(tag)) by { tables_agree(BinaryTag::Or, tag); }
            assert(input[0] == pre_tok(tag));
            assert(pre_tok(tag) == super::verified_roundtrip::unary_tok(tag));
            assert(verified_expression::prefix_operator(input[0]) == Some(tag));
            assert(prec_min(e) == pre_prec(tag));
            assert(prefix_prec_s(tag) >= ctx);
            assert(input.drop_first() =~= sprint_min(*inner, pre_prec(tag)) + tail);
            inert_mono(tail, ctx, pre_prec(tag));
            sprint_min_len(*inner, pre_prec(tag));
            lemma_min(*inner, pre_prec(tag), tail, (fuel - 1) as nat);
            inert_halts(e, tail, ctx, fuel);
        },
        SExpr::Factorial(inner) => {
            let post = seq![TokenView::Exclamation] + tail;
            assert(prec_min(e) == 9);
            assert(9 >= ctx);
            assert(input =~= sprint_min(*inner, 10) + post);
            assert(inert(post, 10)) by { assert(post[0] == TokenView::Exclamation); }
            sprint_min_len(*inner, 10);
            lemma_lhs_high(*inner, ctx, post, fuel);
            postfix_step_min_factorial(*inner, tail, ctx);
            inert_halts(SExpr::Factorial(inner), tail, ctx, fuel);
        },
        SExpr::Is(inner, lit) => {
            let post = seq![TokenView::Keyword(Keyword::Is),
                super::verified_roundtrip::islit_tok(lit)] + tail;
            assert(prec_min(e) == 4);
            assert(4 >= ctx);
            assert(input =~= sprint_min(*inner, 10) + post);
            assert(inert(post, 10)) by { assert(post[0] == TokenView::Keyword(Keyword::Is)); }
            sprint_min_len(*inner, 10);
            lemma_lhs_high(*inner, ctx, post, fuel);
            postfix_step_min_is(*inner, lit, tail, ctx);
            inert_halts(SExpr::Is(inner, lit), tail, ctx, fuel);
        },
        SExpr::Binary(tag, left, right) => {
            lemma_body_binary(tag, *left, *right, ctx, tail, fuel);
        },
    }
}


pub proof fn sprint_body_atom_head(e: SExpr)
    requires
        super::verified_roundtrip::printable_se(e),
        e is All || e is Column || e is Literal || e is Function,
    ensures
        sprint_body(e).len() > 0,
        verified_expression::prefix_operator(sprint_body(e)[0]) is None,
    decreases e,
{
    reveal_with_fuel(sprint_body, 1);
    reveal(super::verified_roundtrip::printable_se);
    reveal(verified_expression::prefix_operator);
    sprint_body_nonempty(e);
    match e {
        SExpr::All => { assert(sprint_body(e)[0] == TokenView::Asterisk); },
        SExpr::Column(t, c) => {
            match t {
                None => { assert(sprint_body(e)[0] == TokenView::Ident(c)); },
                Some(tt) => { assert(sprint_body(e)[0] == TokenView::Ident(tt)); },
            }
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(_) => {},
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Function(name, _) => { assert(sprint_body(e)[0] == TokenView::Ident(name)); },
        _ => {},
    }
}

pub proof fn lemma_atom_min(e: SExpr, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        e is All || e is Column || e is Literal || e is Function,
        super::verified_roundtrip::boundary(tail),
        fuel >= 2 * (sprint_body(e) + tail).len() + 2,
    ensures
        sparse_atom(sprint_body(e) + tail, fuel) == (Some(e), tail),
    decreases super::verified_roundtrip::sdepth(e), 2nat,
{
    reveal_with_fuel(sparse_atom, 1);
    reveal_with_fuel(sprint_body, 1);
    reveal(super::verified_roundtrip::printable_se);
    sprint_body_nonempty(e);
    let tokens = sprint_body(e) + tail;
    match e {
        SExpr::All => {
            assert(tokens[0] == TokenView::Asterisk);
            assert(tokens.drop_first() =~= tail);
        },
        SExpr::Column(table, column) => match table {
            None => {
                assert(tokens[0] == TokenView::Ident(column));
                if tokens.len() >= 2 { assert(tokens[1] == tail[0]); }
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
            assert(sprint_body(e) == lv);
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
        SExpr::Function(name, args) => {
            let close_tail = seq![TokenView::CloseParen] + tail;
            assert(tokens[0] == TokenView::Ident(name));
            assert(tokens[1] == TokenView::OpenParen);
            assert(tokens.subrange(2, tokens.len() as int) =~= sprint_min_args(args) + close_tail);
            lemma_min_args(args, close_tail, fuel);
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
        _ => {},
    }
}

pub proof fn lemma_min_args(args: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::all_printable_se(args),
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
        fuel >= 2 * (sprint_min_args(args) + tail).len() + 4,
    ensures
        verified_precedence::sparse_fn_args(sprint_min_args(args) + tail, fuel) == (Some(args), tail),
    decreases super::verified_roundtrip::slist_depth(args), 1nat,
{
    reveal_with_fuel(verified_precedence::sparse_fn_args, 1);
    reveal_with_fuel(sprint_min_args, 1);
    reveal(super::verified_roundtrip::all_printable_se);
    if args.len() == 0 {
        assert(sprint_min_args(args) + tail =~= tail);
        assert(Seq::<SExpr>::empty() =~= args);
    } else {
        sprint_body_nonempty(args[0]);
        min_args_head(args);
        lemma_min_args_nonempty(args, tail, fuel);
    }
}

pub proof fn min_args_head(args: Seq<SExpr>)
    requires
        super::verified_roundtrip::all_printable_se(args),
        args.len() > 0,
    ensures
        (sprint_min_args(args)).len() > 0,
        (sprint_min_args(args))[0] != TokenView::CloseParen,
{
    reveal_with_fuel(sprint_min_args, 1);
    reveal_with_fuel(sprint_min, 1);
    reveal(super::verified_roundtrip::all_printable_se);
    sprint_body_nonempty(args[0]);
    sprint_min_len(args[0], 0);
    assert(sprint_min(args[0], 0) == sprint_body(args[0]));
    sprint_min_head_not_close(args[0], 0);
    if args.len() == 1 {
        assert(sprint_min_args(args) == sprint_min(args[0], 0));
    } else {
        assert(sprint_min_args(args)[0] == sprint_min(args[0], 0)[0]);
    }
}

pub proof fn sprint_min_head_not_close(e: SExpr, ctx: u8)
    requires
        super::verified_roundtrip::printable_se(e),
    ensures
        sprint_min(e, ctx).len() > 0,
        sprint_min(e, ctx)[0] != TokenView::CloseParen,
    decreases e, 1nat,
{
    reveal_with_fuel(sprint_min, 1);
    sprint_min_len(e, ctx);
    sprint_body_nonempty(e);
    if prec_min(e) < ctx {
        assert(sprint_min(e, ctx)[0] == TokenView::OpenParen);
    } else {
        assert(sprint_min(e, ctx) == sprint_body(e));
        sprint_body_head_atomstart(e);
    }
}

pub proof fn lemma_min_args_nonempty(args: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::all_printable_se(args),
        args.len() > 0,
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
        fuel >= 2 * (sprint_min_args(args) + tail).len() + 4,
    ensures
        verified_precedence::sparse_fn_args_nonempty(sprint_min_args(args) + tail, fuel)
            == (Some(args), tail),
    decreases super::verified_roundtrip::slist_depth(args), 0nat,
{
    reveal_with_fuel(verified_precedence::sparse_fn_args_nonempty, 1);
    reveal_with_fuel(sprint_min_args, 1);
    reveal(super::verified_roundtrip::all_printable_se);
    if args.len() == 1 {
        boundary_inert(tail, 0);
        sprint_min_len(args[0], 0);
        min_args_len(args);
        lemma_min(args[0], 0, tail, (fuel - 1) as nat);
        assert(sprint_min_args(args) + tail =~= sprint_min(args[0], 0) + tail);
        assert(seq![args[0]] =~= args);
    } else {
        let rest = args.drop_first();
        let comma_tail = seq![TokenView::Comma] + sprint_min_args(rest) + tail;
        boundary_inert(comma_tail, 0);
        sprint_min_len(args[0], 0);
        min_args_len(args);
        lemma_min(args[0], 0, comma_tail, (fuel - 1) as nat);
        assert(sprint_min_args(args) + tail =~= sprint_min(args[0], 0) + comma_tail);
        assert(comma_tail[0] == TokenView::Comma);
        assert(comma_tail.drop_first() =~= sprint_min_args(rest) + tail);
        lemma_min_args_nonempty(rest, tail, (fuel - 1) as nat);
        assert(seq![args[0]] + rest =~= args);
    }
}

pub proof fn min_args_len(args: Seq<SExpr>)
    requires
        args.len() > 0,
    ensures
        args.len() == 1 ==> sprint_min_args(args).len() == sprint_min(args[0], 0).len(),
        args.len() > 1 ==> sprint_min_args(args).len()
            == sprint_min(args[0], 0).len() + 1 + sprint_min_args(args.drop_first()).len(),
{
    reveal_with_fuel(sprint_min_args, 1);
}


pub proof fn prec_from_lhs(
    input: Seq<TokenView>,
    ctx: u8,
    fuel: nat,
    lhs0: SExpr,
    after: Seq<TokenView>,
)
    requires
        fuel > 0,
        input.len() > 0,
        verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(lhs0), after),
        ({
            let (lhs1, cur1) = sparse_postfix_loop(lhs0, after, ctx);
            &&& sparse_infix_loop(lhs1, cur1, ctx, fuel).0 is Some
            &&& ({
                let (lhs2, cur2) = (sparse_infix_loop(lhs1, cur1, ctx, fuel).0->Some_0,
                    sparse_infix_loop(lhs1, cur1, ctx, fuel).1);
                sparse_postfix_loop(lhs2, cur2, ctx)
                    == (final_result_expr(input, ctx, fuel, lhs0, after),
                        final_result_rest(input, ctx, fuel, lhs0, after))
            })
        }),
    ensures
        sparse_prec(input, ctx, fuel)
            == (Some(final_result_expr(input, ctx, fuel, lhs0, after)),
                final_result_rest(input, ctx, fuel, lhs0, after)),
{
    reveal_with_fuel(sparse_prec, 1);
}

pub open spec fn final_result_expr(
    input: Seq<TokenView>,
    ctx: u8,
    fuel: nat,
    lhs0: SExpr,
    after: Seq<TokenView>,
) -> SExpr {
    let (lhs1, cur1) = sparse_postfix_loop(lhs0, after, ctx);
    let (lhs2, cur2) = (sparse_infix_loop(lhs1, cur1, ctx, fuel).0->Some_0,
        sparse_infix_loop(lhs1, cur1, ctx, fuel).1);
    sparse_postfix_loop(lhs2, cur2, ctx).0
}

pub open spec fn final_result_rest(
    input: Seq<TokenView>,
    ctx: u8,
    fuel: nat,
    lhs0: SExpr,
    after: Seq<TokenView>,
) -> Seq<TokenView> {
    let (lhs1, cur1) = sparse_postfix_loop(lhs0, after, ctx);
    let (lhs2, cur2) = (sparse_infix_loop(lhs1, cur1, ctx, fuel).0->Some_0,
        sparse_infix_loop(lhs1, cur1, ctx, fuel).1);
    sparse_postfix_loop(lhs2, cur2, ctx).1
}

pub proof fn lemma_lhs_high(inner: SExpr, ctx: u8, rest: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(inner),
        ctx <= 10,
        inert(rest, 10),
        fuel >= 2 * (sprint_min(inner, 10) + rest).len() + 3,
    ensures
        verified_precedence::prec_lhs_phase(sprint_min(inner, 10) + rest, ctx, fuel)
            == (Some(inner), rest),
    decreases super::verified_roundtrip::sdepth(inner), 11nat,
{
    reveal_with_fuel(sprint_min, 1);
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(sparse_prec, 1);
    reveal_with_fuel(sparse_atom, 1);
    reveal(super::verified_roundtrip::printable_se);
    sprint_min_len(inner, 10);
    sprint_body_nonempty(inner);
    let smin = sprint_min(inner, 10);
    let input = smin + rest;
    if prec_min(inner) < 10 {
        let close_tail = seq![TokenView::CloseParen] + rest;
        let body = sprint_body(inner) + close_tail;
        assert(smin == seq![TokenView::OpenParen] + sprint_body(inner) + seq![TokenView::CloseParen]);
        assert(input =~= seq![TokenView::OpenParen] + body);
        assert(input[0] == TokenView::OpenParen);
        assert(verified_expression::prefix_operator(input[0]) is None) by {
            reveal(verified_expression::prefix_operator);
        }
        assert(input.drop_first() =~= body);
        boundary_inert(close_tail, 0);
        lemma_body(inner, 0, close_tail, (fuel - 2) as nat);
        assert(close_tail[0] == TokenView::CloseParen);
        assert(close_tail.drop_first() =~= rest);
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
            == sparse_atom(input, (fuel - 1) as nat));
    } else {
        assert(smin == sprint_body(inner));
        match inner {
            SExpr::All | SExpr::Column(_, _) | SExpr::Literal(_) | SExpr::Function(_, _) => {
                assert(verified_expression::prefix_operator(input[0]) is None) by {
                    reveal(verified_expression::prefix_operator);
                    sprint_body_atom_head(inner);
                }
                inert_boundary(rest, 10);
                lemma_atom_min(inner, rest, (fuel - 1) as nat);
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
                    == sparse_atom(input, (fuel - 1) as nat));
            },
            SExpr::Unary(tag, x) => {
                assert(prec_min(inner) == pre_prec(tag));
                assert(pre_prec(tag) == 10);
                super::verified_roundtrip::unary_tok_prefix(tag);
                assert(pre_prec(tag) == prefix_prec_s(tag)) by { tables_agree(BinaryTag::Or, tag); }
                assert(input[0] == pre_tok(tag));
                assert(input[0] == super::verified_roundtrip::unary_tok(tag));
                assert(verified_expression::prefix_operator(input[0]) == Some(tag));
                assert(prefix_prec_s(tag) >= ctx);
                assert(input.drop_first() =~= sprint_min(*x, 10) + rest);
                sprint_min_len(*x, 10);
                lemma_min(*x, 10, rest, (fuel - 1) as nat);
                assert(sparse_prec(sprint_min(*x, 10) + rest, prefix_prec_s(tag), (fuel - 1) as nat)
                    == (Some(*x), rest));
            },
            SExpr::Factorial(_) | SExpr::Is(_, _) | SExpr::Binary(_, _, _) => {
                assert(false);
            },
        }
    }
}

pub proof fn postfix_step_min_factorial(inner: SExpr, tail: Seq<TokenView>, ctx: u8)
    requires
        ctx <= 9,
        inert(tail, ctx),
    ensures
        sparse_postfix_loop(inner, seq![TokenView::Exclamation] + tail, ctx)
            == (SExpr::Factorial(Box::new(inner)), tail),
{
    reveal_with_fuel(sparse_postfix_loop, 2);
    let input = seq![TokenView::Exclamation] + tail;
    assert(input[0] == TokenView::Exclamation);
    assert(9 >= ctx);
    assert(input.drop_first() =~= tail);
    inert_halts(SExpr::Factorial(Box::new(inner)), tail, ctx, 0);
}

pub proof fn postfix_step_min_is(inner: SExpr, lit: IsLit, tail: Seq<TokenView>, ctx: u8)
    requires
        ctx <= 4,
        inert(tail, ctx),
    ensures
        sparse_postfix_loop(
            inner,
            seq![TokenView::Keyword(Keyword::Is), super::verified_roundtrip::islit_tok(lit)] + tail,
            ctx,
        ) == (SExpr::Is(Box::new(inner), lit), tail),
{
    use super::verified_roundtrip::islit_tok;
    reveal_with_fuel(sparse_postfix_loop, 2);
    let input = seq![TokenView::Keyword(Keyword::Is), islit_tok(lit)] + tail;
    assert(input[0] == TokenView::Keyword(Keyword::Is));
    assert(input[1] == islit_tok(lit));
    assert(4 >= ctx);
    assert(input[1] != TokenView::Keyword(Keyword::Not)) by {
        match lit {
            IsLit::Null => {},
            IsLit::NaN => {},
        }
    }
    assert(input.subrange(2, input.len() as int) =~= tail);
    match lit {
        IsLit::Null => {},
        IsLit::NaN => {},
    }
    inert_halts(SExpr::Is(Box::new(inner), lit), tail, ctx, 0);
}


pub proof fn lemma_body_binary(
    tag: BinaryTag,
    left: SExpr,
    right: SExpr,
    ctx: u8,
    tail: Seq<TokenView>,
    fuel: nat,
)
    requires
        super::verified_roundtrip::printable_se(SExpr::Binary(tag, Box::new(left), Box::new(right))),
        bin_prec(tag) >= ctx,
        inert(tail, ctx),
        fuel >= 2 * (sprint_body(SExpr::Binary(tag, Box::new(left), Box::new(right))) + tail).len() + 3,
    ensures
        sparse_prec(sprint_body(SExpr::Binary(tag, Box::new(left), Box::new(right))) + tail, ctx, fuel)
            == (Some(SExpr::Binary(tag, Box::new(left), Box::new(right))), tail),
    decreases super::verified_roundtrip::sdepth(SExpr::Binary(tag, Box::new(left), Box::new(right))), 6nat,
{
    let e = SExpr::Binary(tag, Box::new(left), Box::new(right));
    lemma_body_leaf_then_spine(e, ctx, tail, fuel);
}

pub proof fn body_binary_len(e: SExpr, ctx: u8, tail: Seq<TokenView>)
    requires
        e is Binary,
    ensures
        sprint_body(e).len()
            == sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)).len() + after_leaf(e, ctx).len(),
{
    lemma_body_decomp(e, ctx);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
pub proof fn lemma_leaf_parse(leaf: SExpr, leaf_ctx: u8, ctx: u8, rest: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(leaf),
        !descends(leaf, leaf_ctx),
        ctx <= leaf_ctx,
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
            || neutral_head(rest[0]),
        !(leaf is Unary)
            || prec_min(leaf) < leaf_ctx
            || rest.len() == 0
            || verified_expression::binary_from_token(rest[0]) is None
            || binary_prec_s(verified_expression::binary_from_token(rest[0])->Some_0)
                < prec_min(leaf),
        fuel >= 2 * (sprint_min(leaf, leaf_ctx) + rest).len() + 3,
    ensures
        ({
            let lp = verified_precedence::prec_lhs_phase(sprint_min(leaf, leaf_ctx) + rest, ctx, fuel);
            &&& lp.0 is Some
            &&& sparse_postfix_loop(lp.0->Some_0, lp.1, ctx) == (leaf, rest)
        }),
    decreases super::verified_roundtrip::sdepth(leaf), 10nat,
{
    reveal_with_fuel(sprint_min, 1);
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(sparse_prec, 1);
    reveal_with_fuel(sparse_atom, 1);
    reveal(super::verified_roundtrip::printable_se);
    sprint_min_len(leaf, leaf_ctx);
    sprint_body_nonempty(leaf);
    let input = sprint_min(leaf, leaf_ctx) + rest;
    assert(rest_halts_postfix(rest)) by {
        if rest.len() > 0 {
            match verified_expression::binary_from_token(rest[0]) {
                Some(t) => { super::verified_roundtrip::binary_tok_roundtrip(t); },
                None => {},
            }
        }
    }
    if prec_min(leaf) < leaf_ctx {
        let close_tail = seq![TokenView::CloseParen] + rest;
        let body = sprint_body(leaf) + close_tail;
        assert(input =~= seq![TokenView::OpenParen] + body);
        assert(input[0] == TokenView::OpenParen);
        assert(verified_expression::prefix_operator(input[0]) is None) by {
            reveal(verified_expression::prefix_operator);
        }
        assert(input.drop_first() =~= body);
        boundary_inert(close_tail, 0);
        lemma_body(leaf, 0, close_tail, (fuel - 2) as nat);
        assert(close_tail[0] == TokenView::CloseParen);
        assert(close_tail.drop_first() =~= rest);
        assert(sparse_atom(input, (fuel - 1) as nat) == (Some(leaf), rest));
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
            == sparse_atom(input, (fuel - 1) as nat));
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(leaf), rest));
        leaf_postfix_halts(leaf, rest, ctx);
    } else {
        assert(sprint_min(leaf, leaf_ctx) == sprint_body(leaf));
        match leaf {
            SExpr::All | SExpr::Column(_, _) | SExpr::Literal(_) | SExpr::Function(_, _) => {
                assert(verified_expression::prefix_operator(input[0]) is None) by {
                    reveal(verified_expression::prefix_operator);
                    sprint_body_atom_head(leaf);
                }
                atom_boundary_from_rest(rest);
                lemma_atom_min(leaf, rest, (fuel - 1) as nat);
                assert(sparse_atom(input, (fuel - 1) as nat) == (Some(leaf), rest));
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
                    == sparse_atom(input, (fuel - 1) as nat));
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(leaf), rest));
                leaf_postfix_halts(leaf, rest, ctx);
            },
            SExpr::Unary(tag, x) => {
                super::verified_roundtrip::unary_tok_prefix(tag);
                assert(pre_prec(tag) == prefix_prec_s(tag)) by { tables_agree(BinaryTag::Or, tag); }
                assert(input[0] == pre_tok(tag));
                assert(input[0] == super::verified_roundtrip::unary_tok(tag));
                assert(verified_expression::prefix_operator(input[0]) == Some(tag));
                assert(prec_min(leaf) == pre_prec(tag));
                assert(pre_prec(tag) >= leaf_ctx >= ctx);
                assert(prefix_prec_s(tag) >= ctx);
                assert(input.drop_first() =~= sprint_min(*x, pre_prec(tag)) + rest);
                leaf_rest_inert(rest, pre_prec(tag));
                sprint_min_len(*x, pre_prec(tag));
                lemma_min(*x, pre_prec(tag), rest, (fuel - 1) as nat);
                assert(sparse_prec(sprint_min(*x, pre_prec(tag)) + rest, prefix_prec_s(tag),
                    (fuel - 1) as nat) == (Some(*x), rest));
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(leaf), rest));
                leaf_postfix_halts(leaf, rest, ctx);
            },
            SExpr::Factorial(inner) => {
                let post = seq![TokenView::Exclamation] + rest;
                assert(input =~= sprint_min(*inner, 10) + post);
                assert(prec_min(leaf) == 9);
                assert(ctx <= 9);
                rest_post_inert(rest, TokenView::Exclamation);
                assert(inert(post, 10)) by { assert(post[0] == TokenView::Exclamation); }
                sprint_min_len(*inner, 10);
                lemma_lhs_high(*inner, ctx, post, fuel);
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(*inner), post));
                leaf_postfix_factorial(*inner, rest, ctx);
                assert(sparse_postfix_loop(*inner, post, ctx) == (leaf, rest));
            },
            SExpr::Is(inner, lit) => {
                let post = seq![TokenView::Keyword(Keyword::Is),
                    super::verified_roundtrip::islit_tok(lit)] + rest;
                assert(input =~= sprint_min(*inner, 10) + post);
                assert(prec_min(leaf) == 4);
                assert(ctx <= 4);
                rest_post_inert(rest, TokenView::Keyword(Keyword::Is));
                assert(inert(post, 10)) by { assert(post[0] == TokenView::Keyword(Keyword::Is)); }
                sprint_min_len(*inner, 10);
                lemma_lhs_high(*inner, ctx, post, fuel);
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(*inner), post));
                leaf_postfix_is(*inner, lit, rest, ctx);
                assert(sparse_postfix_loop(*inner, post, ctx) == (leaf, rest));
            },
            SExpr::Binary(_, _, _) => {
                assert(descends(leaf, leaf_ctx));
                assert(false);
            },
        }
    }
}

pub open spec fn rest_halts_postfix(rest: Seq<TokenView>) -> bool {
    rest.len() == 0
        || (rest[0] != TokenView::Exclamation && rest[0] != TokenView::Keyword(Keyword::Is))
}

pub proof fn leaf_postfix_halts(leaf: SExpr, rest: Seq<TokenView>, ctx: u8)
    requires
        rest_halts_postfix(rest),
    ensures
        sparse_postfix_loop(leaf, rest, ctx) == (leaf, rest),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
}

pub proof fn leaf_postfix_factorial(inner: SExpr, rest: Seq<TokenView>, ctx: u8)
    requires
        ctx <= 9,
        rest_halts_postfix(rest),
    ensures
        sparse_postfix_loop(inner, seq![TokenView::Exclamation] + rest, ctx)
            == (SExpr::Factorial(Box::new(inner)), rest),
{
    reveal_with_fuel(sparse_postfix_loop, 2);
    let s = seq![TokenView::Exclamation] + rest;
    assert(s[0] == TokenView::Exclamation);
    assert(9 >= ctx);
    assert(s.drop_first() =~= rest);
    leaf_postfix_halts(SExpr::Factorial(Box::new(inner)), rest, ctx);
}

pub proof fn leaf_postfix_is(inner: SExpr, lit: IsLit, rest: Seq<TokenView>, ctx: u8)
    requires
        ctx <= 4,
        rest_halts_postfix(rest),
    ensures
        sparse_postfix_loop(
            inner,
            seq![TokenView::Keyword(Keyword::Is), super::verified_roundtrip::islit_tok(lit)] + rest,
            ctx,
        ) == (SExpr::Is(Box::new(inner), lit), rest),
{
    use super::verified_roundtrip::islit_tok;
    reveal_with_fuel(sparse_postfix_loop, 2);
    let s = seq![TokenView::Keyword(Keyword::Is), islit_tok(lit)] + rest;
    assert(s[0] == TokenView::Keyword(Keyword::Is));
    assert(s[1] == islit_tok(lit));
    assert(4 >= ctx);
    assert(s[1] != TokenView::Keyword(Keyword::Not)) by {
        match lit { IsLit::Null => {}, IsLit::NaN => {} }
    }
    assert(s.subrange(2, s.len() as int) =~= rest);
    match lit { IsLit::Null => {}, IsLit::NaN => {} }
    leaf_postfix_halts(SExpr::Is(Box::new(inner), lit), rest, ctx);
}

pub proof fn rest_post_inert(rest: Seq<TokenView>, op: TokenView)
    requires
        rest_halts_postfix(rest),
        op == TokenView::Exclamation || op == TokenView::Keyword(Keyword::Is),
    ensures
        inert(seq![op] + rest, 10),
{
    assert((seq![op] + rest)[0] == op);
}

pub proof fn rest_inert_high(rest: Seq<TokenView>, level: u8)
    requires
        level >= 9,
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
            || neutral_head(rest[0]),
    ensures
        inert(rest, level),
{
    if rest.len() > 0 {
        match verified_expression::binary_from_token(rest[0]) {
            Some(t) => {
                binary_prec_le_8(t);
                assert(binary_prec_s(t) <= 8);
                super::verified_roundtrip::binary_tok_roundtrip(t);
            },
            None => {
                reveal(verified_expression::binary_from_token);
            },
        }
    }
}

pub proof fn leaf_rest_inert(rest: Seq<TokenView>, level: u8)
    requires
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
            || neutral_head(rest[0]),
        rest.len() == 0
            || verified_expression::binary_from_token(rest[0]) is None
            || binary_prec_s(verified_expression::binary_from_token(rest[0])->Some_0) < level,
    ensures
        inert(rest, level),
{
    if rest.len() > 0 {
        match verified_expression::binary_from_token(rest[0]) {
            Some(t) => {
                super::verified_roundtrip::binary_tok_roundtrip(t);
                assert(binary_prec_s(t) < level);
            },
            None => {
                reveal(verified_expression::binary_from_token);
            },
        }
    }
}

pub proof fn binary_prec_le_8(t: BinaryTag)
    ensures
        binary_prec_s(t) <= 8,
{
    tables_agree(t, UnaryTag::Not);
    match t {
        BinaryTag::Exponentiate => {},
        _ => {},
    }
}

pub proof fn inert_shape(tail: Seq<TokenView>, level: u8)
    requires
        inert(tail, level),
        level <= 8,
    ensures
        tail.len() == 0
            || (verified_expression::binary_from_token(tail[0]) is Some
                && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
            || (tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma)
            || neutral_head(tail[0]),
{
    if tail.len() > 0 {
        match verified_expression::binary_from_token(tail[0]) {
            Some(t) => { super::verified_roundtrip::binary_tok_roundtrip(t); },
            None => {},
        }
    }
}

pub proof fn leaf_gap(e: SExpr, ctx: u8)
    requires
        e is Binary,
        lleaf(e, ctx) is Unary,
        prec_min(lleaf(e, ctx)) >= lleaf_ctx(e, ctx),
    ensures
        ({
            let s = after_leaf(e, ctx);
            s.len() == 0
                || verified_expression::binary_from_token(s[0]) is None
                || binary_prec_s(verified_expression::binary_from_token(s[0])->Some_0)
                    < prec_min(lleaf(e, ctx))
        }),
    decreases e,
{
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
    let here = seq![bin_tok(tag)] + sprint_min(*right, rc);
    super::verified_roundtrip::binary_tok_roundtrip(tag);
    if descends(*left, lc) {
        assert(lleaf(e, ctx) == lleaf(*left, lc));
        assert(lleaf_ctx(e, ctx) == lleaf_ctx(*left, lc));
        assert(after_leaf(e, ctx) =~= after_leaf(*left, lc) + here);
        leaf_gap(*left, lc);
        if after_leaf(*left, lc).len() == 0 {
            after_leaf_empty_iff(*left, lc);
            assert(lleaf(*left, lc) == *left);
            assert(false);
        }
        assert(after_leaf(e, ctx)[0] == after_leaf(*left, lc)[0]);
    } else {
        assert(lleaf(e, ctx) == *left);
        assert(lleaf_ctx(e, ctx) == lc);
        assert(after_leaf(e, ctx)[0] == bin_tok(tag));
        assert(binary_prec_s(tag) == bin_prec(tag)) by { tables_agree(tag, UnaryTag::Not); }
        assert(prec_min(*left) >= lc);
        assert(*left is Unary);
        let utag = (*left)->Unary_0;
        assert(prec_min(*left) == pre_prec(utag));
        assert(pre_prec(utag) == 3 || pre_prec(utag) == 10) by {
            match utag { UnaryTag::Not => {}, UnaryTag::Identity => {}, UnaryTag::Negate => {} }
        }
        assert(bin_prec(tag) <= 8) by { binary_prec_le_8_direct(tag); }
        if pre_prec(utag) == 3 {
            assert(bin_assoc(tag) == 0 || bin_assoc(tag) == 1) by {
                match tag { BinaryTag::Exponentiate => {}, _ => {} }
            }
            no_binary_prec_3(tag);
            assert(bin_prec(tag) < 3);
        }
    }
}

pub proof fn lleaf_sdepth(e: SExpr, ctx: u8)
    requires
        e is Binary,
    ensures
        super::verified_roundtrip::sdepth(lleaf(e, ctx)) < super::verified_roundtrip::sdepth(e),
    decreases e,
{
    use super::verified_roundtrip::sdepth;
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    assert(sdepth(*left) < sdepth(e));
    if descends(*left, lc) {
        lleaf_sdepth(*left, lc);
        assert(lleaf(e, ctx) == lleaf(*left, lc));
    } else {
        assert(lleaf(e, ctx) == *left);
    }
}

pub proof fn after_leaf_empty_iff(e: SExpr, ctx: u8)
    ensures
        (after_leaf(e, ctx).len() == 0) == !(e is Binary),
{
    match e {
        SExpr::Binary(tag, left, right) => {
            let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
            let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
            sprint_min_len(*right, rc);
            assert(after_leaf(e, ctx).len() >= 1);
        },
        _ => {},
    }
}

pub proof fn no_binary_prec_3(t: BinaryTag)
    ensures
        bin_prec(t) != 3,
{
    match t { BinaryTag::Exponentiate => {}, _ => {} }
}

pub proof fn binary_prec_le_8_direct(t: BinaryTag)
    ensures
        bin_prec(t) <= 8,
{
    match t { BinaryTag::Exponentiate => {}, _ => {} }
}

pub proof fn atom_boundary_from_rest(rest: Seq<TokenView>)
    requires
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
            || neutral_head(rest[0]),
    ensures
        super::verified_roundtrip::boundary(rest),
{
}

pub proof fn lemma_body_leaf_then_spine(e: SExpr, ctx: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        e is Binary,
        prec_min(e) >= ctx,
        inert(tail, ctx),
        fuel >= 2 * (sprint_body(e) + tail).len() + 3,
    ensures
        sparse_prec(sprint_body(e) + tail, ctx, fuel) == (Some(e), tail),
    decreases super::verified_roundtrip::sdepth(e), 5nat,
{
    reveal(super::verified_roundtrip::printable_se);
    let leaf = lleaf(e, ctx);
    let leaf_ctx = lleaf_ctx(e, ctx);
    let spine = after_leaf(e, ctx);
    lemma_body_decomp(e, ctx);
    lleaf_props(e, ctx);
    leaf_printable(e, ctx);
    lleaf_ctx_le(e, ctx);
    let input = sprint_body(e) + tail;
    let sprintf = sprint_min(leaf, leaf_ctx);
    assert(input =~= sprintf + (spine + tail));
    let rest = spine + tail;
    assert(bin_prec(e->Binary_0) >= ctx);
    binary_prec_le_8_direct(e->Binary_0);
    assert(ctx <= 8);
    inert_shape(tail, ctx);
    leaf_rest_shape(e, ctx, tail);
    if leaf is Unary && prec_min(leaf) >= leaf_ctx {
        leaf_gap(e, ctx);
        after_leaf_empty_iff(e, ctx);
        assert(spine.len() >= 1);
        assert(rest[0] == spine[0]);
    }
    leaf_parse_fuel(e, ctx, tail, fuel);
    lleaf_sdepth(e, ctx);
    lemma_leaf_parse(leaf, leaf_ctx, ctx, rest, fuel);
    let lp = verified_precedence::prec_lhs_phase(input, ctx, fuel);
    let lhs0 = lp.0->Some_0;
    assert(lp.0 is Some);
    assert(sparse_postfix_loop(lhs0, lp.1, ctx) == (leaf, rest));
    let rc = (bin_prec(e->Binary_0) + bin_assoc(e->Binary_0)) as u8;
    inert_mono(tail, ctx, rc);
    run_open_fuel(e, ctx, tail, fuel);
    assert(spine + tail =~= after_leaf(e, ctx) + tail);
    lemma_run_open(e, ctx, tail, fuel);
    assert(sparse_infix_loop(leaf, rest, ctx, fuel) == sparse_infix_loop(e, tail, ctx, fuel));
    inert_halts(e, tail, ctx, fuel);
    assert(sparse_postfix_loop(lhs0, lp.1, ctx).0 == leaf);
    assert(sparse_postfix_loop(lhs0, lp.1, ctx).1 == rest);
    prec_from_lhs(input, ctx, fuel, lhs0, lp.1);
    assert(final_result_expr(input, ctx, fuel, lhs0, lp.1) == e);
    assert(final_result_rest(input, ctx, fuel, lhs0, lp.1) == tail);
}

pub proof fn leaf_printable(e: SExpr, ctx: u8)
    requires
        super::verified_roundtrip::printable_se(e),
        e is Binary,
    ensures
        super::verified_roundtrip::printable_se(lleaf(e, ctx)),
    decreases e,
{
    reveal(super::verified_roundtrip::printable_se);
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    if descends(*left, lc) {
        leaf_printable(*left, lc);
        assert(lleaf(e, ctx) == lleaf(*left, lc));
    } else {
        assert(lleaf(e, ctx) == *left);
    }
}

pub proof fn lleaf_ctx_le(e: SExpr, ctx: u8)
    requires
        e is Binary,
        prec_min(e) >= ctx,
    ensures
        ctx <= lleaf_ctx(e, ctx),
    decreases e,
{
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    assert(prec_min(e) == bin_prec(tag));
    assert(lc >= bin_prec(tag)) by {
        assert(bin_assoc(tag) == 0 || bin_assoc(tag) == 1) by {
            match tag { BinaryTag::Exponentiate => {}, _ => {} }
        }
    }
    assert(lc >= ctx);
    if descends(*left, lc) {
        lleaf_ctx_le(*left, lc);
        assert(lleaf_ctx(e, ctx) == lleaf_ctx(*left, lc));
    } else {
        assert(lleaf_ctx(e, ctx) == lc);
    }
}

pub proof fn leaf_rest_shape(e: SExpr, ctx: u8, tail: Seq<TokenView>)
    requires
        e is Binary,
        tail.len() == 0
            || (verified_expression::binary_from_token(tail[0]) is Some
                && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
            || (tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma)
            || neutral_head(tail[0]),
    ensures
        ({
            let rest = after_leaf(e, ctx) + tail;
            rest.len() == 0
                || (verified_expression::binary_from_token(rest[0]) is Some
                    && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
                || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
                || neutral_head(rest[0])
        }),
    decreases e,
{
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
    let here = seq![bin_tok(tag)] + sprint_min(*right, rc);
    super::verified_roundtrip::binary_tok_roundtrip(tag);
    if descends(*left, lc) {
        assert((here + tail)[0] == bin_tok(tag));
        leaf_rest_shape(*left, lc, here + tail);
        assert(after_leaf(e, ctx) + tail =~= after_leaf(*left, lc) + (here + tail));
    } else {
        assert(after_leaf(e, ctx) =~= here);
        let rest = after_leaf(e, ctx) + tail;
        assert(rest[0] == bin_tok(tag));
    }
}

pub proof fn leaf_parse_fuel(e: SExpr, ctx: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        e is Binary,
        fuel >= 2 * (sprint_body(e) + tail).len() + 3,
    ensures
        fuel >= 2 * (sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)) + (after_leaf(e, ctx) + tail)).len()
            + 3,
{
    lemma_body_decomp(e, ctx);
    assert(sprint_body(e) + tail
        =~= sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)) + (after_leaf(e, ctx) + tail));
}

pub proof fn run_open_fuel(e: SExpr, ctx: u8, tail: Seq<TokenView>, fuel: nat)
    requires
        e is Binary,
        fuel >= 2 * (sprint_body(e) + tail).len() + 3,
    ensures
        fuel >= 2 * (after_leaf(e, ctx) + tail).len() + 3,
{
    lemma_body_decomp(e, ctx);
    sprint_body_len_ge(e, ctx);
    assert((after_leaf(e, ctx) + tail).len() <= (sprint_body(e) + tail).len());
}

pub proof fn sprint_body_len_ge(e: SExpr, ctx: u8)
    requires
        e is Binary,
    ensures
        after_leaf(e, ctx).len() <= sprint_body(e).len(),
{
    lemma_body_decomp(e, ctx);
}

pub proof fn lleaf_props(e: SExpr, ctx: u8)
    requires
        e is Binary,
    ensures
        !descends(lleaf(e, ctx), lleaf_ctx(e, ctx)),
    decreases e,
{
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let lc = (bin_prec(tag) + 1 - bin_assoc(tag)) as u8;
    if descends(*left, lc) {
        lleaf_props(*left, lc);
        assert(lleaf(e, ctx) == lleaf(*left, lc));
        assert(lleaf_ctx(e, ctx) == lleaf_ctx(*left, lc));
    } else {
        assert(lleaf(e, ctx) == *left);
        assert(lleaf_ctx(e, ctx) == lc);
    }
}

pub proof fn lemma_run_open(e: SExpr, ctx: u8, cont: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        e is Binary,
        prec_min(e) >= ctx,
        inert(cont, (bin_prec(e->Binary_0) + bin_assoc(e->Binary_0)) as u8),
        fuel >= 2 * (after_leaf(e, ctx) + cont).len() + 3,
    ensures
        ({
            let target = sparse_infix_loop(e, cont, ctx, fuel);
            sparse_infix_loop(lleaf(e, ctx), after_leaf(e, ctx) + cont, ctx, fuel) == target
        }),
    decreases super::verified_roundtrip::sdepth(e), 4nat,
{
    reveal(super::verified_roundtrip::printable_se);
    let (tag, left, right) = match e {
        SExpr::Binary(tag, left, right) => (tag, left, right),
        _ => { return; },
    };
    let bp = bin_prec(tag);
    let assoc = bin_assoc(tag);
    let lc = (bp + 1 - assoc) as u8;
    let rc = (bp + assoc) as u8;
    let here = seq![bin_tok(tag)] + sprint_min(*right, rc);
    assert(prec_min(e) == bp);

    if descends(*left, lc) {
        assert(lleaf(e, ctx) == lleaf(*left, lc));
        assert(after_leaf(e, ctx) =~= after_leaf(*left, lc) + here);
        assert(after_leaf(e, ctx) + cont =~= after_leaf(*left, lc) + (here + cont));
        assert(prec_min(*left) >= lc);
        assert(lleaf(*left, lc) == lleaf(*left, ctx));
        assert(after_leaf(*left, lc) == after_leaf(*left, ctx));
        let ltag = (*left)->Binary_0;
        let rc_l = (bin_prec(ltag) + bin_assoc(ltag)) as u8;
        descend_gap(tag, *left);
        assert(bp < rc_l);
        here_cont_inert(tag, *right, rc, cont, rc_l);
        assert(inert(here + cont, rc_l));
        run_open_len(*left, lc, here + cont, e, ctx, cont);
        lemma_run_open(*left, ctx, here + cont, fuel);
        assert(sparse_infix_loop(lleaf(*left, ctx), after_leaf(*left, ctx) + (here + cont), ctx, fuel)
            == sparse_infix_loop(*left, here + cont, ctx, fuel));
        run_here_step(tag, *left, *right, cont, ctx, fuel);
    } else {
        assert(lleaf(e, ctx) == *left);
        assert(after_leaf(e, ctx) =~= here);
        assert(after_leaf(e, ctx) + cont =~= here + cont);
        run_here_step(tag, *left, *right, cont, ctx, fuel);
    }
}

pub proof fn here_cont_inert(
    tag: BinaryTag,
    r: SExpr,
    rc: u8,
    cont: Seq<TokenView>,
    rc_l: u8,
)
    requires
        bin_prec(tag) < rc_l,
    ensures
        inert(seq![bin_tok(tag)] + sprint_min(r, rc) + cont, rc_l),
{
    let s = seq![bin_tok(tag)] + sprint_min(r, rc) + cont;
    super::verified_roundtrip::binary_tok_roundtrip(tag);
    assert(s[0] == bin_tok(tag));
    assert(verified_expression::binary_from_token(s[0]) == Some(tag));
    assert(binary_prec_s(tag) == bin_prec(tag)) by { tables_agree(tag, UnaryTag::Not); }
    assert(binary_prec_s(tag) < rc_l);
    assert(s[0] != TokenView::Exclamation);
    assert(s[0] != TokenView::Keyword(Keyword::Is));
}

pub proof fn run_here_step(
    tag: BinaryTag,
    l: SExpr,
    r: SExpr,
    cont: Seq<TokenView>,
    ctx: u8,
    fuel: nat,
)
    requires
        super::verified_roundtrip::printable_se(r),
        bin_prec(tag) >= ctx,
        inert(cont, (bin_prec(tag) + bin_assoc(tag)) as u8),
        fuel >= 2 * (seq![bin_tok(tag)] + sprint_min(r, (bin_prec(tag) + bin_assoc(tag)) as u8)
            + cont).len() + 3,
    ensures
        sparse_infix_loop(l, seq![bin_tok(tag)]
            + sprint_min(r, (bin_prec(tag) + bin_assoc(tag)) as u8) + cont, ctx, fuel)
            == sparse_infix_loop(SExpr::Binary(tag, Box::new(l), Box::new(r)), cont, ctx, fuel),
    decreases super::verified_roundtrip::sdepth(r), 9nat,
{
    reveal_with_fuel(sparse_infix_loop, 1);
    let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
    let input = seq![bin_tok(tag)] + sprint_min(r, rc) + cont;
    binary_tok_tag(tag);
    assert(input[0] == bin_tok(tag));
    assert(verified_expression::binary_from_token(input[0]) == Some(tag));
    assert(binary_prec_s(tag) >= ctx) by { tables_agree(tag, UnaryTag::Not); }
    assert(input.drop_first() =~= sprint_min(r, rc) + cont);
    let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
    assert(next_prec == rc) by { tables_agree(tag, UnaryTag::Not); }
    sprint_min_len(r, rc);
    lemma_min(r, rc, cont, (fuel - 1) as nat);
    assert(sparse_prec(sprint_min(r, rc) + cont, next_prec, (fuel - 1) as nat) == (Some(r), cont));
    verified_precedence::lemma_infix_fuel(
        SExpr::Binary(tag, Box::new(l), Box::new(r)), cont, ctx, (fuel - 1) as nat, fuel);
}

pub proof fn run_open_len(
    l: SExpr,
    lc: u8,
    hc: Seq<TokenView>,
    e: SExpr,
    ctx: u8,
    cont: Seq<TokenView>,
)
    requires
        e is Binary,
        descends(l, (bin_prec(e->Binary_0) + 1 - bin_assoc(e->Binary_0)) as u8),
        lc == (bin_prec(e->Binary_0) + 1 - bin_assoc(e->Binary_0)) as u8,
        l == *(e->Binary_1),
        hc == seq![bin_tok(e->Binary_0)]
            + sprint_min(*(e->Binary_2), (bin_prec(e->Binary_0) + bin_assoc(e->Binary_0)) as u8)
            + cont,
    ensures
        (after_leaf(l, lc) + hc).len() == (after_leaf(e, ctx) + cont).len(),
{
    let tag = e->Binary_0;
    let rc = (bin_prec(tag) + bin_assoc(tag)) as u8;
    let here = seq![bin_tok(tag)] + sprint_min(*(e->Binary_2), rc);
    assert(after_leaf(e, ctx) =~= after_leaf(l, lc) + here);
    assert(hc =~= here + cont);
    assert(after_leaf(l, lc) + hc =~= (after_leaf(l, lc) + here) + cont);
}

pub proof fn binary_tok_tag(tag: BinaryTag)
    ensures
        verified_expression::binary_from_token(bin_tok(tag)) == Some(tag),
{
    super::verified_roundtrip::binary_tok_roundtrip(tag);
}


pub proof fn min_roundtrip(e: SExpr, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(e),
        fuel >= 2 * sprint_min(e, 0).len() + 3,
    ensures
        sparse_prec(sprint_min(e, 0), 0, fuel) == (Some(e), Seq::<TokenView>::empty()),
{
    let tail = Seq::<TokenView>::empty();
    boundary_inert(tail, 0);
    assert(sprint_min(e, 0) + tail =~= sprint_min(e, 0));
    lemma_min(e, 0, tail, fuel);
}


pub fn prec_min_exec(e: &ast::Expression) -> (r: u8)
    ensures
        r == prec_min(super::verified_roundtrip::view_expr(*e)),
{
    reveal_with_fuel(super::verified_roundtrip::view_expr, 2);
    match e {
        ast::Expression::All => 11,
        ast::Expression::Column(_, _) => 11,
        ast::Expression::Literal(_) => 11,
        ast::Expression::Function(_, _) => 11,
        ast::Expression::Operator(op) => match op {
            ast::Operator::Not(_) => 3,
            ast::Operator::Identity(_) => 10,
            ast::Operator::Negate(_) => 10,
            ast::Operator::Factorial(_) => 9,
            ast::Operator::Is(_, _) => 4,
            ast::Operator::And(_, _) => 2,
            ast::Operator::Or(_, _) => 1,
            ast::Operator::Equal(_, _) => 4,
            ast::Operator::NotEqual(_, _) => 4,
            ast::Operator::Like(_, _) => 4,
            ast::Operator::GreaterThan(_, _) => 5,
            ast::Operator::GreaterThanOrEqual(_, _) => 5,
            ast::Operator::LessThan(_, _) => 5,
            ast::Operator::LessThanOrEqual(_, _) => 5,
            ast::Operator::Add(_, _) => 6,
            ast::Operator::Subtract(_, _) => 6,
            ast::Operator::Multiply(_, _) => 7,
            ast::Operator::Divide(_, _) => 7,
            ast::Operator::Remainder(_, _) => 7,
            ast::Operator::Exponentiate(_, _) => 8,
        },
    }
}

pub fn wrap_parens(inner: Vec<super::Token>) -> (r: Vec<super::Token>)
    ensures
        verified_production::token_views(r@)
            == seq![TokenView::OpenParen] + verified_production::token_views(inner@)
                + seq![TokenView::CloseParen],
{
    reveal_with_fuel(verified_production::token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(super::Token::OpenParen);
    let ghost open = r@;
    let mut inner = inner;
    let ghost inner_old = inner@;
    r.append(&mut inner);
    r.push(super::Token::CloseParen);
    proof {
        assert(open.drop_first() =~= Seq::<super::Token>::empty());
        assert(r@ =~= open + inner_old + seq![super::Token::CloseParen]);
        verified_production::token_views_concat(open + inner_old, seq![super::Token::CloseParen]);
        verified_production::token_views_concat(open, inner_old);
        assert(verified_production::token_views(open) =~= seq![TokenView::OpenParen]);
        assert(verified_production::token_views(seq![super::Token::CloseParen])
            =~= seq![TokenView::CloseParen]);
    }
    r
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20000)]
pub fn print_min_at(e: &ast::Expression, ctx: u8) -> (r: Vec<super::Token>)
    requires
        super::verified_roundtrip::printable_se(super::verified_roundtrip::view_expr(*e)),
    ensures
        verified_production::token_views(r@)
            == sprint_min(super::verified_roundtrip::view_expr(*e), ctx),
    decreases super::verified_roundtrip::sdepth(super::verified_roundtrip::view_expr(*e)), 2nat,
{
    reveal_with_fuel(sprint_min, 1);
    let body = print_min_body(e);
    let pm = prec_min_exec(e);
    if pm < ctx {
        wrap_parens(body)
    } else {
        body
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30000)]
pub fn print_min_body(e: &ast::Expression) -> (r: Vec<super::Token>)
    requires
        super::verified_roundtrip::printable_se(super::verified_roundtrip::view_expr(*e)),
    ensures
        verified_production::token_views(r@) == sprint_body(super::verified_roundtrip::view_expr(*e)),
    decreases super::verified_roundtrip::sdepth(super::verified_roundtrip::view_expr(*e)), 1nat,
{
    reveal(super::verified_roundtrip::printable_se);
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(super::verified_roundtrip::view_expr, 2);
    let ghost se = super::verified_roundtrip::view_expr(*e);
    match e {
        ast::Expression::All | ast::Expression::Column(_, _) | ast::Expression::Literal(_)
        | ast::Expression::Function(_, _) => {
            print_min_atom(e)
        },
        ast::Expression::Operator(op) => {
            let out = match op {
                ast::Operator::Not(inner) =>
                    prepend_tok(super::Token::Keyword(Keyword::Not), print_min_at(&**inner, 3)),
                ast::Operator::Identity(inner) =>
                    prepend_tok(super::Token::Plus, print_min_at(&**inner, 10)),
                ast::Operator::Negate(inner) =>
                    prepend_tok(super::Token::Minus, print_min_at(&**inner, 10)),
                ast::Operator::Factorial(inner) =>
                    append_tok(print_min_at(&**inner, 10), super::Token::Exclamation),
                ast::Operator::Is(inner, lit) => {
                    let is_tok = match lit {
                        ast::Literal::Null => super::Token::Keyword(Keyword::Null),
                        _ => super::Token::Keyword(Keyword::NaN),
                    };
                    append_is(print_min_at(&**inner, 10), is_tok)
                },
                ast::Operator::Or(l, rr) =>
                    mid_binary(print_min_at(&**l, 1), super::Token::Keyword(Keyword::Or), print_min_at(&**rr, 2)),
                ast::Operator::And(l, rr) =>
                    mid_binary(print_min_at(&**l, 2), super::Token::Keyword(Keyword::And), print_min_at(&**rr, 3)),
                ast::Operator::Equal(l, rr) =>
                    mid_binary(print_min_at(&**l, 4), super::Token::Equal, print_min_at(&**rr, 5)),
                ast::Operator::NotEqual(l, rr) =>
                    mid_binary(print_min_at(&**l, 4), super::Token::NotEqual, print_min_at(&**rr, 5)),
                ast::Operator::Like(l, rr) =>
                    mid_binary(print_min_at(&**l, 4), super::Token::Keyword(Keyword::Like), print_min_at(&**rr, 5)),
                ast::Operator::GreaterThan(l, rr) =>
                    mid_binary(print_min_at(&**l, 5), super::Token::GreaterThan, print_min_at(&**rr, 6)),
                ast::Operator::GreaterThanOrEqual(l, rr) =>
                    mid_binary(print_min_at(&**l, 5), super::Token::GreaterThanOrEqual, print_min_at(&**rr, 6)),
                ast::Operator::LessThan(l, rr) =>
                    mid_binary(print_min_at(&**l, 5), super::Token::LessThan, print_min_at(&**rr, 6)),
                ast::Operator::LessThanOrEqual(l, rr) =>
                    mid_binary(print_min_at(&**l, 5), super::Token::LessThanOrEqual, print_min_at(&**rr, 6)),
                ast::Operator::Add(l, rr) =>
                    mid_binary(print_min_at(&**l, 6), super::Token::Plus, print_min_at(&**rr, 7)),
                ast::Operator::Subtract(l, rr) =>
                    mid_binary(print_min_at(&**l, 6), super::Token::Minus, print_min_at(&**rr, 7)),
                ast::Operator::Multiply(l, rr) =>
                    mid_binary(print_min_at(&**l, 7), super::Token::Asterisk, print_min_at(&**rr, 8)),
                ast::Operator::Divide(l, rr) =>
                    mid_binary(print_min_at(&**l, 7), super::Token::Slash, print_min_at(&**rr, 8)),
                ast::Operator::Remainder(l, rr) =>
                    mid_binary(print_min_at(&**l, 7), super::Token::Percent, print_min_at(&**rr, 8)),
                ast::Operator::Exponentiate(l, rr) =>
                    mid_binary(print_min_at(&**l, 9), super::Token::Caret, print_min_at(&**rr, 8)),
            };
            out
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20000)]
pub fn print_min_atom(e: &ast::Expression) -> (r: Vec<super::Token>)
    requires
        super::verified_roundtrip::printable_se(super::verified_roundtrip::view_expr(*e)),
        !(e is Operator),
    ensures
        verified_production::token_views(r@) == sprint_body(super::verified_roundtrip::view_expr(*e)),
    decreases super::verified_roundtrip::sdepth(super::verified_roundtrip::view_expr(*e)), 0nat,
{
    reveal(super::verified_roundtrip::printable_se);
    reveal_with_fuel(sprint_body, 1);
    reveal_with_fuel(super::verified_roundtrip::view_expr, 2);
    reveal_with_fuel(verified_production::token_views, 3);
    let mut r: Vec<super::Token> = Vec::new();
    match e {
        ast::Expression::All => {
            r.push(super::Token::Asterisk);
            proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
            r
        },
        ast::Expression::Column(table, column) => match table {
            Some(t) => {
                r.push(super::Token::Ident(t.clone()));
                r.push(super::Token::Period);
                r.push(super::Token::Ident(column.clone()));
                proof {
                    reveal_with_fuel(verified_production::token_views, 4);
                    assert(r@.drop_first().drop_first().drop_first() =~= Seq::<super::Token>::empty());
                }
                r
            },
            None => {
                r.push(super::Token::Ident(column.clone()));
                proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
                r
            },
        },
        ast::Expression::Literal(l) => super::verified_roundtrip::print_lit_exec(l),
        ast::Expression::Function(name, args) => {
            r.push(super::Token::Ident(name.clone()));
            r.push(super::Token::OpenParen);
            let ghost head = r@;
            let mut body = print_min_args_slice(args.as_slice());
            let ghost body_old = body@;
            r.append(&mut body);
            r.push(super::Token::CloseParen);
            proof {
                assert(r@ =~= head + body_old + seq![super::Token::CloseParen]);
                verified_production::token_views_concat(head + body_old, seq![super::Token::CloseParen]);
                verified_production::token_views_concat(head, body_old);
                assert(head.drop_first().drop_first() =~= Seq::<super::Token>::empty());
                assert(verified_production::token_views(head)
                    =~= seq![TokenView::Ident(*name), TokenView::OpenParen]);
            }
            r
        },
        _ => { assert(false); Vec::new() },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20000)]
pub fn print_min_args_slice(s: &[ast::Expression]) -> (r: Vec<super::Token>)
    requires
        super::verified_roundtrip::all_printable_se(super::verified_roundtrip::view_args(s@)),
    ensures
        verified_production::token_views(r@)
            == sprint_min_args(super::verified_roundtrip::view_args(s@)),
    decreases super::verified_roundtrip::slist_depth(super::verified_roundtrip::view_args(s@)),
{
    reveal_with_fuel(sprint_min_args, 1);
    reveal_with_fuel(verified_production::token_views, 1);
    reveal(super::verified_roundtrip::all_printable_se);
    let ghost va = super::verified_roundtrip::view_args(s@);
    if s.len() == 0 {
        let r: Vec<super::Token> = Vec::new();
        proof { assert(super::verified_roundtrip::view_args(s@) =~= Seq::<SExpr>::empty()); }
        r
    } else if s.len() == 1 {
        proof {
            super::verified_roundtrip::view_args_step(s@);
            super::verified_roundtrip::sdepth_positive(super::verified_roundtrip::view_args(s@)[0]);
            assert(super::verified_roundtrip::view_args(s@.drop_first()) =~= Seq::<SExpr>::empty());
            assert(sprint_min_args(super::verified_roundtrip::view_args(s@))
                == sprint_min(super::verified_roundtrip::view_args(s@)[0], 0));
            super::verified_roundtrip::slist_depth_head_decreases(s@);
        }
        print_min_at(&s[0], 0)
    } else {
        proof {
            super::verified_roundtrip::view_args_len(s@);
            super::verified_roundtrip::view_args_step(s@);
            super::verified_roundtrip::sdepth_positive(super::verified_roundtrip::view_args(s@)[0]);
            super::verified_roundtrip::slist_depth_head_decreases(s@);
            super::verified_roundtrip::slist_depth_tail_decreases(s@);
        }
        let mut r = print_min_at(&s[0], 0);
        let ghost p0 = r@;
        r.push(super::Token::Comma);
        let ghost head = r@;
        let rest = vstd::slice::slice_subrange(s, 1, s.len());
        proof { assert(rest@ =~= s@.drop_first()); }
        let mut more = print_min_args_slice(rest);
        let ghost more_old = more@;
        r.append(&mut more);
        proof {
            reveal_with_fuel(verified_production::token_views, 2);
            assert(head =~= p0 + seq![super::Token::Comma]);
            assert(r@ =~= head + more_old);
            verified_production::token_views_concat(head, more_old);
            verified_production::token_views_concat(p0, seq![super::Token::Comma]);
            assert(verified_production::token_views(seq![super::Token::Comma]) =~= seq![TokenView::Comma]);
            assert(sprint_min_args(super::verified_roundtrip::view_args(s@))
                =~= sprint_min(super::verified_roundtrip::view_args(s@)[0], 0) + seq![TokenView::Comma]
                    + sprint_min_args(super::verified_roundtrip::view_args(s@).drop_first()));
        }
        r
    }
}

pub fn prepend_tok(tok: super::Token, inner: Vec<super::Token>) -> (r: Vec<super::Token>)
    ensures
        verified_production::token_views(r@)
            == seq![verified_production::token_view(tok)] + verified_production::token_views(inner@),
{
    reveal_with_fuel(verified_production::token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    r.push(tok);
    let ghost head = r@;
    let mut inner = inner;
    let ghost inner_old = inner@;
    r.append(&mut inner);
    proof {
        assert(r@ =~= head + inner_old);
        verified_production::token_views_concat(head, inner_old);
        assert(head.drop_first() =~= Seq::<super::Token>::empty());
    }
    r
}

pub fn append_tok(inner: Vec<super::Token>, tok: super::Token) -> (r: Vec<super::Token>)
    ensures
        verified_production::token_views(r@)
            == verified_production::token_views(inner@) + seq![verified_production::token_view(tok)],
{
    reveal_with_fuel(verified_production::token_views, 2);
    let mut r = inner;
    let ghost inner_old = r@;
    r.push(tok);
    proof {
        assert(r@ =~= inner_old + seq![tok]);
        verified_production::token_views_concat(inner_old, seq![tok]);
        assert(verified_production::token_views(seq![tok]) =~= seq![verified_production::token_view(tok)]);
    }
    r
}

pub fn append_is(inner: Vec<super::Token>, is_tok: super::Token) -> (r: Vec<super::Token>)
    ensures
        verified_production::token_views(r@)
            == verified_production::token_views(inner@)
                + seq![TokenView::Keyword(Keyword::Is), verified_production::token_view(is_tok)],
{
    reveal_with_fuel(verified_production::token_views, 3);
    let mut r = inner;
    let ghost inner_old = r@;
    r.push(super::Token::Keyword(Keyword::Is));
    r.push(is_tok);
    proof {
        assert(r@ =~= inner_old + seq![super::Token::Keyword(Keyword::Is), is_tok]);
        verified_production::token_views_concat(inner_old,
            seq![super::Token::Keyword(Keyword::Is), is_tok]);
        assert(seq![super::Token::Keyword(Keyword::Is), is_tok].drop_first().drop_first()
            =~= Seq::<super::Token>::empty());
        assert(verified_production::token_view(super::Token::Keyword(Keyword::Is))
            == TokenView::Keyword(Keyword::Is));
        assert(verified_production::token_views(seq![super::Token::Keyword(Keyword::Is), is_tok])
            =~= seq![TokenView::Keyword(Keyword::Is), verified_production::token_view(is_tok)]);
    }
    r
}

pub fn mid_binary(left: Vec<super::Token>, op: super::Token, right: Vec<super::Token>)
    -> (r: Vec<super::Token>)
    ensures
        verified_production::token_views(r@)
            == verified_production::token_views(left@) + seq![verified_production::token_view(op)]
                + verified_production::token_views(right@),
{
    reveal_with_fuel(verified_production::token_views, 2);
    let mut r = left;
    let ghost left_old = r@;
    r.push(op);
    let ghost mid = r@;
    let mut right = right;
    let ghost right_old = right@;
    r.append(&mut right);
    proof {
        assert(mid =~= left_old + seq![op]);
        assert(r@ =~= mid + right_old);
        verified_production::token_views_concat(mid, right_old);
        verified_production::token_views_concat(left_old, seq![op]);
        assert(verified_production::token_views(seq![op]) =~= seq![verified_production::token_view(op)]);
    }
    r
}

pub fn print_min_expr(e: &ast::Expression) -> (r: Vec<super::Token>)
    requires
        super::verified_roundtrip::printable_se(super::verified_roundtrip::view_expr(*e)),
    ensures
        verified_production::token_views(r@)
            == sprint_min(super::verified_roundtrip::view_expr(*e), 0),
{
    print_min_at(e, 0)
}


#[verifier::rlimit(20000)]
pub fn min_roundtrip_live(e: &ast::Expression, fuel: usize)
    -> (r: (Option<ast::Expression>, usize, Option<super::parse_error::ParseError>))
    requires
        super::verified_roundtrip::printable_se(super::verified_roundtrip::view_expr(*e)),
        fuel >= 2 * sprint_min(super::verified_roundtrip::view_expr(*e), 0).len() + 3,
    ensures
        r.0 is Some,
        super::verified_roundtrip::view_expr(r.0->Some_0)
            == super::verified_roundtrip::view_expr(*e),
        r.1 == sprint_min(super::verified_roundtrip::view_expr(*e), 0).len(),
{
    let toks = print_min_expr(e);
    let ghost se = super::verified_roundtrip::view_expr(*e);
    proof {
        super::verified_roundtrip::token_views_len(toks@);
    }
    let (opt, pos, err) = verified_precedence::parse_expression_at(&toks, 0, 0, fuel);
    proof {
        assert(toks@.subrange(0, toks@.len() as int) =~= toks@);
        assert(verified_production::token_views(toks@.subrange(0, toks@.len() as int))
            == sprint_min(se, 0));
        min_roundtrip(se, fuel as nat);
        assert(sparse_prec(sprint_min(se, 0), 0, fuel as nat)
            == (Some(se), Seq::<TokenView>::empty()));
        assert(opt is Some);
        assert(super::verified_roundtrip::view_expr(opt->Some_0) == se);
        super::verified_roundtrip::token_views_len(toks@.subrange(pos as int, toks@.len() as int));
        assert(verified_production::token_views(toks@.subrange(pos as int, toks@.len() as int))
            == Seq::<TokenView>::empty());
    }
    (opt, pos, err)
}


pub open spec fn min_normal(toks: Seq<TokenView>) -> bool {
    exists|e: SExpr|
        super::verified_roundtrip::printable_se(e) && #[trigger] sprint_min(e, 0) == toks
}

pub proof fn min_dual(toks: Seq<TokenView>, fuel: nat)
    requires
        min_normal(toks),
        fuel >= super::verified_stmt_prec::expr_fuel(toks),
    ensures
        sparse_prec(toks, 0, fuel).0 is Some,
        super::verified_roundtrip::printable_se(sparse_prec(toks, 0, fuel).0->Some_0),
        sprint_min(sparse_prec(toks, 0, fuel).0->Some_0, 0) == toks,
        sparse_prec(toks, 0, fuel).1 == Seq::<TokenView>::empty(),
{
    let e = choose|e: SExpr|
        super::verified_roundtrip::printable_se(e) && #[trigger] sprint_min(e, 0) == toks;
    min_roundtrip(e, fuel);
}

pub proof fn min_parse_injective(t1: Seq<TokenView>, t2: Seq<TokenView>, f1: nat, f2: nat)
    requires
        min_normal(t1),
        min_normal(t2),
        f1 >= super::verified_stmt_prec::expr_fuel(t1),
        f2 >= super::verified_stmt_prec::expr_fuel(t2),
        sparse_prec(t1, 0, f1).0 == sparse_prec(t2, 0, f2).0,
    ensures
        t1 == t2,
{
    min_dual(t1, f1);
    min_dual(t2, f2);
}


pub open spec fn min_normal_fix(toks: Seq<TokenView>) -> bool {
    let (sopt, srest) = sparse_prec(toks, 0, super::verified_stmt_prec::expr_fuel(toks));
    &&& sopt is Some
    &&& srest.len() == 0
    &&& super::verified_roundtrip::printable_se(sopt->Some_0)
    &&& sprint_min(sopt->Some_0, 0) == toks
}

pub proof fn min_normal_fix_iff(toks: Seq<TokenView>)
    ensures
        min_normal(toks) == min_normal_fix(toks),
{
    if min_normal(toks) {
        min_dual(toks, super::verified_stmt_prec::expr_fuel(toks));
    }
    if min_normal_fix(toks) {
        let e = sparse_prec(toks, 0, super::verified_stmt_prec::expr_fuel(toks)).0->Some_0;
        assert(super::verified_roundtrip::printable_se(e) && sprint_min(e, 0) == toks);
    }
}


pub open spec fn floats_ok(e: SExpr) -> bool
    decreases e,
{
    match e {
        SExpr::Literal(ast::Literal::Float(v)) =>
            v.is_finite_spec() && !v.is_sign_negative_spec(),
        SExpr::Literal(_) => true,
        SExpr::All => true,
        SExpr::Column(_, _) => true,
        SExpr::Unary(_, inner) => floats_ok(*inner),
        SExpr::Factorial(inner) => floats_ok(*inner),
        SExpr::Is(inner, _) => floats_ok(*inner),
        SExpr::Binary(_, left, right) => floats_ok(*left) && floats_ok(*right),
        SExpr::Function(_, args) => all_floats_ok(args),
    }
}

pub open spec fn all_floats_ok(args: Seq<SExpr>) -> bool
    decreases args,
{
    args.len() == 0 || (floats_ok(args[0]) && all_floats_ok(args.drop_first()))
}

pub open spec fn cond_printable(e: SExpr) -> bool {
    floats_ok(e) ==> super::verified_roundtrip::printable_se(e)
}

pub open spec fn cond_all_printable(args: Seq<SExpr>) -> bool {
    all_floats_ok(args) ==> super::verified_roundtrip::all_printable_se(args)
}

pub proof fn cond_printable_unary(tag: UnaryTag, inner: SExpr)
    requires
        cond_printable(inner),
    ensures
        cond_printable(SExpr::Unary(tag, Box::new(inner))),
{
    reveal(super::verified_roundtrip::printable_se);
}

pub proof fn cond_printable_postfix(inner: SExpr, lit: IsLit)
    requires
        cond_printable(inner),
    ensures
        cond_printable(SExpr::Factorial(Box::new(inner))),
        cond_printable(SExpr::Is(Box::new(inner), lit)),
{
    reveal(super::verified_roundtrip::printable_se);
}

pub proof fn cond_printable_binary(tag: BinaryTag, left: SExpr, right: SExpr)
    requires
        cond_printable(left),
        cond_printable(right),
    ensures
        cond_printable(SExpr::Binary(tag, Box::new(left), Box::new(right))),
{
    reveal(super::verified_roundtrip::printable_se);
}

pub proof fn cond_all_singleton(e: SExpr)
    requires
        cond_printable(e),
    ensures
        cond_all_printable(seq![e]),
{
    reveal(super::verified_roundtrip::all_printable_se);
    if all_floats_ok(seq![e]) {
        assert(floats_ok(e));
        assert(seq![e].drop_first() =~= Seq::<SExpr>::empty());
        assert(super::verified_roundtrip::all_printable_se(seq![e].drop_first()));
    }
}

pub proof fn cond_all_cons(e: SExpr, more: Seq<SExpr>)
    requires
        cond_printable(e),
        cond_all_printable(more),
    ensures
        cond_all_printable(seq![e] + more),
{
    reveal(super::verified_roundtrip::all_printable_se);
    let s = seq![e] + more;
    assert(s[0] == e);
    assert(s.drop_first() =~= more);
    if all_floats_ok(s) {
        assert(floats_ok(e));
        assert(all_floats_ok(more));
    }
}

pub proof fn sparse_postfix_printable(lhs: SExpr, input: Seq<TokenView>, min_prec: u8)
    requires
        cond_printable(lhs),
    ensures
        cond_printable(sparse_postfix_loop(lhs, input, min_prec).0),
    decreases input.len(),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
    if input.len() == 0 {
    } else if input[0] == TokenView::Exclamation {
        if 9 >= min_prec {
            cond_printable_postfix(lhs, IsLit::Null);
            sparse_postfix_printable(SExpr::Factorial(Box::new(lhs)), input.drop_first(), min_prec);
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
                cond_printable_postfix(lhs, lit);
                let new_lhs = if negated {
                    cond_printable_unary(UnaryTag::Not, is_expr);
                    SExpr::Unary(UnaryTag::Not, Box::new(is_expr))
                } else {
                    is_expr
                };
                sparse_postfix_printable(new_lhs, input.subrange(p + 1, input.len() as int), min_prec);
            }
        }
    }
}

pub proof fn sparse_infix_printable(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    requires
        cond_printable(lhs),
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel).0 is Some
            ==> cond_printable(sparse_infix_loop(lhs, input, min_prec, fuel).0->Some_0),
    decreases fuel, 2nat,
{
    reveal_with_fuel(sparse_infix_loop, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match verified_expression::binary_from_token(input[0]) {
            Some(tag) => {
                if binary_prec_s(tag) >= min_prec {
                    let next_prec = (binary_prec_s(tag) + binary_assoc_s(tag)) as u8;
                    sparse_prec_printable(input.drop_first(), next_prec, (fuel - 1) as nat);
                    match sparse_prec(input.drop_first(), next_prec, (fuel - 1) as nat) {
                        (Some(right), rest) => {
                            cond_printable_binary(tag, lhs, right);
                            sparse_infix_printable(
                                SExpr::Binary(tag, Box::new(lhs), Box::new(right)),
                                rest,
                                min_prec,
                                (fuel - 1) as nat,
                            );
                        },
                        (None, _) => {},
                    }
                }
            },
            None => {},
        }
    }
}

pub proof fn sparse_atom_printable(input: Seq<TokenView>, fuel: nat)
    ensures
        sparse_atom(input, fuel).0 is Some
            ==> cond_printable(sparse_atom(input, fuel).0->Some_0),
    decreases fuel, 3nat,
{
    reveal_with_fuel(sparse_atom, 1);
    reveal(super::verified_roundtrip::printable_se);
    if fuel == 0 || input.len() == 0 {
    } else {
        match input[0] {
            TokenView::Number(bytes) => {
                reveal(verified_production::parse_literal_views);
                match verified_production::parse_literal_views(seq![TokenView::Number(bytes)]) {
                    Some(lit) => {
                        match lit {
                            ast::Literal::Integer(v) => {
                                assert(v >= 0);
                            },
                            _ => {},
                        }
                    },
                    None => {},
                }
            },
            TokenView::Ident(name) => {
                if input.len() >= 2 && input[1] == TokenView::OpenParen {
                    sparse_fn_args_printable(input.subrange(2, input.len() as int), fuel);
                }
            },
            TokenView::OpenParen => {
                sparse_prec_printable(input.drop_first(), 0, (fuel - 1) as nat);
            },
            _ => {},
        }
    }
}

pub proof fn sparse_fn_args_printable(input: Seq<TokenView>, fuel: nat)
    ensures
        verified_precedence::sparse_fn_args(input, fuel).0 is Some
            ==> cond_all_printable(verified_precedence::sparse_fn_args(input, fuel).0->Some_0),
    decreases fuel, 2nat,
{
    reveal_with_fuel(verified_precedence::sparse_fn_args, 1);
    reveal(super::verified_roundtrip::all_printable_se);
    if fuel == 0 || input.len() == 0 {
    } else if input[0] == TokenView::CloseParen {
    } else {
        sparse_fn_args_ne_printable(input, fuel);
    }
}

pub proof fn sparse_fn_args_ne_printable(input: Seq<TokenView>, fuel: nat)
    ensures
        verified_precedence::sparse_fn_args_nonempty(input, fuel).0 is Some
            ==> cond_all_printable(
                verified_precedence::sparse_fn_args_nonempty(input, fuel).0->Some_0),
    decreases fuel, 1nat,
{
    reveal_with_fuel(verified_precedence::sparse_fn_args_nonempty, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        sparse_prec_printable(input, 0, (fuel - 1) as nat);
        match sparse_prec(input, 0, (fuel - 1) as nat) {
            (Some(e), rest) => {
                if rest.len() == 0 {
                } else if rest[0] == TokenView::CloseParen {
                    cond_all_singleton(e);
                } else if rest[0] == TokenView::Comma {
                    sparse_fn_args_ne_printable(rest.drop_first(), (fuel - 1) as nat);
                    match verified_precedence::sparse_fn_args_nonempty(
                        rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), _) => { cond_all_cons(e, more); },
                        (None, _) => {},
                    }
                }
            },
            (None, _) => {},
        }
    }
}

pub proof fn sparse_prec_printable(input: Seq<TokenView>, min_prec: u8, fuel: nat)
    ensures
        sparse_prec(input, min_prec, fuel).0 is Some
            ==> cond_printable(sparse_prec(input, min_prec, fuel).0->Some_0),
    decreases fuel, 3nat,
{
    reveal_with_fuel(sparse_prec, 1);
    if fuel == 0 || input.len() == 0 {
    } else {
        match verified_expression::prefix_operator(input[0]) {
            Some(tag) => {
                if prefix_prec_s(tag) >= min_prec {
                    sparse_prec_printable(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat);
                    match sparse_prec(input.drop_first(), prefix_prec_s(tag), (fuel - 1) as nat) {
                        (Some(inner), _) => { cond_printable_unary(tag, inner); },
                        (None, _) => {},
                    }
                } else {
                    sparse_atom_printable(input, (fuel - 1) as nat);
                }
            },
            None => { sparse_atom_printable(input, (fuel - 1) as nat); },
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
                sparse_postfix_printable(lhs0, after_lhs, min_prec);
                sparse_infix_printable(lhs1, cur1, min_prec, fuel);
                match sparse_infix_loop(lhs1, cur1, min_prec, fuel) {
                    (None, _) => {},
                    (Some(lhs2), cur2) => {
                        sparse_postfix_printable(lhs2, cur2, min_prec);
                    },
                }
            },
        }
    }
}


pub fn min_normalize_live(toks: &Vec<super::Token>, fuel: usize, refuel: usize)
    -> (r: (ast::Expression, Vec<super::Token>, ast::Expression, usize))
    requires
        fuel >= 2 * toks@.len() + 3,
        ({
            let (sopt, srest) =
                sparse_prec(verified_production::token_views(toks@), 0, fuel as nat);
            &&& sopt is Some
            &&& srest.len() == 0
            &&& floats_ok(sopt->Some_0)
            &&& refuel >= 2 * sprint_min(sopt->Some_0, 0).len() + 3
        }),
    ensures
        ({
            let se = sparse_prec(verified_production::token_views(toks@), 0, fuel as nat).0->Some_0;
            &&& super::verified_roundtrip::view_expr(r.0) == se
            &&& verified_production::token_views(r.1@) == sprint_min(se, 0)
            &&& min_normal(verified_production::token_views(r.1@))
            &&& super::verified_roundtrip::view_expr(r.2) == se
            &&& r.3 == r.1@.len()
        }),
{
    let ghost input = verified_production::token_views(toks@);
    let ghost se = sparse_prec(input, 0, fuel as nat).0->Some_0;
    proof {
        assert(toks@.subrange(0, toks@.len() as int) =~= toks@);
    }
    let (opt, _pos, _err) = verified_precedence::parse_expression_at(toks, 0, 0, fuel);
    proof {
        assert(opt is Some);
        assert(super::verified_roundtrip::view_expr(opt->Some_0) == se);
        sparse_prec_printable(input, 0, fuel as nat);
        assert(super::verified_roundtrip::printable_se(se));
    }
    let e = opt.unwrap();
    let printed = print_min_expr(&e);
    proof {
        super::verified_roundtrip::token_views_len(printed@);
        assert(printed@.len() == sprint_min(se, 0).len());
        assert(printed@.subrange(0, printed@.len() as int) =~= printed@);
    }
    let (opt2, pos2, _err2) = verified_precedence::parse_expression_at(&printed, 0, 0, refuel);
    proof {
        min_roundtrip(se, refuel as nat);
        assert(opt2 is Some);
        assert(super::verified_roundtrip::view_expr(opt2->Some_0) == se);
        super::verified_roundtrip::token_views_len(
            printed@.subrange(pos2 as int, printed@.len() as int));
        assert(pos2 == printed@.len());
        assert(super::verified_roundtrip::printable_se(se)
            && sprint_min(se, 0) == verified_production::token_views(printed@));
    }
    let e2 = opt2.unwrap();
    (e, printed, e2, pos2)
}

}
