//! Verified precedence-climbing expression parser (Phase 2 of the parser
//! cutover, see `verus-parser-cutover-prompt.md`).
//!
//! Unlike `verified_roundtrip`'s `parse_expr_exec` — which is the exact inverse
//! of the canonical printer and accepts only fully-parenthesised forms — this
//! parser is a 1:1 port of the production precedence-climbing parser in
//! `parser.rs`. It accepts the full concrete grammar (`a + b * c`, prefix/infix/
//! postfix operators with precedence and associativity, function calls,
//! qualified columns, parenthesised groups) and builds production
//! `ast::Expression` values directly over `super::Token`.
//!
//! # What Verus proves here (milestone 1)
//!
//! No panic, no arithmetic overflow, and termination. Every `Vec` index is
//! bounds-guarded, every `pos + k` / `prec + assoc` is range-bounded, and
//! recursion terminates on a `fuel` measure (the caller passes `toks.len() + 1`,
//! which always exceeds the expression-tree depth). There is deliberately no
//! functional specification at this milestone: behavioural equivalence to the
//! trusted production parser is established by the differential harness
//! (`sql::parser::differential`), not by proof. The roundtrip lemma
//! `parse(print(e)) == e` for this parser lands in milestone 2.
//!
//! The `fuel == 0` and out-of-bounds branches return `None` (a safe parse
//! failure). Because the caller supplies enough fuel, these are never taken on
//! well-formed input; the differential harness would flag it if they were.

// Proof/verification scaffolding, not idiomatic library code.
#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_expression::{BinaryTag, UnaryTag};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_roundtrip::{
    binary_tag_exec, build_binary, build_unary, prefix_op_exec, IsLit, SExpr,
};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_production::TokenView;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{ast, float_trust, verified_expression, verified_integer, verified_production, Keyword, Token};

verus! {

// ---- precedence table (mirrors parser.rs) ----------------------------------

// ---- spec twins of the precedence tables (for the roundtrip proof) ---------

/// Spec twin of `binary_prec`; the exec fn is proven to refine it.
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

/// Spec twin of `binary_assoc`.
pub open spec fn binary_assoc_s(tag: BinaryTag) -> u8 {
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

/// Spec twin of `prefix_prec`.
pub open spec fn prefix_prec_s(tag: UnaryTag) -> u8 {
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity => 10,
        UnaryTag::Negate => 10,
    }
}

/// Infix operator precedence. 1 is lowest. Mirrors `InfixOperator::precedence`.
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

/// Infix associativity increment: left-associative operators bind tighter to
/// their left operand (+1), `^` is right-associative (+0). Mirrors
/// `InfixOperator::associativity` folded through `Add<Associativity>`.
pub fn binary_assoc(tag: BinaryTag) -> (r: u8)
    ensures r <= 1, r == binary_assoc_s(tag),
{
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

/// Prefix operator precedence. Mirrors `PrefixOperator::precedence`.
pub fn prefix_prec(tag: UnaryTag) -> (r: u8)
    ensures 3 <= r <= 10, r == prefix_prec_s(tag),
{
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity | UnaryTag::Negate => 10,
    }
}

// ---- postfix classification ------------------------------------------------

/// A detected postfix operator: `!`, or `IS [NOT] NULL|NAN`.
pub enum PostfixOp {
    Factorial,
    /// `negated` is the `NOT`, `nan` selects `NAN` over `NULL`.
    Is { negated: bool, nan: bool },
}

/// Detects a postfix operator at `pos` whose precedence is at least `min_prec`,
/// returning it and the position past its tokens. `IS`/`IS NOT` is precedence 4,
/// `!` is precedence 9. Mirrors `parse_postfix_operator_at`; a malformed
/// `IS ... <other>` yields no postfix (leaving the tokens for the caller to
/// reject), which the differential harness confirms matches the production
/// parser's error on the same input.
pub fn parse_postfix_at(toks: &Vec<Token>, pos: usize, min_prec: u8) -> (r: (Option<PostfixOp>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
{
    if pos >= toks.len() {
        return (None, pos);
    }
    match &toks[pos] {
        Token::Keyword(Keyword::Is) => {
            if 4 < min_prec {
                return (None, pos);
            }
            let mut p = pos + 1;
            let negated = if p < toks.len() && matches!(toks[p], Token::Keyword(Keyword::Not)) {
                p = p + 1;
                true
            } else {
                false
            };
            if p < toks.len() {
                match &toks[p] {
                    Token::Keyword(Keyword::NaN) => (Some(PostfixOp::Is { negated, nan: true }), p + 1),
                    Token::Keyword(Keyword::Null) => {
                        (Some(PostfixOp::Is { negated, nan: false }), p + 1)
                    },
                    _ => (None, pos),
                }
            } else {
                (None, pos)
            }
        },
        Token::Exclamation => {
            if 9 < min_prec {
                (None, pos)
            } else {
                (Some(PostfixOp::Factorial), pos + 1)
            }
        },
        _ => (None, pos),
    }
}

/// The mirror expression a detected postfix operator produces over an operand
/// view. Mirrors `build_postfix` at the `SExpr` level; used by the postfix-loop
/// refinement to connect the exec's `build_postfix` to `sparse_postfix_loop`.
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

/// Builds the `ast::Expression` for a detected postfix operator applied to `lhs`.
/// Mirrors `PostfixOperator::into_expression`.
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

// ---- the parser ------------------------------------------------------------

/// Parses an expression atom: a literal, `*`, a column reference, a function
/// call, or a parenthesised expression. Mirrors `parse_expression_atom`.
pub fn parse_atom(toks: &Vec<Token>, pos: usize, fuel: usize) -> (r: (Option<ast::Expression>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
    decreases fuel, 1int,
{
    if fuel == 0 || pos >= toks.len() {
        return (None, pos);
    }
    match &toks[pos] {
        Token::Asterisk => (Some(ast::Expression::All), pos + 1),
        Token::Number(bytes) => {
            if all_digits_exec_local(bytes.as_slice()) {
                match verified_integer::parse_i64(bytes.as_slice()) {
                    Some(value) => (Some(ast::Expression::Literal(ast::Literal::Integer(value))), pos + 1),
                    None => (None, pos),
                }
            } else {
                match float_trust::parse_f64(bytes.as_slice()) {
                    Some(value) => (Some(ast::Expression::Literal(ast::Literal::Float(value))), pos + 1),
                    None => (None, pos),
                }
            }
        },
        Token::String(value) => {
            (Some(ast::Expression::Literal(ast::Literal::String(value.clone()))), pos + 1)
        },
        Token::Keyword(Keyword::True) => {
            (Some(ast::Expression::Literal(ast::Literal::Boolean(true))), pos + 1)
        },
        Token::Keyword(Keyword::False) => {
            (Some(ast::Expression::Literal(ast::Literal::Boolean(false))), pos + 1)
        },
        Token::Keyword(Keyword::Infinity) => {
            (Some(ast::Expression::Literal(ast::Literal::Float(float_trust::infinity()))), pos + 1)
        },
        Token::Keyword(Keyword::NaN) => {
            (
                Some(ast::Expression::Literal(ast::Literal::Float(float_trust::canonical_nan()))),
                pos + 1,
            )
        },
        Token::Keyword(Keyword::Null) => {
            (Some(ast::Expression::Literal(ast::Literal::Null)), pos + 1)
        },
        Token::Ident(name) => {
            if pos + 1 < toks.len() && matches!(toks[pos + 1], Token::OpenParen) {
                // Function call: name ( args ).
                let fname = name.clone();
                parse_function_call(toks, fname, pos + 2, fuel)
            } else if pos + 1 < toks.len() && matches!(toks[pos + 1], Token::Period) {
                // Qualified column: table . column.
                let table = name.clone();
                if pos + 2 < toks.len() {
                    match &toks[pos + 2] {
                        Token::Ident(column) => (
                            Some(ast::Expression::Column(Some(table), column.clone())),
                            pos + 3,
                        ),
                        _ => (None, pos),
                    }
                } else {
                    (None, pos)
                }
            } else {
                (Some(ast::Expression::Column(None, name.clone())), pos + 1)
            }
        },
        Token::OpenParen => {
            let (inner, ipos) = parse_expression_at(toks, pos + 1, 0, fuel - 1);
            match inner {
                Some(expr) => {
                    if ipos < toks.len() && matches!(toks[ipos], Token::CloseParen) {
                        (Some(expr), ipos + 1)
                    } else {
                        (None, pos)
                    }
                },
                None => (None, pos),
            }
        },
        _ => (None, pos),
    }
}

/// Parses a function call's argument list, having consumed `name (`. `pos`
/// points just past the `(`. Mirrors the `Token::Ident(name) if ... OpenParen`
/// arm of `parse_expression_atom`.
pub fn parse_function_call(toks: &Vec<Token>, name: String, pos: usize, fuel: usize)
    -> (r: (Option<ast::Expression>, usize))
    requires pos <= toks.len(),
    ensures pos <= r.1 <= toks.len(),
    decreases fuel, 0int,
{
    if fuel == 0 {
        return (None, pos);
    }
    let mut args: Vec<ast::Expression> = Vec::new();
    let mut cur = pos;
    let mut first = true;
    loop
        invariant
            pos <= cur <= toks.len(),
            fuel > 0,
        decreases toks.len() - cur,
    {
        if cur >= toks.len() {
            return (None, pos);
        }
        if matches!(toks[cur], Token::CloseParen) {
            return (Some(ast::Expression::Function(name, args)), cur + 1);
        }
        if !first {
            if matches!(toks[cur], Token::Comma) {
                cur = cur + 1;
            } else {
                return (None, pos);
            }
        }
        if cur >= toks.len() {
            return (None, pos);
        }
        let (arg, npos) = parse_expression_at(toks, cur, 0, fuel - 1);
        match arg {
            Some(expr) => {
                args.push(expr);
                cur = npos;
                first = false;
            },
            None => return (None, pos),
        }
    }
}

/// Parses an expression at the given minimum precedence. Mirrors
/// `parse_expression_at`: prefix operator or atom for the left-hand side, a
/// postfix pass, an infix precedence-climbing loop, then a second postfix pass.
pub fn parse_expression_at(toks: &Vec<Token>, pos: usize, min_prec: u8, fuel: usize)
    -> (r: (Option<ast::Expression>, usize))
    requires pos <= toks.len(),
    ensures
        pos <= r.1 <= toks.len(),
        r.0 is Some ==> pos < r.1,
    decreases fuel, 2int,
{
    if fuel == 0 || pos >= toks.len() {
        return (None, pos);
    }
    // Left-hand side: prefix operator (if its precedence clears min_prec) or atom.
    let (lhs_opt, lhs_pos) = match prefix_op_exec(&toks[pos]) {
        Some(tag) if prefix_prec(tag) >= min_prec => {
            let next_prec = prefix_prec(tag); // prefix operators are right-associative (+0).
            let (rhs, rpos) = parse_expression_at(toks, pos + 1, next_prec, fuel - 1);
            match rhs {
                Some(inner) => (Some(build_unary(tag, inner)), rpos),
                None => (None, pos),
            }
        },
        _ => parse_atom(toks, pos, fuel - 1),
    };
    let mut lhs = match lhs_opt {
        Some(expr) => expr,
        None => return (None, pos),
    };
    let mut cur = lhs_pos;

    // Postfix pass 1.
    loop
        invariant
            pos < cur <= toks.len(),
        decreases toks.len() - cur,
    {
        let (op, npos) = parse_postfix_at(toks, cur, min_prec);
        match op {
            Some(op) => {
                lhs = build_postfix(op, lhs);
                cur = npos;
            },
            None => break,
        }
    }

    // Infix precedence-climbing loop.
    loop
        invariant
            pos < cur <= toks.len(),
            fuel > 0,
        decreases toks.len() - cur,
    {
        if cur >= toks.len() {
            break;
        }
        match binary_tag_exec(&toks[cur]) {
            Some(tag) if binary_prec(tag) >= min_prec => {
                let next_prec = binary_prec(tag) + binary_assoc(tag);
                let (rhs, rpos) = parse_expression_at(toks, cur + 1, next_prec, fuel - 1);
                match rhs {
                    Some(right) => {
                        lhs = build_binary(tag, lhs, right);
                        cur = rpos;
                    },
                    None => return (None, pos),
                }
            },
            _ => break,
        }
    }

    // Postfix pass 2 (e.g. `1 + NULL IS NULL`).
    loop
        invariant
            pos < cur <= toks.len(),
        decreases toks.len() - cur,
    {
        let (op, npos) = parse_postfix_at(toks, cur, min_prec);
        match op {
            Some(op) => {
                lhs = build_postfix(op, lhs);
                cur = npos;
            },
            None => break,
        }
    }

    (Some(lhs), cur)
}

/// Local copy of `all_digits_exec` (byte-slice all-ASCII-digit test). Kept here
/// so this module does not depend on `verified_roundtrip`'s spec surface.
fn all_digits_exec_local(bytes: &[u8]) -> (r: bool)
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        true
    } else {
        let b = bytes[bytes.len() - 1];
        if 48u8 <= b && b <= 57u8 {
            all_digits_exec_local(vstd::slice::slice_subrange(bytes, 0, bytes.len() - 1))
        } else {
            false
        }
    }
}

/// Parses a complete expression from a token vector, requiring that the whole
/// vector is consumed. Returns `None` on any parse failure or trailing tokens.
/// This is the entry point the cutover routes `Parser::parse_expr` through.
pub fn parse_expression(toks: &Vec<Token>) -> (r: Option<ast::Expression>) {
    // Fuel exceeds the expression-tree depth (bounded by the token count); the
    // guard keeps the `+ 1` from overflowing on a degenerate maximal vector.
    let fuel = if toks.len() < usize::MAX { toks.len() + 1 } else { toks.len() };
    let (opt, consumed) = parse_expression_at(toks, 0, 0, fuel);
    match opt {
        Some(expr) => {
            if consumed == toks.len() {
                Some(expr)
            } else {
                None
            }
        },
        None => None,
    }
}

// ===========================================================================
// Phase 2.2 — spec-level model of the precedence parser
// ===========================================================================
//
// The executable parser above is a hybrid: `decreases fuel` bounds the
// recursion depth, but the three inner `while` loops (postfix pass 1, the infix
// precedence-climbing loop, postfix pass 2) terminate on the token count, not
// on fuel. The spec model below expresses the whole algorithm as pure
// recursion so it can carry a functional specification. Each loop becomes a
// recursive helper; the fuel-vs-token-count gap between the loops and this
// recursion is bridged by the refinement lemma (Brick 2). This module currently
// establishes the model and its termination (Brick 1); refinement and the
// `parse(sprint(e)) == e` roundtrip (Bricks 2-3) build on it.
//
// Convention (matching `verified_roundtrip::sparse`): the parser works over a
// `Seq<TokenView>` *suffix* and returns the remaining suffix. On any parse
// failure it returns `(None, input)` — the *original* input — mirroring the
// exec parsers, which return the original `pos` on failure.

/// Spec model of `parse_expression_at`: prefix-or-atom for the left-hand side,
/// a postfix pass, the infix precedence-climbing loop, then a second postfix
/// pass. `min_prec` is the minimum operator precedence this call will consume.
pub open spec fn sparse_prec(input: Seq<TokenView>, min_prec: u8, fuel: nat)
    -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 3nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        // Left-hand side: a prefix operator whose precedence clears min_prec, or
        // an atom.
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

/// Spec model of `parse_atom`: literal, `*`, column, function call, or
/// parenthesised group.
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
                } else if input.len() >= 3 && input[1] == TokenView::Period {
                    match input[2] {
                        TokenView::Ident(column) =>
                            (Some(SExpr::Column(Some(name), column)), input.subrange(3, input.len() as int)),
                        _ => (None, input),
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

/// Spec model of the infix precedence-climbing loop. `None` signals a hard
/// failure (a matched operator whose right-hand side failed to parse); the
/// caller then discards all progress and returns the original input, mirroring
/// the exec loop's `return (None, pos)`.
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

/// Spec model of a postfix pass: applies `!` (precedence 9) and `IS [NOT]
/// NULL|NAN` (precedence 4) repeatedly while their precedence clears `min_prec`.
/// A malformed `IS ...` stops the pass, leaving its tokens for the caller.
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

/// Spec model of the function-call argument list, positioned just past `name (`.
/// The empty list (`f()`) is accepted only here; a non-empty list requires at
/// least one argument via `sparse_fn_args_nonempty`. Returns the suffix at the
/// closing `)` (the caller consumes it).
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

/// Parses `arg (, arg)*` ending at the closing `)`. Unlike `sparse_fn_args` this
/// never accepts an empty argument in leading position, so a trailing comma
/// (`f(a,)`) fails exactly as the exec loop does.
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

// ===========================================================================
// Phase 2.2 — spec-level roundtrip: sparse_prec(sprint(e) ++ tail) == (e, tail)
// ===========================================================================
//
// The mathematical heart of the roundtrip, proven purely at the spec level
// (exec-independent). The key structural fact: in the canonical fully-
// parenthesised print, every operand is immediately followed by a token that
// stops the postfix/infix loops — `)`, `,`, `!`, `IS`, or a single binary
// operator — so the precedence-climbing loops each do at most one productive
// step and never diverge on precedence. Operands parsed via `sparse_prec`
// (prefix rhs, infix rhs, top level) always see a *prec-boundary* tail (`)` /
// `,` / empty); operands parsed via `sparse_atom` (lhs phase) may see a `!`,
// `IS`, or binary-operator tail, which the enclosing loop then consumes.

/// A tail that stops every continuation loop: the postfix loop (`!` / `IS`),
/// the infix loop (any binary operator), and keeps a bare atom self-delimiting.
/// `)` and `,` are the only tokens that can follow a complete `sparse_prec`
/// sub-parse in the canonical form.
pub open spec fn prec_boundary(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma
}

/// The infix loop halts immediately when there is no binary operator to consume.
pub proof fn infix_halt(lhs: SExpr, input: Seq<TokenView>, min_prec: u8, fuel: nat)
    requires
        input.len() == 0 || verified_expression::binary_from_token(input[0]) is None,
    ensures
        sparse_infix_loop(lhs, input, min_prec, fuel) == (Some(lhs), input),
{
    reveal_with_fuel(sparse_infix_loop, 1);
}

/// The postfix loop halts immediately when the head is neither `!` nor `IS`.
pub proof fn postfix_halt(lhs: SExpr, input: Seq<TokenView>, min_prec: u8)
    requires
        input.len() == 0
            || (input[0] != TokenView::Exclamation && input[0] != TokenView::Keyword(Keyword::Is)),
    ensures
        sparse_postfix_loop(lhs, input, min_prec) == (lhs, input),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
}

/// A prec-boundary head is neither a binary operator nor a postfix operator, so
/// both continuation loops halt on it.
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

/// Roundtrip for the atom parser: parsing the canonical print of any printable
/// mirror expression (followed by an atom-safe `boundary` tail) via `sparse_atom`
/// recovers the expression and leaves the tail unconsumed. This is the primary
/// induction; `sparse_atom` dispatches every compound form into the interior
/// `sparse_prec` on its parenthesised body.
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
            // sparse_atom sees `(` and recurses sparse_prec on the body.
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.drop_first() =~= body);
            // sparse_prec(body, 0, fuel-1): prefix op then inner then `)`.
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
            // lhs phase parses inner; postfix loop consumes `!`.
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
            // lhs phase parses left; infix loop consumes op then right.
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

/// Roundtrip for the full expression parser: for a prec-boundary tail (`)` / `,`
/// / empty), `sparse_prec` at any `min_prec` recovers the expression. The lhs
/// phase routes to `sparse_atom` (an operand never begins with a prefix
/// operator, by `sprint_head`), then both continuation loops halt on the
/// boundary.
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
    // prefix_operator(tokens[0]) is None (sprint_head), so lhs = sparse_atom.
    lemma_atom(e, tail, (fuel - 1) as nat);
    prec_boundary_halts(e, tail, min_prec, fuel);
}

/// Comma-list roundtrip: parsing the print of a printable argument sequence,
/// closed by a `)`-led tail, recovers the sequence. Empty list allowed here.
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

/// Non-empty argument list: at least one argument (parsed via `sparse_prec` at
/// precedence 0), each followed by `,` or the closing `)`.
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

// ---- small step helpers ----------------------------------------------------

/// One productive step of the postfix loop for `!`.
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

/// One productive step of the postfix loop for `IS NULL` / `IS NAN`.
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

/// One productive step of the infix loop: consume `op`, parse the right operand
/// via `sparse_prec`, then halt at `)`.
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

} // verus!
