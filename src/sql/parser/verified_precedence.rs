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

/// Builds the `ast::Expression` for a detected postfix operator applied to `lhs`.
/// Mirrors `PostfixOperator::into_expression`.
pub fn build_postfix(op: PostfixOp, lhs: ast::Expression) -> ast::Expression {
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

} // verus!
