//! Minimal-parenthesisation printer for the mirror expression grammar
//! (Phase 3 of the parser cutover).
//!
//! The existing roundtrip (`verified_roundtrip::sprint` /
//! `verified_precedence::sparse_prec`) is proven over a *fully-parenthesised*
//! printer: every operator node emits `( ... )`. That printer's domain contains
//! no `1 - 2 - 3`, `NOT a AND b`, `2 ^ 3 ^ 2` — no SQL anyone types — so it
//! cannot observe precedence or associativity at all. A consistent swap of the
//! precedence table would leave it green.
//!
//! This module provides a *minimal-parenthesisation* printer, `sprint_min`,
//! that closes that gap. Its parenthesisation decisions encode the precedence
//! and associativity table a THIRD time, independently of the parser
//! (`verified_precedence::binary_prec_s` / `binary_assoc_s` / `prefix_prec_s`)
//! and its spec twin: it wraps a child in `( ... )` exactly when the child binds
//! looser than the associativity-aware context it sits in. The precedence table
//! (`bin_prec` / `bin_assoc` / `pre_prec`) is written out longhand rather than
//! imported, so a mutation of the parser table that is NOT mirrored here breaks
//! the intended roundtrip; `tables_agree` proves this table coincides with the
//! parser's spec twins, making the third encoding a fact Verus checks.
//!
//! The rule (mirroring `sql/types/expression.rs`'s `ExpressionDisplay`, but
//! associativity-correct for `^`): for a binary node of precedence `bp` and
//! associativity `assoc` (1 = left, 0 = right), the left child is printed at
//! context `bp + 1 - assoc` and the right child at `bp + assoc`; a prefix
//! operator prints its operand at the prefix precedence; the postfix `!`/`IS`
//! print their operand at context 10. A child is bracketed iff its own
//! precedence (`prec_min`) is below the context it is printed at.
//!
//! # Status
//!
//! Task 1 of the phase (the printer + independent precedence table +
//! `tables_agree`) is complete and verified here. The spec-level print/parse
//! roundtrip over `sparse_prec` (task 2) and its lift to the live parser
//! (task 3) are the intended continuation; see the phase report for the
//! precise remaining proof obligation (the left-associative precedence-climbing
//! fold and its inner-operand inertness threading).

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
use super::verified_roundtrip::{IsLit, SExpr};
// These are `spec fn`s (erased from non-Verus builds), so the import is gated to
// Verus compilation; their users (`tables_agree` and the roundtrip lemmas below)
// are all inside `verus!`.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_precedence::{
    binary_assoc_s, binary_prec_s, prefix_prec_s, sparse_atom, sparse_infix_loop,
    sparse_postfix_loop, sparse_prec,
};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, Token, ast, float_trust, verified_expression, verified_production};

verus! {

// ===========================================================================
// Independent precedence / associativity table (third encoding).
//
// These MUST agree with `verified_precedence`'s `binary_prec_s` / `binary_assoc_s`
// / `prefix_prec_s` for the roundtrip to hold; they are written out here longhand
// so the agreement is a fact Verus checks, not an import. `bin_prec` mirrors the
// `ExpressionDisplay::precedence` table in `sql/types/expression.rs`.
// ===========================================================================

/// Precedence of a binary operator, 1 (loosest) .. 8 (tightest). Independent
/// copy of `binary_prec_s`; `bin_prec_agrees` proves they coincide.
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

/// Associativity increment: +1 for left-associative operators, +0 for the
/// right-associative `^`. Independent copy of `binary_assoc_s`.
pub open spec fn bin_assoc(tag: BinaryTag) -> u8 {
    match tag {
        BinaryTag::Exponentiate => 0,
        _ => 1,
    }
}

/// Precedence of a prefix operator. Independent copy of `prefix_prec_s`.
pub open spec fn pre_prec(tag: UnaryTag) -> u8 {
    match tag {
        UnaryTag::Not => 3,
        UnaryTag::Identity => 10,
        UnaryTag::Negate => 10,
    }
}

/// Precedence of the whole node — how tightly its top operator binds. Atoms
/// (11) never need wrapping; postfix `!` is 9, `IS` is 4. This is exactly the
/// `min_prec` threshold at which `sparse_prec` will still consume the node
/// without an enclosing paren.
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

/// The three tables agree with the parser's spec twins.
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

// ===========================================================================
// The minimal-parenthesisation printer.
// ===========================================================================

/// Token encoding of a binary operator tag (reuses the canonical map).
pub open spec fn bin_tok(tag: BinaryTag) -> TokenView {
    super::verified_roundtrip::binary_tok(tag)
}

/// Token encoding of a prefix operator tag.
pub open spec fn pre_tok(tag: UnaryTag) -> TokenView {
    super::verified_roundtrip::unary_tok(tag)
}

/// Prints the *body* of an expression (no outer parens) with children printed at
/// their associativity-aware contexts. Callers wrap the result in parens when the
/// context demands it (`sprint_min`).
pub open spec fn sprint_body(e: SExpr) -> Seq<TokenView>
    decreases e, 0nat,
{
    match e {
        // Atoms print exactly as the canonical printer does.
        SExpr::All => seq![TokenView::Asterisk],
        SExpr::Column(None, column) => seq![TokenView::Ident(column)],
        SExpr::Column(Some(table), column) =>
            seq![TokenView::Ident(table), TokenView::Period, TokenView::Ident(column)],
        SExpr::Literal(literal) => verified_production::literal_views(literal).unwrap(),
        SExpr::Function(name, args) =>
            seq![TokenView::Ident(name), TokenView::OpenParen] + sprint_min_args(args)
                + seq![TokenView::CloseParen],
        // Prefix operator: `op inner`, inner at the prefix precedence.
        SExpr::Unary(tag, inner) =>
            seq![pre_tok(tag)] + sprint_min(*inner, pre_prec(tag)),
        // Postfix `!` and `IS`: operand printed at prec 10, so any binary or
        // postfix sub-operand is bracketed and only atoms or the prefix
        // `+`/`-` (prec 10) stand unbracketed. Both then re-parse as the lhs of
        // the enclosing postfix pass, with no infix fold to reason about. This
        // is more conservative than the theoretical minimum for `IS` (which
        // binds at 4), but keeps the roundtrip's postfix cases single-child.
        SExpr::Factorial(inner) =>
            sprint_min(*inner, 10) + seq![TokenView::Exclamation],
        SExpr::Is(inner, lit) =>
            sprint_min(*inner, 10)
                + seq![TokenView::Keyword(Keyword::Is), super::verified_roundtrip::islit_tok(lit)],
        // Binary: `left op right`. The child that sits on the ASSOCIATIVE side
        // may share the parent's precedence bare; the other side must bind
        // strictly tighter. Left-associative (`assoc == 1`): left at `bp`, right
        // at `bp + 1`. Right-associative `^` (`assoc == 0`): left at `bp + 1`,
        // right at `bp`. Uniformly: left at `bp + 1 - assoc`, right at `bp + assoc`.
        SExpr::Binary(tag, left, right) =>
            sprint_min(*left, (bin_prec(tag) + 1 - bin_assoc(tag)) as u8) + seq![bin_tok(tag)]
                + sprint_min(*right, (bin_prec(tag) + bin_assoc(tag)) as u8),
    }
}

/// Prints `e` for a context that requires at least precedence `ctx`: wraps the
/// body in parens exactly when `e` binds looser than `ctx` (`prec_min(e) < ctx`).
pub open spec fn sprint_min(e: SExpr, ctx: u8) -> Seq<TokenView>
    decreases e, 1nat,
{
    if prec_min(e) < ctx {
        seq![TokenView::OpenParen] + sprint_body(e) + seq![TokenView::CloseParen]
    } else {
        sprint_body(e)
    }
}

/// Comma-separated argument list; each argument printed at context 0 (a `,` or
/// `)` boundary follows, so no argument ever needs wrapping on its own account).
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

// ===========================================================================
// Task 2 — spec-level minimal-parenthesisation roundtrip.
//
//   sparse_prec(sprint_min(e, ctx) ++ tail, ctx, fuel) == (Some(e), tail)
//
// for a `tail` that is *inert* at level `ctx` (see `inert` below) and adequate
// `fuel`. Specialising to `ctx == 0`, `tail == empty` gives the headline
// roundtrip `sparse_prec(sprint_min(e, 0), 0, fuel) == (Some(e), empty)`
// (`min_roundtrip`). The lift to the live parser is `min_roundtrip_live` (task
// 3), via `verified_precedence::parse_expression_at`'s refinement of
// `sparse_prec`.
//
// Unlike the fully-parenthesised printer (`verified_roundtrip::sprint`, whose
// operands are always followed by a boundary token so each continuation loop
// takes at most one step), the min-parens printer emits bare infix spines like
// `1 - 2 - 3`. The parser recovers those by precedence climbing: the infix loop
// replays the whole left spine. The proof therefore threads a precedence-aware
// notion of "the tail does not extend the current parse" — `inert(tail, level)`
// — through both continuation loops, and decomposes a binary node into its
// leftmost leaf plus a fold of `(op, right)` steps.
// ===========================================================================

/// `tail` cannot extend a parse running at min-precedence `level`: its head is
/// neither a postfix operator whose precedence clears `level` (`!` at 9, `IS` at
/// 4) nor a binary operator whose precedence clears `level`. Both continuation
/// loops (`sparse_postfix_loop`, `sparse_infix_loop`) therefore halt on it
/// immediately (`inert_halts`).
pub open spec fn inert(tail: Seq<TokenView>, level: u8) -> bool {
    tail.len() == 0 || {
        &&& match verified_expression::binary_from_token(tail[0]) {
            Some(tag) => binary_prec_s(tag) < level,
            None => true,
        }
        &&& (tail[0] != TokenView::Exclamation || 9 < level)
        &&& (tail[0] != TokenView::Keyword(Keyword::Is) || 4 < level)
    }
}

/// An inert tail stops both continuation loops dead.
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
        // Infix loop: either no binary op, or one below `level`.
        assert(sparse_infix_loop(lhs, tail, level, fuel) == (Some(lhs), tail)) by {
            match verified_expression::binary_from_token(tail[0]) {
                Some(tag) => { assert(binary_prec_s(tag) < level); },
                None => {},
            }
        }
        // Postfix loop: head is not `!`/`IS`, or their precedence is below `level`.
        assert(sparse_postfix_loop(lhs, tail, level) == (lhs, tail));
    }
}

/// Inertness is monotone in the level: a tail inert at `level` is inert at any
/// higher level (the guards only get harder to clear).
pub proof fn inert_mono(tail: Seq<TokenView>, level: u8, level2: u8)
    requires
        inert(tail, level),
        level <= level2,
    ensures
        inert(tail, level2),
{
}

/// A prec-boundary tail (`)` / `,` / empty) is inert at every level: `)` and `,`
/// are neither binary nor postfix operators.
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

// ---- printer length bounds (fuel accounting) -------------------------------
//
// The parser lemmas require `fuel >= 2 * input.len() + k`. We express fuel
// budgets in terms of the printed length; these facts let the recursion's
// budget flow from the parent's.

/// The wrapping decision only changes the length by the two parentheses.
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

/// `sprint_body(e)` is non-empty.
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

} // verus!
