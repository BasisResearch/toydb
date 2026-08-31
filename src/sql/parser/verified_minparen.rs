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
use super::{
    Keyword, Token, ast, float_trust, verified_expression, verified_precedence, verified_production,
};

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
    tail.len() == 0
        || (verified_expression::binary_from_token(tail[0]) is Some
            && binary_prec_s(verified_expression::binary_from_token(tail[0])->Some_0) < level)
        // A postfix `!` (prec 9) below `level`. The `IS` guard is tightened to
        // `8 < level` (not the minimal `4 < level`): still sound for halting, and
        // it keeps a bare binary node's tail (parsed at a level <= 8) free of an
        // `IS` head, which the spine-shape reasoning (`leaf_rest_shape`) relies
        // on. The only `IS`-headed inert tail arises in the postfix operand
        // context (level 10 > 8).
        || (tail[0] == TokenView::Exclamation && 9 < level)
        || (tail[0] == TokenView::Keyword(Keyword::Is) && 8 < level)
        // A prec-boundary token: `)` or `,` (never `.` / `(`, so a bare atom is
        // not re-read as a qualified column or a function call).
        || tail[0] == TokenView::CloseParen
        || tail[0] == TokenView::Comma
}

/// An inert tail is a `boundary` tail (never opens with `.` or `(`).
pub proof fn inert_boundary(tail: Seq<TokenView>, level: u8)
    requires
        inert(tail, level),
    ensures
        super::verified_roundtrip::boundary(tail),
{
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

/// The head token of any bare node body is an atom-start token: never `)`.
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

// ---- leftmost-leaf / spine decomposition of a bare binary node ------------
//
// When a binary node prints unwrapped at context `ctx`, the parser's lhs phase
// consumes only its *leftmost leaf* and the infix precedence-climbing loop
// replays the rest of the spine. `lleaf(e, ctx)` is that leaf; `after_leaf(e,
// ctx)` is the token stream between the leaf's print and the end of
// `sprint_body(e)`. The two satisfy `sprint_body(e) == sprint_min(lleaf, llc)
// ++ after_leaf` (`lemma_body_decomp`), where the leaf is printed at the
// context it sits in.
//
// The descent rule: from `Binary(tag, L, R)` at context `ctx` (bp = bin_prec,
// LC = bp+1-assoc) we descend into `L` only when `L` is itself a *bare* binary
// node there — `L` is `Binary(..)` with `prec_min(L) >= LC`. Otherwise `L` is
// the leaf (an atom, a prefix chain, a postfix node, or a parenthesised group).

/// The leftmost leaf of a bare binary spine and the context it is printed at.
pub open spec fn descends(l: SExpr, lc: u8) -> bool {
    l is Binary && prec_min(l) >= lc
}

/// Leftmost leaf reached by descending bare-binary left children.
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

/// The context the leftmost leaf is printed at.
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

/// The spine tokens after the leftmost leaf's print, i.e. the `[op] ++
/// sprint_min(right, rc)` productions from the leaf up to the root, innermost
/// first (matching the left-to-right token order the infix loop consumes).
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

/// The print of a bare binary node decomposes into its leftmost leaf's print
/// (at the leaf's own context) followed by the spine tokens.
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
        // sprint_min(*left, lc) = sprint_body(*left) since *left unwrapped at lc.
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

// ---- the infix-loop spine replay ------------------------------------------

/// Precedence gap under descent: if we descend into a bare left child `l` at
/// left-context `lc = bp + 1 - assoc` of a parent operator with precedence `bp`
/// and associativity `assoc`, then the parent operator binds strictly looser
/// than `l`'s right-context `bin_prec(l) + bin_assoc(l)`. This is what makes the
/// parent operator (which follows `l`'s right operand in the token stream) inert
/// against `l`'s right-context, so `l`'s right operand parse stops before it.
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
    // prec_min(l) == bin_prec(ltag) since l is Binary.
    assert(prec_min(l) == bin_prec(ltag));
    let lc = (bp + 1 - assoc) as u8;
    assert(bin_prec(ltag) >= lc);
    match ltag {
        BinaryTag::Exponentiate => {
            assert(bin_prec(ltag) == 8);
            assert(bin_assoc(ltag) == 0);
            // rc_l = 8. Need bp < 8. Only Exponentiate has precedence 8, and it is
            // associativity 0, so the parent (if prec 8) would have assoc 0, giving
            // lc = 9 > 8 = bin_prec(ltag), contradicting `descends`. Hence bp < 8.
            reveal_prec_assoc_link();
            if bp == 8 {
                assert(bin_assoc(ptag) == 0);  // ptag prec 8 => Exp => assoc 0
                assert(lc == 9);
                assert(false);
            }
            assert(bp < 8);
        },
        _ => {
            assert(bin_assoc(ltag) == 1);
            // rc_l = bin_prec(ltag) + 1 >= lc + 1 = bp + 2 - assoc >= bp + 1 > bp.
            assert(bin_prec(ltag) + 1 >= lc + 1);
        },
    }
}

/// The precedence/associativity table has a single associativity-0 operator
/// (Exponentiate, precedence 8), and it is the unique precedence-8 operator.
/// Used by `descend_gap` to rule out a precedence-8, associativity-1 parent.
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

// ---- the roundtrip induction ----------------------------------------------
//
// Three mutually recursive lemmas, on the lexicographic measure `(e, phase)`
// with `phase`: run_open = 0 < body = 1 < min = 2.
//
//   lemma_min(e, ctx, tail): sparse_prec(sprint_min(e, ctx) ++ tail, ctx) = (e, tail)
//   lemma_body(e, ctx, tail): sparse_prec(sprint_body(e) ++ tail, ctx) = (e, tail)   [prec_min(e) >= ctx]
//   lemma_run_open(e, ctx, cont): sparse_infix_loop(lleaf(e), after_leaf(e) ++ cont, ctx)
//                                   = sparse_infix_loop(e, cont, ctx)                 [e Binary, bp >= ctx]
//
// All budget their fuel as `2 * (input.len()) + 3` and normalise with
// verified_precedence's fuel-stability lemmas where a recursion's fuel differs.

/// Roundtrip for the minimal-parenthesisation printer at the `sprint_min`
/// entry: parsing `sprint_min(e, ctx)` (followed by any tail inert at `ctx`) at
/// min-precedence `ctx` recovers `e` and leaves the tail. This is the headline
/// statement (`min_roundtrip` specialises it to `ctx == 0`, `tail == empty`).
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
        // Wrapped: `( sprint_body(e) ) tail`. The lhs phase sees `(` and routes
        // to sparse_atom, which recurses sparse_prec on the body at ctx 0.
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
        // sparse_atom(input, fuel-1): OpenParen => sparse_prec(body, 0, fuel-2).
        boundary_inert(close_tail, 0);
        assert(prec_min(e) >= 0);
        lemma_body(e, 0, close_tail, (fuel - 2) as nat);
        assert(sparse_prec(body, 0, (fuel - 2) as nat) == (Some(e), close_tail));
        assert(close_tail[0] == TokenView::CloseParen);
        assert(close_tail.drop_first() =~= tail);
        // sparse_atom(input, fuel-1) sees `(`, recurses sparse_prec(body, 0, fuel-2),
        // then consumes the matching `)` -> (Some(e), tail).
        assert(sparse_atom(input, (fuel - 1) as nat) == (Some(e), tail));
        // lhs phase == sparse_atom (head is not a prefix op); then loops halt.
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
        // Unwrapped: sprint_min(e, ctx) == sprint_body(e); defer to lemma_body.
        assert(sprint_min(e, ctx) == sprint_body(e));
        lemma_body(e, ctx, tail, fuel);
    }
}

/// Roundtrip for a bare (unwrapped) node body: parsing `sprint_body(e)` at
/// min-precedence `ctx` (with `prec_min(e) >= ctx`, tail inert at `ctx`)
/// recovers `e`. Dispatches per constructor; the binary case uses the spine
/// replay (`lemma_run_open`).
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
            // Pure atom: head is not a prefix op, so the lhs phase routes to
            // sparse_atom; then both continuation loops halt on the inert tail.
            assert(verified_expression::prefix_operator(input[0]) is None) by {
                reveal(verified_expression::prefix_operator);
                sprint_body_atom_head(e);
            }
            inert_boundary(tail, ctx);
            lemma_atom_min(e, tail, (fuel - 1) as nat);
            // lhs = e via sparse_atom, after_lhs = tail; loops at ctx halt.
            inert_halts(e, tail, ctx, fuel);
        },
        SExpr::Unary(tag, inner) => {
            // Prefix op at head; recurse at pre_prec(tag) = prefix_prec_s(tag).
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
            // lhs = Unary(tag, inner), after_lhs = tail; loops at ctx halt.
            inert_halts(e, tail, ctx, fuel);
        },
        SExpr::Factorial(inner) => {
            // Body: sprint_min(inner, 10) ++ [!]. The lhs phase parses `inner`
            // (it prints at context 10, so it is an atom, a prefix chain, or a
            // parenthesised group — all consumed whole by the lhs phase), leaving
            // `[!] ++ tail`; postfix pass 1 consumes `!`; then the loops halt.
            let post = seq![TokenView::Exclamation] + tail;
            assert(prec_min(e) == 9);
            assert(9 >= ctx);
            assert(input =~= sprint_min(*inner, 10) + post);
            assert(inert(post, 10)) by { assert(post[0] == TokenView::Exclamation); }
            sprint_min_len(*inner, 10);
            lemma_lhs_high(*inner, ctx, post, fuel);
            // prec_lhs_phase == (Some(inner), post). Assemble sparse_prec:
            //   postfix1(inner, post, ctx) consumes `!` -> Factorial(inner);
            //   the remaining loops halt on the inert tail.
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

// ---- atom / function roundtrip --------------------------------------------

/// The head token of a pure atom's body (`All`, `Column`, `Literal`,
/// `Function`) is never a prefix operator.
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

/// `sparse_atom` roundtrip for pure atoms: `All`, `Column`, `Literal`,
/// `Function`. For a `Function` the arguments recurse through `lemma_min_args`.
/// The tail must be a `boundary` (never `.` or `(`) so a bare column or ident is
/// not re-read as qualified or as a call.
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
            // sprint_body = [Ident, OpenParen] ++ sprint_min_args(args) ++ [CloseParen].
            let close_tail = seq![TokenView::CloseParen] + tail;
            assert(tokens[0] == TokenView::Ident(name));
            assert(tokens[1] == TokenView::OpenParen);
            assert(tokens.subrange(2, tokens.len() as int) =~= sprint_min_args(args) + close_tail);
            lemma_min_args(args, close_tail, fuel);
            // sparse_fn_args returns (Some(args), close_tail); sparse_atom then
            // consumes the closing `)`, leaving `tail`.
            assert(close_tail[0] == TokenView::CloseParen);
            assert(close_tail.drop_first() =~= tail);
        },
        _ => {},
    }
}

/// The comma-separated argument list roundtrip, mirroring `lemma_fn_args`. The
/// list is parsed by `sparse_fn_args`; each argument at context 0 with a `,` or
/// `)` boundary following.
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

/// The head token of a non-empty min-args list is not `)` (so `sparse_fn_args`
/// takes the non-empty branch).
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

/// `sprint_min(e, ctx)`'s head is never `)`. When wrapped, it is `(`; when bare,
/// it is `sprint_body(e)`'s head, which for a printable node is an atom-start
/// (`sprint_head` gives `!= )`).
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

/// The non-empty argument list, mirroring `lemma_fn_args_nonempty`.
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

/// Length bookkeeping: the printed arg list is at least the first argument's
/// print plus (for a multi-arg list) the comma and remainder.
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

// ---- lhs-phase assembly ---------------------------------------------------

/// Assemble `sparse_prec` from its lhs phase and continuation loops: given the
/// lhs phase produced `(Some(lhs0), after)`, the full parse is the composition
/// postfix1 -> infix -> postfix2. This is exactly the definition of
/// `sparse_prec`; stated as a lemma so callers can name the pieces.
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

/// The final `SExpr` produced by `sparse_prec` when the lhs phase gives
/// `(Some(lhs0), after)`.
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

/// The final residual produced by `sparse_prec` in the same situation.
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

/// An operand printed at context 10 is consumed *whole* by the lhs phase: it is
/// an atom, a prefix chain (`+`/`-`), or a parenthesised group. So the lhs phase
/// over `sprint_min(inner, 10) ++ rest` yields `(Some(inner), rest)` for any
/// outer context `ctx <= 10`.
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
        // Wrapped: `( sprint_body(inner) )`. lhs = sparse_atom (paren group).
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
                // Only Identity/Negate reach here unwrapped (Not has prec 3 < 10).
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
                // prec_min < 10 for these, contradicting the unwrapped branch.
                assert(false);
            },
        }
    }
}

/// The postfix pass consumes a trailing `!` at context `ctx <= 9`, producing
/// `Factorial`, then halts on the inert tail.
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

/// The postfix pass consumes a trailing `IS NULL`/`IS NAN` at context `ctx <=
/// 4`, producing `Is`, then halts on the inert tail.
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

// ---- binary body via the spine replay -------------------------------------

/// The bare binary node roundtrip: the lhs phase parses the leftmost leaf, then
/// the infix loop replays the spine (`lemma_run_open`) to rebuild the node.
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
    // The lhs phase parses the leftmost leaf; the infix loop replays the spine.
    lemma_body_leaf_then_spine(e, ctx, tail, fuel);
}

/// Fuel/length bound for the binary body: enough fuel for the whole body covers
/// the leaf's print, the spine, and the tail.
pub proof fn body_binary_len(e: SExpr, ctx: u8, tail: Seq<TokenView>)
    requires
        e is Binary,
    ensures
        sprint_body(e).len()
            == sprint_min(lleaf(e, ctx), lleaf_ctx(e, ctx)).len() + after_leaf(e, ctx).len(),
{
    lemma_body_decomp(e, ctx);
}

/// Leaf parse: the lhs phase plus postfix pass 1, at context `ctx`, over a
/// non-bare-binary leaf's print followed by `rest`, reproduces the leaf and
/// leaves `rest`. `rest` must be inert at `ctx` for the postfix loop to halt
/// after the leaf's own postfix ops (a following binary operator token is inert
/// for the postfix loop; a boundary is inert for both).
#[verifier::spinoff_prover]
#[verifier::rlimit(40000)]
pub proof fn lemma_leaf_parse(leaf: SExpr, leaf_ctx: u8, ctx: u8, rest: Seq<TokenView>, fuel: nat)
    requires
        super::verified_roundtrip::printable_se(leaf),
        !descends(leaf, leaf_ctx),
        ctx <= leaf_ctx,
        // rest halts the postfix loop and does not re-read the leaf as qualified
        // / a call: it is a binary-operator head or a boundary.
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma),
        // Leaf gap (only needed for an unwrapped *prefix* leaf, whose operand is
        // parsed at `prec_min(leaf)`): the following binary operator binds
        // strictly looser than the leaf, so that operand parse stops before it.
        // Non-prefix and wrapped leaves parse their operands at context 10 or via
        // parentheses and need no gap.
        !(leaf is Unary)
            || prec_min(leaf) < leaf_ctx
            || rest.len() == 0
            || verified_expression::binary_from_token(rest[0]) is None
            || binary_prec_s(verified_expression::binary_from_token(rest[0])->Some_0)
                < prec_min(leaf),
        fuel >= 2 * (sprint_min(leaf, leaf_ctx) + rest).len() + 3,
    ensures
        // The lhs phase yields *some* node whose postfix pass 1 produces the leaf
        // and leaves `rest`. (For a postfix leaf the lhs produces the inner
        // operand and postfix pass 1 applies the `!` / `IS`; for the other leaves
        // the lhs already produces the leaf and postfix pass 1 halts.)
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
    // rest halts the postfix loop (its head is a binary op / boundary / empty).
    assert(rest_halts_postfix(rest)) by {
        if rest.len() > 0 {
            match verified_expression::binary_from_token(rest[0]) {
                Some(t) => { super::verified_roundtrip::binary_tok_roundtrip(t); },
                None => {},
            }
        }
    }
    if prec_min(leaf) < leaf_ctx {
        // Wrapped leaf: `( sprint_body(leaf) )`. lhs = sparse_atom (paren group).
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
        // sparse_atom -> (Some(leaf), rest); lhs phase == this (head not prefix).
        assert(sparse_atom(input, (fuel - 1) as nat) == (Some(leaf), rest));
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel)
            == sparse_atom(input, (fuel - 1) as nat));
        assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(leaf), rest));
        leaf_postfix_halts(leaf, rest, ctx);
    } else {
        // Unwrapped: sprint_min(leaf, leaf_ctx) == sprint_body(leaf).
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
                // rest inert at pre_prec(tag): rest's binary head has prec <
                // prec_min(leaf) == pre_prec(tag) (the leaf-gap hypothesis), and
                // `)` / `,` are boundaries.
                leaf_rest_inert(rest, pre_prec(tag));
                sprint_min_len(*x, pre_prec(tag));
                lemma_min(*x, pre_prec(tag), rest, (fuel - 1) as nat);
                // lhs phase (prefix) = Unary(tag, x) = leaf, residual rest.
                assert(sparse_prec(sprint_min(*x, pre_prec(tag)) + rest, prefix_prec_s(tag),
                    (fuel - 1) as nat) == (Some(*x), rest));
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(leaf), rest));
                leaf_postfix_halts(leaf, rest, ctx);
            },
            SExpr::Factorial(inner) => {
                // lhs parses `inner` (printed at 10); postfix1 consumes `!` then
                // halts on `rest`.
                let post = seq![TokenView::Exclamation] + rest;
                assert(input =~= sprint_min(*inner, 10) + post);
                assert(prec_min(leaf) == 9);
                assert(ctx <= 9);
                rest_post_inert(rest, TokenView::Exclamation);
                assert(inert(post, 10)) by { assert(post[0] == TokenView::Exclamation); }
                sprint_min_len(*inner, 10);
                lemma_lhs_high(*inner, ctx, post, fuel);
                assert(verified_precedence::prec_lhs_phase(input, ctx, fuel) == (Some(*inner), post));
                // postfix1 from inner over `! rest`: consume `!`, halt on rest.
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
                // Unwrapped Binary would be `descends`, contradicting the premise.
                assert(descends(leaf, leaf_ctx));
                assert(false);
            },
        }
    }
}

/// `rest` (binary-op head / boundary / empty) halts the postfix loop.
pub open spec fn rest_halts_postfix(rest: Seq<TokenView>) -> bool {
    rest.len() == 0
        || (rest[0] != TokenView::Exclamation && rest[0] != TokenView::Keyword(Keyword::Is))
}

/// From the `rest` shape, the postfix loop over `rest` halts at any level.
pub proof fn leaf_postfix_halts(leaf: SExpr, rest: Seq<TokenView>, ctx: u8)
    requires
        rest_halts_postfix(rest),
    ensures
        sparse_postfix_loop(leaf, rest, ctx) == (leaf, rest),
{
    reveal_with_fuel(sparse_postfix_loop, 1);
}

/// After parsing `inner`, postfix pass 1 consumes `!` then halts on `rest`.
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

/// After parsing `inner`, postfix pass 1 consumes `IS NULL`/`NAN` then halts.
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

/// `[op] ++ rest` (postfix op followed by a postfix-halting rest) is inert at
/// level 10 (both `!` prec 9 and `IS` prec 4 are below 10).
pub proof fn rest_post_inert(rest: Seq<TokenView>, op: TokenView)
    requires
        rest_halts_postfix(rest),
        op == TokenView::Exclamation || op == TokenView::Keyword(Keyword::Is),
    ensures
        inert(seq![op] + rest, 10),
{
    assert((seq![op] + rest)[0] == op);
}

/// A `rest` with a binary-op / boundary head is inert at a high level (>= 9):
/// every binary operator has precedence <= 8 < level.
pub proof fn rest_inert_high(rest: Seq<TokenView>, level: u8)
    requires
        level >= 9,
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma),
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

/// `rest` (binary-op / boundary head) whose binary head binds strictly below
/// `level` is inert at `level`.
pub proof fn leaf_rest_inert(rest: Seq<TokenView>, level: u8)
    requires
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma),
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

/// Every binary operator has spec precedence at most 8.
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

/// An inert tail at a level `<= 8` has the binary-op / boundary head shape
/// (`!` needs level > 9, `IS` needs level > 8, so neither can head it here).
pub proof fn inert_shape(tail: Seq<TokenView>, level: u8)
    requires
        inert(tail, level),
        level <= 8,
    ensures
        tail.len() == 0
            || (verified_expression::binary_from_token(tail[0]) is Some
                && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
            || (tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma),
{
    if tail.len() > 0 {
        match verified_expression::binary_from_token(tail[0]) {
            Some(t) => { super::verified_roundtrip::binary_tok_roundtrip(t); },
            None => {},
        }
    }
}

/// The spine head of a bare binary node binds strictly looser than a *prefix*
/// leftmost leaf: the leaf-gap needed by `lemma_leaf_parse`'s prefix case. Only
/// asserted for `Unary` leaves (`prec_min` 3 for `NOT`, 10 for `+`/`-`), which
/// are the only leaves whose operand is parsed at `prec_min(leaf)`.
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
            // Empty inner spine: the head is `bin_tok(tag)`. But an empty inner
            // spine means *left has no operators, i.e. lleaf(*left,lc) == *left is
            // a bare binary — contradicting `lleaf(...) is Unary`. So unreachable.
            after_leaf_empty_iff(*left, lc);
            assert(lleaf(*left, lc) == *left);
            assert(false);
        }
        assert(after_leaf(e, ctx)[0] == after_leaf(*left, lc)[0]);
    } else {
        // Leaf is *left (a Unary), printed at lc; spine head is `bin_tok(tag)`.
        assert(lleaf(e, ctx) == *left);
        assert(lleaf_ctx(e, ctx) == lc);
        assert(after_leaf(e, ctx)[0] == bin_tok(tag));
        assert(binary_prec_s(tag) == bin_prec(tag)) by { tables_agree(tag, UnaryTag::Not); }
        assert(prec_min(*left) >= lc);
        // *left is Unary: prec_min in {3, 10}. bin_prec(tag) <= 8 < 10, and no
        // binary op has precedence 3, so bin_prec(tag) < prec_min(*left).
        assert(*left is Unary);
        let utag = (*left)->Unary_0;
        assert(prec_min(*left) == pre_prec(utag));
        assert(pre_prec(utag) == 3 || pre_prec(utag) == 10) by {
            match utag { UnaryTag::Not => {}, UnaryTag::Identity => {}, UnaryTag::Negate => {} }
        }
        assert(bin_prec(tag) <= 8) by { binary_prec_le_8_direct(tag); }
        if pre_prec(utag) == 3 {
            // Unwrapped Not needs 3 >= lc = bp + 1 - assoc, so bp <= 2 + assoc <= 3;
            // bp != 3 (no binary prec 3), so bp <= 2 < 3.
            assert(bin_assoc(tag) == 0 || bin_assoc(tag) == 1) by {
                match tag { BinaryTag::Exponentiate => {}, _ => {} }
            }
            no_binary_prec_3(tag);
            assert(bin_prec(tag) < 3);
        }
    }
}

/// `after_leaf(e) == empty` iff `e` is not a bare-binary spine (its leftmost
/// leaf is `e` itself). Contrapositive used above: a descending child has a
/// non-empty spine.
/// `sdepth(lleaf(e, ctx)) < sdepth(e)` for a binary `e`: the leftmost leaf is a
/// strict subterm, so the leaf parse can be discharged by a lemma decreasing on
/// `sdepth`.
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

/// No binary operator has precedence 3.
pub proof fn no_binary_prec_3(t: BinaryTag)
    ensures
        bin_prec(t) != 3,
{
    match t { BinaryTag::Exponentiate => {}, _ => {} }
}

/// `bin_prec(t) <= 8` directly (spec table).
pub proof fn binary_prec_le_8_direct(t: BinaryTag)
    ensures
        bin_prec(t) <= 8,
{
    match t { BinaryTag::Exponentiate => {}, _ => {} }
}

/// An atom leaf's `rest` (binary-op / boundary / empty head) is a `boundary`.
pub proof fn atom_boundary_from_rest(rest: Seq<TokenView>)
    requires
        rest.len() == 0
            || (verified_expression::binary_from_token(rest[0]) is Some
                && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
            || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma),
    ensures
        super::verified_roundtrip::boundary(rest),
{
}

/// The bare binary node parses: lhs+postfix1 build the leftmost leaf, the infix
/// loop replays the spine (`lemma_run_open`), and postfix pass 2 halts.
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
    // `rest` starts with a binary op (spine head) or is `tail` (inert) if spine
    // is empty. Either way it satisfies lemma_leaf_parse's precondition.
    assert(bin_prec(e->Binary_0) >= ctx);
    binary_prec_le_8_direct(e->Binary_0);
    assert(ctx <= 8);
    inert_shape(tail, ctx);
    leaf_rest_shape(e, ctx, tail);
    // The leaf-gap for a prefix leaf: the spine head binds looser than the leaf.
    if leaf is Unary && prec_min(leaf) >= leaf_ctx {
        leaf_gap(e, ctx);
        // rest[0] == spine[0] when spine is non-empty.
        after_leaf_empty_iff(e, ctx);
        assert(spine.len() >= 1);
        assert(rest[0] == spine[0]);
    }
    // The lhs phase + postfix1 parse the leaf, leaving `rest`.
    leaf_parse_fuel(e, ctx, tail, fuel);
    lleaf_sdepth(e, ctx);  // sdepth(leaf) < sdepth(e), for the leaf-parse recursion.
    lemma_leaf_parse(leaf, leaf_ctx, ctx, rest, fuel);
    let lp = verified_precedence::prec_lhs_phase(input, ctx, fuel);
    let lhs0 = lp.0->Some_0;
    assert(lp.0 is Some);
    // postfix pass 1 turns the lhs result into the leftmost leaf, leaving `rest`.
    assert(sparse_postfix_loop(lhs0, lp.1, ctx) == (leaf, rest));
    // Now the infix loop replays the spine to build `e`, then postfix2 halts.
    let rc = (bin_prec(e->Binary_0) + bin_assoc(e->Binary_0)) as u8;
    inert_mono(tail, ctx, rc);
    run_open_fuel(e, ctx, tail, fuel);
    assert(spine + tail =~= after_leaf(e, ctx) + tail);
    lemma_run_open(e, ctx, tail, fuel);
    // sparse_infix_loop(leaf, spine ++ tail, ctx, fuel) == sparse_infix_loop(e,
    // tail, ctx, fuel); the inert tail then halts both remaining loops.
    assert(sparse_infix_loop(leaf, rest, ctx, fuel) == sparse_infix_loop(e, tail, ctx, fuel));
    inert_halts(e, tail, ctx, fuel);
    // Assemble sparse_prec from lhs -> postfix1 -> infix -> postfix2.
    assert(sparse_postfix_loop(lhs0, lp.1, ctx).0 == leaf);
    assert(sparse_postfix_loop(lhs0, lp.1, ctx).1 == rest);
    prec_from_lhs(input, ctx, fuel, lhs0, lp.1);
    assert(final_result_expr(input, ctx, fuel, lhs0, lp.1) == e);
    assert(final_result_rest(input, ctx, fuel, lhs0, lp.1) == tail);
}

/// The leftmost leaf of a printable bare binary node is printable.
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

/// The leaf's print context is at least `ctx` (contexts only grow on descent).
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

/// The `rest = after_leaf(e) ++ tail` satisfies `lemma_leaf_parse`'s shape:
/// a binary-op head (the shallowest spine operator) or `tail` (inert) if the
/// spine is empty.
pub proof fn leaf_rest_shape(e: SExpr, ctx: u8, tail: Seq<TokenView>)
    requires
        e is Binary,
        tail.len() == 0
            || (verified_expression::binary_from_token(tail[0]) is Some
                && tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
            || (tail[0] == TokenView::CloseParen || tail[0] == TokenView::Comma),
    ensures
        ({
            let rest = after_leaf(e, ctx) + tail;
            rest.len() == 0
                || (verified_expression::binary_from_token(rest[0]) is Some
                    && rest[0] != TokenView::Period && rest[0] != TokenView::OpenParen)
                || (rest[0] == TokenView::CloseParen || rest[0] == TokenView::Comma)
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
        // The recursion's `tail` here is `here ++ tail`, whose head is `bin_tok(tag)`
        // (a binary op), satisfying the shape hypothesis.
        assert((here + tail)[0] == bin_tok(tag));
        leaf_rest_shape(*left, lc, here + tail);
        assert(after_leaf(e, ctx) + tail =~= after_leaf(*left, lc) + (here + tail));
    } else {
        assert(after_leaf(e, ctx) =~= here);
        let rest = after_leaf(e, ctx) + tail;
        assert(rest[0] == bin_tok(tag));
    }
}

/// Fuel bound for the leaf parse: the leaf's print + `rest` fits the body budget.
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

/// Fuel bound for the spine replay: the spine + tail fits the body budget.
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

/// `after_leaf(e) <= sprint_body(e)` in length.
pub proof fn sprint_body_len_ge(e: SExpr, ctx: u8)
    requires
        e is Binary,
    ensures
        after_leaf(e, ctx).len() <= sprint_body(e).len(),
{
    lemma_body_decomp(e, ctx);
}

/// The leftmost leaf of a bare binary spine is not itself a bare binary node
/// (`!descends`): either it is not a `Binary` at all, or it is a `Binary`
/// printed *wrapped* at its context (`prec_min < lleaf_ctx`), which the parser
/// reads as a parenthesised atom.
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

/// The infix loop replays a bare binary spine: from the leftmost leaf over the
/// spine tokens, it rebuilds `e` and hands `cont` to a continued loop. No
/// inertness requirement on `cont` — this is the *open* (composable) form.
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
        // Descend: leftmost leaf comes from L; process after_leaf(L,lc) then `here`.
        assert(lleaf(e, ctx) == lleaf(*left, lc));
        assert(after_leaf(e, ctx) =~= after_leaf(*left, lc) + here);
        assert(after_leaf(e, ctx) + cont =~= after_leaf(*left, lc) + (here + cont));
        assert(prec_min(*left) >= lc);
        assert(lleaf(*left, lc) == lleaf(*left, ctx));
        assert(after_leaf(*left, lc) == after_leaf(*left, ctx));
        // The parent op `here[0]` is inert against L's right-context, so
        // `here ++ cont` is inert at L's rc — the IH's precondition.
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

/// `here ++ cont` (a parent operator's `op ++ sprint_min(r, rc) ++ cont`) is
/// inert at a child right-context `rc_l` when the parent operator binds looser
/// than `rc_l` (`bin_prec(tag) < rc_l`). The head is the parent op token, which
/// is a binary token (never `!`/`IS`) with precedence `bin_prec(tag) < rc_l`.
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

/// The single infix step for a bare binary node's top operator: starting from
/// its (already parsed) left `l`, consume `op ++ sprint_min(r, rc) ++ cont` and
/// reach the continued loop over `Binary(tag, l, r)` and `cont`. Requires the
/// continuation to be inert at the right-context `rc` so `r`'s parse stops.
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
    // right operand parses at rc leaving cont.
    sprint_min_len(r, rc);
    lemma_min(r, rc, cont, (fuel - 1) as nat);
    assert(sparse_prec(sprint_min(r, rc) + cont, next_prec, (fuel - 1) as nat) == (Some(r), cont));
    // The loop recurses with `fuel - 1`; normalise to `fuel` for the ensures.
    verified_precedence::lemma_infix_fuel(
        SExpr::Binary(tag, Box::new(l), Box::new(r)), cont, ctx, (fuel - 1) as nat, fuel);
}

/// Fuel bound bridge for the descend recursion: `after_leaf(L,lc) + (here+cont)`
/// is a subsequence of `after_leaf(e) + cont`, so the parent's budget covers it.
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

/// `bin_tok(tag)` decodes back to `Some(tag)` under `binary_from_token`.
pub proof fn binary_tok_tag(tag: BinaryTag)
    ensures
        verified_expression::binary_from_token(bin_tok(tag)) == Some(tag),
{
    super::verified_roundtrip::binary_tok_roundtrip(tag);
}

// ===========================================================================
// Headline spec roundtrip (task 2) and the residual (task 5).
// ===========================================================================

/// The minimal-parenthesisation print of any printable mirror expression
/// re-parses to that expression, consuming all tokens:
///
///   sparse_prec(sprint_min(e, 0), 0, fuel) == (Some(e), empty)
///
/// for `fuel >= 2 * sprint_min(e, 0).len() + 3`. This is the phase's core
/// guarantee: because the printer's parenthesisation decisions
/// (`bin_prec` / `bin_assoc` / `pre_prec`, checked to agree with the parser's
/// spec twins by `tables_agree`) encode the precedence/associativity table a
/// third time — independently of the parser and its spec twin — the round trip
/// FAILS unless parser, spec twin, and printer all agree on that table. A
/// mutation of the parser's table that is not mirrored in the printer breaks
/// this theorem (see the mutation check in the phase report).
///
/// Residual (task 5): a CONSISTENT swap of all three encodings (the exec table
/// `verified_precedence::binary_prec`, its spec twin `binary_prec_s`, AND this
/// module's `bin_prec`) still round-trips here — the theorem pins them to each
/// other, not to an external ground truth. The guards against a consistent swap
/// are the `op_precedence` goldenscripts and the differential harness restored
/// in phase 0, which compare the parser against externally-fixed SQL semantics.
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

} // verus!
