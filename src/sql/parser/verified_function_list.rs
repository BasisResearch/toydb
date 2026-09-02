//! Verified comma-list function-call roundtrip over an executable parser.
//!
//! This module is the axiom-free template for parsing `Function(name, args)`
//! nodes, the one production expression form the spec-parser core in
//! `verified_expression.rs` cannot reach. Two facts force the design:
//!
//! 1. **Termination through `Vec<Expression>`.** A production `Vec` exposes no
//!    structural termination measure, so naive `decreases *e, args.len()`
//!    recursion is rejected. The fix is a spec height (`sdepth` / `slist_depth`)
//!    whose list component decreases on the argument *sequence* itself (a Verus
//!    well-founded value), not on `args.len()` (an `int`, which is type-
//!    incompatible in the mutual-recursion group).
//!
//! 2. **`Vec` is opaque in the spec logic.** Verus has no spec-level `Vec`
//!    constructor and `Vec` equality is not determined by its view (not even
//!    deeply: `v1@ == v2@` does not give `v1 == v2`). So a *spec* parser cannot
//!    build a `Function(name, Vec)` node, and no spec proof can recover `Vec`
//!    equality from element equality. The parser must therefore be an **exec**
//!    function that builds `Vec`s at runtime, verified against a `Seq`-based
//!    mirror AST (`SExpr`) at the level of a structural view (`view_expr`).
//!
//! Types here are a minimal `Atom` / `Function` grammar standing in for the
//! production AST. The pattern this module pioneered (exec parser over real
//! `Vec`s verified against a `Seq` mirror) was reused for the whole grammar in
//! `verified_roundtrip` / `verified_precedence`; the exec demo layer here
//! (`parse_exec` / `parse_args_exec` / `roundtrip_demo`), which nothing ever
//! called, was deleted in phase 4 — the spec
//! mirror and its roundtrip lemmas remain as the template's record.

// Ghost items are erased by the non-Verus build; the module is verification
// scaffolding.
#![allow(dead_code, unused_variables)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Tok { Num(u64), LParen, RParen, Comma }

// ---- Seq-based mirror (specification vehicle) ------------------------------

/// Mirror of the production AST that stores its argument list as a `Seq`. Unlike
/// `Vec`, `Seq` is spec-constructible and extensional, so `Func` equality
/// reduces to `Seq` equality of the arguments and the roundtrip below closes.
pub enum SExpr { Atom(u64), Func(u64, Seq<SExpr>) }

pub open spec fn sprint(e: SExpr) -> Seq<Tok>
    decreases e,
{
    match e {
        SExpr::Atom(n) => seq![Tok::Num(n)],
        SExpr::Func(name, args) =>
            seq![Tok::Num(name), Tok::LParen] + sprint_args(args) + seq![Tok::RParen],
    }
}

pub open spec fn sprint_args(args: Seq<SExpr>) -> Seq<Tok>
    decreases args,
{
    if args.len() == 0 {
        Seq::empty()
    } else if args.len() == 1 {
        sprint(args[0])
    } else {
        sprint(args[0]) + seq![Tok::Comma] + sprint_args(args.drop_first())
    }
}

/// Fuel measure for the parser. The `Func` case bounds the fuel needed to parse
/// all arguments; `slist_depth` decreases on the argument sequence, keeping it
/// type-compatible with `sdepth`'s datatype measure in the mutual recursion.
pub open spec fn sdepth(e: SExpr) -> nat
    decreases e,
{
    match e {
        SExpr::Atom(_) => 1,
        SExpr::Func(_, args) => 1 + slist_depth(args),
    }
}

pub open spec fn slist_depth(args: Seq<SExpr>) -> nat
    decreases args,
{
    if args.len() == 0 {
        1
    } else {
        let d = sdepth(args[0]);
        let rest = slist_depth(args.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

/// A trailing token stream is a safe boundary for an atom when it does not open
/// with `(`, so a bare atom is never re-read as a function call.
pub open spec fn boundary(tail: Seq<Tok>) -> bool {
    tail.len() == 0 || tail[0] != Tok::LParen
}

pub open spec fn sparse(input: Seq<Tok>, fuel: nat) -> (Option<SExpr>, Seq<Tok>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            Tok::Num(n) => {
                if input.len() >= 2 && input[1] == Tok::LParen {
                    match sparse_args(input.drop_first().drop_first(), (fuel - 1) as nat) {
                        (Some(args), rest) if rest.len() > 0 && rest[0] == Tok::RParen =>
                            (Some(SExpr::Func(n, args)), rest.drop_first()),
                        _ => (None, input),
                    }
                } else {
                    (Some(SExpr::Atom(n)), input.drop_first())
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_args(input: Seq<Tok>, fuel: nat) -> (Option<Seq<SExpr>>, Seq<Tok>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else if input[0] == Tok::RParen {
        (Some(Seq::empty()), input)
    } else {
        match sparse(input, (fuel - 1) as nat) {
            (Some(e), rest) => {
                if rest.len() == 0 {
                    (None, input)
                } else if rest[0] == Tok::RParen {
                    (Some(seq![e]), rest)
                } else if rest[0] == Tok::Comma {
                    match sparse_args(rest.drop_first(), (fuel - 1) as nat) {
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

pub proof fn reveal_first_token(e: SExpr)
    ensures sprint(e).len() > 0, sprint(e)[0] is Num,
{
    match e {
        SExpr::Atom(n) => {},
        SExpr::Func(name, args) => {
            assert((seq![Tok::Num(name), Tok::LParen] + sprint_args(args) + seq![Tok::RParen])[0]
                == Tok::Num(name));
        },
    }
}

pub proof fn lemma_sparse_sprint(e: SExpr, tail: Seq<Tok>, fuel: nat)
    requires fuel >= sdepth(e), boundary(tail),
    ensures sparse(sprint(e) + tail, fuel) == (Some(e), tail),
    decreases e,
{
    reveal_with_fuel(sparse, 1);
    match e {
        SExpr::Atom(n) => {
            let tokens = sprint(e) + tail;
            assert(tokens[0] == Tok::Num(n));
            assert(tokens.drop_first() =~= tail);
            if tokens.len() >= 2 {
                assert(tokens[1] == tail[0]);
            }
        },
        SExpr::Func(name, args) => {
            let body = sprint_args(args);
            let inner_tail = seq![Tok::RParen] + tail;
            lemma_sparse_args_sprint(args, inner_tail, (fuel - 1) as nat);
            let tokens = sprint(e) + tail;
            assert(tokens[0] == Tok::Num(name));
            assert(tokens[1] == Tok::LParen);
            assert(tokens.drop_first().drop_first() =~= body + inner_tail);
            assert(inner_tail[0] == Tok::RParen);
            assert(inner_tail.drop_first() =~= tail);
        },
    }
}

pub proof fn lemma_sparse_args_sprint(args: Seq<SExpr>, tail: Seq<Tok>, fuel: nat)
    requires fuel >= slist_depth(args), tail.len() > 0, tail[0] == Tok::RParen,
    ensures sparse_args(sprint_args(args) + tail, fuel) == (Some(args), tail),
    decreases args,
{
    reveal_with_fuel(sparse_args, 1);
    if args.len() == 0 {
        assert(sprint_args(args) + tail =~= tail);
    } else if args.len() == 1 {
        lemma_sparse_sprint(args[0], tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + tail);
        reveal_first_token(args[0]);
        assert(seq![args[0]] =~= args);
    } else {
        let rest_args = args.drop_first();
        let comma_tail = seq![Tok::Comma] + sprint_args(rest_args) + tail;
        lemma_sparse_sprint(args[0], comma_tail, (fuel - 1) as nat);
        lemma_sparse_args_sprint(rest_args, tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + comma_tail);
        reveal_first_token(args[0]);
        assert(comma_tail[0] == Tok::Comma);
        assert(comma_tail.drop_first() =~= sprint_args(rest_args) + tail);
        assert(seq![args[0]] + rest_args =~= args);
    }
}

pub proof fn sdepth_le_len(e: SExpr)
    ensures sdepth(e) <= sprint(e).len(),
    decreases e,
{
    match e {
        SExpr::Atom(_) => {},
        SExpr::Func(_, args) => { slist_depth_le_len(args); },
    }
}

pub proof fn slist_depth_le_len(args: Seq<SExpr>)
    ensures slist_depth(args) <= sprint_args(args).len() + 1,
    decreases args,
{
    if args.len() == 0 {
    } else if args.len() == 1 {
        sdepth_le_len(args[0]);
        reveal_first_token(args[0]);
        assert(slist_depth(args.drop_first()) == 1);
        assert(sprint_args(args) == sprint(args[0]));
    } else {
        sdepth_le_len(args[0]);
        slist_depth_le_len(args.drop_first());
        reveal_first_token(args[0]);
        assert(sprint_args(args)
            == sprint(args[0]) + seq![Tok::Comma] + sprint_args(args.drop_first()));
    }
}

// ---- production-shaped exec AST + structural view --------------------------

/// Executable AST whose function arguments are a real `Vec`, mirroring the shape
/// of `ast::Expression::Function(String, Vec<Expression>)`.
pub enum Expr { Atom(u64), Func(u64, Vec<Expr>) }

pub open spec fn view_expr(e: Expr) -> SExpr
    decreases e,
{
    match e {
        Expr::Atom(n) => SExpr::Atom(n),
        Expr::Func(name, args) => SExpr::Func(name, view_args(args@)),
    }
}

pub open spec fn view_args(args: Seq<Expr>) -> Seq<SExpr>
    decreases args,
{
    if args.len() == 0 {
        Seq::empty()
    } else {
        seq![view_expr(args[0])] + view_args(args.drop_first())
    }
}

} // verus!
