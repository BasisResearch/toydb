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
//! The headline result is `roundtrip_demo`: running the executable parser on a
//! printer-shaped token vector recovers the full structural view of the input
//! expression, over real `Vec`s, with no axioms.
//!
//! Types here are a minimal `Atom` / `Function` grammar standing in for the
//! production AST; extending the exec parser to the whole `ast::Expression`
//! operator set (reusing the mirror + refinement pattern) is the Phase 2/4
//! cutover tracked in `verus-parser-roundtrip-plan.md`.

// `roundtrip_demo`'s `e` and `consumed` are used only in ghost positions, which
// the non-Verus build erases; the module is verification scaffolding.
#![allow(dead_code, unused_variables)]

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

// ---- exec parser refining `sparse` ----------------------------------------

pub fn parse_exec(toks: &Vec<Tok>, pos: usize, fuel: usize) -> (r: (Option<Expr>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = toks@.subrange(pos as int, toks@.len() as int);
        let (sopt, srest) = sparse(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(e) => sopt is Some
                    && view_expr(e) == sopt.unwrap()
                    && srest == toks@.subrange(r.1 as int, toks@.len() as int),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse, 1);
    let ghost input = toks@.subrange(pos as int, toks@.len() as int);
    if fuel == 0 || pos >= toks.len() {
        assert(fuel == 0 || input.len() == 0);
        return (None, pos);
    }
    assert(input[0] == toks@[pos as int]);
    match toks[pos] {
        Tok::Num(n) => {
            let is_func = pos + 1 < toks.len() && matches!(toks[pos + 1], Tok::LParen);
            if is_func {
                assert(input.len() >= 2 && input[1] == Tok::LParen) by {
                    assert(input[1] == toks@[pos as int + 1]);
                }
                assert(input.drop_first().drop_first()
                    =~= toks@.subrange(pos as int + 2, toks@.len() as int));
                let (aopt, apos) = parse_args_exec(toks, pos + 2, fuel - 1);
                match aopt {
                    Some(args) => {
                        if apos < toks.len() && matches!(toks[apos], Tok::RParen) {
                            assert(toks@.subrange(apos as int, toks@.len() as int)[0]
                                == toks@[apos as int]);
                            assert(toks@.subrange(apos as int, toks@.len() as int).drop_first()
                                =~= toks@.subrange(apos as int + 1, toks@.len() as int));
                            (Some(Expr::Func(n, args)), apos + 1)
                        } else {
                            (None, pos)
                        }
                    },
                    None => (None, pos),
                }
            } else {
                assert(!(input.len() >= 2 && input[1] == Tok::LParen)) by {
                    if input.len() >= 2 {
                        assert(input[1] == toks@[pos as int + 1]);
                    }
                }
                assert(input.drop_first() =~= toks@.subrange(pos as int + 1, toks@.len() as int));
                (Some(Expr::Atom(n)), pos + 1)
            }
        },
        _ => {
            (None, pos)
        },
    }
}

pub fn parse_args_exec(toks: &Vec<Tok>, pos: usize, fuel: usize) -> (r: (Option<Vec<Expr>>, usize))
    requires pos <= toks.len(),
    ensures ({
        let input = toks@.subrange(pos as int, toks@.len() as int);
        let (sopt, srest) = sparse_args(input, fuel as nat);
        &&& pos <= r.1 <= toks@.len()
        &&& match r.0 {
                Some(v) => sopt is Some
                    && view_args(v@) == sopt.unwrap()
                    && srest == toks@.subrange(r.1 as int, toks@.len() as int),
                None => sopt is None,
            }
    }),
    decreases fuel,
{
    reveal_with_fuel(sparse_args, 1);
    let ghost input = toks@.subrange(pos as int, toks@.len() as int);
    if fuel == 0 || pos >= toks.len() {
        assert(fuel == 0 || input.len() == 0);
        return (None, pos);
    }
    assert(input[0] == toks@[pos as int]);
    if matches!(toks[pos], Tok::RParen) {
        let v: Vec<Expr> = Vec::new();
        assert(view_args(v@) =~= Seq::<SExpr>::empty());
        return (Some(v), pos);
    }
    let (eopt, epos) = parse_exec(toks, pos, fuel - 1);
    match eopt {
        Some(e) => {
            if epos >= toks.len() {
                (None, pos)
            } else {
                assert(toks@.subrange(epos as int, toks@.len() as int)[0] == toks@[epos as int]);
                match toks[epos] {
                    Tok::RParen => {
                        let mut v: Vec<Expr> = Vec::new();
                        v.push(e);
                        assert(v@ =~= seq![e]);
                        assert(view_args(v@) =~= seq![view_expr(e)]) by {
                            assert(v@.len() == 1);
                            assert(v@[0] == e);
                            assert(v@.drop_first() =~= Seq::<Expr>::empty());
                            assert(view_args(Seq::<Expr>::empty()) == Seq::<SExpr>::empty());
                        }
                        (Some(v), epos)
                    },
                    Tok::Comma => {
                        assert(toks@.subrange(epos as int, toks@.len() as int).drop_first()
                            =~= toks@.subrange(epos as int + 1, toks@.len() as int));
                        let (mopt, mpos) = parse_args_exec(toks, epos + 1, fuel - 1);
                        match mopt {
                            Some(mut more) => {
                                let mut v: Vec<Expr> = Vec::new();
                                v.push(e);
                                let ghost more_old = more@;
                                v.append(&mut more);
                                assert(v@ =~= seq![e] + more_old);
                                assert(view_args(v@) =~= seq![view_expr(e)] + view_args(more_old)) by {
                                    assert(v@[0] == e);
                                    assert(v@.drop_first() =~= more_old);
                                }
                                (Some(v), mpos)
                            },
                            None => (None, pos),
                        }
                    },
                    _ => (None, pos),
                }
            }
        },
        None => (None, pos),
    }
}

// ---- end-to-end roundtrip: parse recovers the full structural view ---------

/// Running the executable parser on a printer-shaped token vector recovers the
/// input expression up to its structural view, over real `Vec` arguments.
pub fn roundtrip_demo(e: &Expr, toks: &Vec<Tok>) -> (out: Expr)
    requires toks@ == sprint(view_expr(*e)),
    ensures view_expr(out) == view_expr(*e),
{
    let fuel = toks.len();
    proof {
        assert(toks@.subrange(0int, toks@.len() as int) =~= toks@);
        sdepth_le_len(view_expr(*e));
        lemma_sparse_sprint(view_expr(*e), Seq::empty(), fuel as nat);
        assert(sprint(view_expr(*e)) + Seq::<Tok>::empty() =~= sprint(view_expr(*e)));
    }
    let (res, consumed) = parse_exec(toks, 0, fuel);
    match res {
        Some(out) => out,
        None => {
            proof { assert(false); }
            Expr::Atom(0)
        },
    }
}

} // verus!
