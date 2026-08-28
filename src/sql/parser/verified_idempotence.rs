//! Parser idempotence at the token level, in three phases.
//!
//! The roundtrip proofs in `verified_roundtrip` / `verified_stmt` fix one
//! direction: for a *printable* AST `a`, parsing its canonical print recovers
//! `a` (`parse(print(a)) == a`). This module states the complementary,
//! input-driven property — *parse idempotence*:
//!
//! ```text
//!     for every token sequence `toks`,
//!     if parse(toks) = Some(a) then parse(print(a)) = parse(toks).
//! ```
//!
//! i.e. `parse ∘ print ∘ parse == parse`. Re-printing what you parsed and
//! parsing that again lands exactly where the first parse did. It is proved by
//! composing three phases:
//!
//! - **Phase 1 — parse image is printable.** `parse(toks) = Some(a)` implies
//!   `printable(a)`. Every *structural* case holds: columns, `*`, functions,
//!   and the operator forms build printable nodes whenever their children are
//!   printable, and the integer/keyword/string literal leaves land in the
//!   printable set (`parse_literal_views` yields a non-negative integer or a
//!   `Null`/`Boolean`/`String`). Phase 1 is therefore true on the finite-float
//!   fragment — but *not universally*. A number token such as `1e400` lexes and
//!   parses to `Literal::Float(inf)`, which `printable_literal` rejects (it
//!   demands `is_finite`), because Rust prints `inf` as the text `"inf"`, which
//!   re-lexes as an identifier rather than a number. So the parser can emit an
//!   AST that does not roundtrip, and idempotence genuinely fails there. This
//!   is the same load-bearing finite guard the float-trust decision rests on
//!   (`x.is_finite()` is not decoration). Consequently the `printable`
//!   hypothesis on the Phase-3 headlines below is *necessary*, not a temporary
//!   crutch: it carves out exactly the inputs whose parse the printer can
//!   reproduce. Discharging it for a given input reduces to showing the parsed
//!   literals are finite and in range.
//!
//! - **Phase 2 — printer right-inverts on the printable image.**
//!   `printable(a) ==> parse(print(a)) = (Some(a), [])`. This is exactly the
//!   existing roundtrip lemma (`lemma_sparse_sprint` for expressions,
//!   `lemma_sparse_stmt_sprint` for statements); it is reused verbatim.
//!
//! - **Phase 3 — idempotence.** Compose 1 and 2: parsing `toks` gives
//!   `(Some(a), tail)`; Phase 2 turns `print(a)` back into `(Some(a), [])`; so
//!   the two parses agree (exactly when `tail` is empty, and always on the AST
//!   component).
//!
//! Everything here is axiom-free: the headlines only compose lemmas already
//! proved in the roundtrip modules. Both the expression grammar (`SExpr`) and
//! the full statement grammar (`SStmt`) are covered.

#![allow(dead_code, unused_variables)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
// All items used here are ghost (spec/proof); gate the imports behind
// `verus_keep_ghost` so a plain `cargo build` (which strips ghost code) still
// resolves. This module defines no executable functions.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::{
    SExpr, boundary, lemma_sparse_sprint, printable_se, sdepth, sparse, sprint,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_stmt::{
    SStmt, lemma_sparse_stmt_sprint, printable_stmt, sdepth_stmt, sparse_stmt, sprint_stmt,
};

verus! {

// ---- Phase 3 headlines: idempotence, given the Phase 1 printability side-condition ----
//
// These carry `printable` as a hypothesis. Per Phase 1 (module docs), that
// hypothesis is necessary: the parser can produce non-printable infinite-float
// ASTs (from overflow number tokens like `1e400`) that do not roundtrip, so the
// headlines hold exactly on the finite-float fragment `printable` carves out.
// The composition itself — Phase 2 turning `print(a)` back into `(Some(a), [])`
// — is proved here.

/// Expression idempotence, full-consume form. When `toks` parses to `e` with no
/// leftover, re-parsing `print(e)` reproduces that parse exactly:
/// `parse(print(e)) == parse(toks)`. This is the token-level statement of
/// `parse(prettyprint(ast)) = parse(input)` for a fully-consumed input.
pub proof fn lemma_parse_idempotent_expr(
    input: Seq<TokenView>,
    e: SExpr,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse(input, fuel) == (Some(e), Seq::<TokenView>::empty()),
        printable_se(e),
        fuel2 >= sdepth(e),
    ensures
        sparse(sprint(e), fuel2) == sparse(input, fuel),
{
    // Phase 2: printer right-inverse with the empty tail (boundary(empty) holds).
    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel2);
    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
    // Now sparse(sprint(e), fuel2) == (Some(e), []) == sparse(input, fuel).
}

/// Expression idempotence, AST-component form (tail-agnostic). Even when the
/// first parse leaves a leftover `tail`, the AST recovered by re-parsing
/// `print(e)` equals the AST of the original parse.
pub proof fn lemma_parse_idempotent_expr_ast(
    input: Seq<TokenView>,
    e: SExpr,
    tail: Seq<TokenView>,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse(input, fuel) == (Some(e), tail),
        printable_se(e),
        fuel2 >= sdepth(e),
    ensures
        sparse(sprint(e), fuel2).0 == sparse(input, fuel).0,
{
    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel2);
    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
}

/// Statement idempotence, full-consume form: `parse(print(s)) == parse(toks)`
/// when `toks` parses to statement `s` with no leftover. This is the headline
/// property `parse(prettyprint(ast)) = parse(input)` over the whole SQL
/// statement grammar.
pub proof fn lemma_parse_idempotent_stmt(
    input: Seq<TokenView>,
    s: SStmt,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse_stmt(input, fuel) == (Some(s), Seq::<TokenView>::empty()),
        printable_stmt(s),
        fuel2 >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel2) == sparse_stmt(input, fuel),
{
    // Phase 2 for statements: sparse_stmt(sprint_stmt(s), fuel2) == (Some(s), []).
    lemma_sparse_stmt_sprint(s, fuel2);
}

/// Statement idempotence, AST-component form (tail-agnostic).
pub proof fn lemma_parse_idempotent_stmt_ast(
    input: Seq<TokenView>,
    s: SStmt,
    tail: Seq<TokenView>,
    fuel: nat,
    fuel2: nat,
)
    requires
        sparse_stmt(input, fuel) == (Some(s), tail),
        printable_stmt(s),
        fuel2 >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel2).0 == sparse_stmt(input, fuel).0,
{
    lemma_sparse_stmt_sprint(s, fuel2);
}

} // verus!
