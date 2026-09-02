# Phase 7: the token-stream dual — print_min ∘ parse = id on normal forms

Branch `kg/parser-fix-phase-7-token-dual`, off `kg/verified-parser-cutover`.
Independent of phases 4/6 (touches only `verified_minparen.rs` /
`verified_precedence.rs` doc-wise; new proofs go in `verified_minparen.rs`
or a sibling module).

## Context (self-contained)

`verified_minparen.rs` proves the AST-side roundtrip:

- `min_roundtrip`: `sparse_prec(sprint_min(e, 0), 0, fuel) == (Some(e), empty)`
- `min_roundtrip_live`: lifted to production `parse_expression_at`.

The dual direction — `print(parse(toks)) == toks` for ALL accepted token
streams — is impossible for any deterministic printer: `1 + 2`, `(1 + 2)`,
`((1 + 2))` parse to the same AST, which prints one way. The strongest true
dual restricts to the printer's image (min-parens normal forms), and it
makes parse/print a bijection between ASTs and normal-form streams.

## Tasks

1. Define the normal-form predicate extensionally:
   `spec fn min_normal(toks: Seq<TokenView>) -> bool` :=
   `exists e. printable_se(e) && wf_se(e) && sprint_min(e, 0) == toks`
   (reuse whatever well-formedness the roundtrip already assumes on `e`;
   inspect `min_roundtrip`'s requires).
2. The dual theorem, spec level: for `min_normal(toks)`,
   `sparse_prec(toks, 0, expr_fuel(toks)).0 is Some` and
   `sprint_min(sparse_prec(...).0.unwrap(), 0) == toks`, with the parse
   consuming all tokens. This should be a short corollary of
   `min_roundtrip` (unpack the existential witness, apply the roundtrip,
   rewrite). If it is NOT short, report why before sinking time.
3. Parser injectivity on normal forms, as a named corollary: if
   `min_normal(t1)`, `min_normal(t2)` and both parse to the same
   expression, then `t1 == t2`.
4. The normalisation statement for arbitrary accepted streams, exec level:
   for any toks where `parse_expression_at` accepts consuming all input,
   `print_min_expr(result)` re-parses to the same AST (live-parser
   corollary of `min_roundtrip_live`; mind the printable_se side
   condition — the parser can produce expressions with e.g. negative
   literals? Check: it cannot — leading `-` parses as Negate — but VERIFY
   which side conditions hold for parser-produced ASTs and state the
   theorem with exactly those).
5. Doc comment at the `min_roundtrip` site: state the bijection picture
   (parse/print inverse on ASTs × normal forms; arbitrary accepted streams
   normalise) and WHY the unrestricted dual is impossible, so nobody
   re-attempts it.

## Stretch (attempt only if 1-4 land quickly)

6. An intrinsic (structural, non-existential) characterisation of
   `min_normal` — a no-redundant-parens predicate over token streams proven
   equivalent to the extensional definition. This is the hard direction;
   timebox it and report partial progress rather than forcing it.

## Constraints

- No changes to exec parser or printer behaviour; proofs and docs only
  (plus any new spec fns).
- Do not push or open a PR; commit locally and report.
- cargo-verus caches by content hash; "Finished in 0.05s" is cache replay.
  Delete target/verus-partial/debug/.fingerprint/toydb-* to force a real
  run. Toolchain: export PATH="$HOME/.local/verus/verus-arm64-macos:$PATH".

## Acceptance

- `scripts/verus/verify.sh` fresh run, 0 errors; `cargo test --lib` green.
- Report the exact theorem statements as committed, and which tasks (1-6)
  landed.
