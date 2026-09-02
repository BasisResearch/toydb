# Phase 5: retire the legacy oracle (judgment call; last)

Branch `kg/parser-fix-phase-5-retire`, only after phases 2 and 3 have
landed and `scripts/verus/verified_coverage.py --check` is green.

## Context (self-contained)

Phase 0 restored the legacy recursive-descent parser and the differential
harness under `#[cfg(test)]` as the behavioural oracle, because the verified
parser's specs were too weak to stand alone. Phases 2 and 3 changed that:
the live parser now refines a full statement-level spec and carries a
min-parens round trip that pins precedence and associativity. The remaining
gap the oracle covers is the consistent-triple-swap residual (parser table,
spec twin, and printer table all wrong in the same way) plus concrete
error-message text.

## Tasks

1. Decide: delete the legacy parser + differential harness again, or keep
   them permanently as cheap `#[cfg(test)]` insurance. Default
   recommendation: keep the differential harness, delete the rest, unless
   maintaining the legacy parser against grammar changes has become the
   dominant cost. Whichever way, record the rationale in
   `verus-parser-roundtrip-plan.md`.
2. If deleting: this is a redo of `ee8d73d` — reuse its shape, and confirm
   the goldenscript `op_precedence` tests and the phase 3 mutation
   arguments are cited in the commit message as the remaining guards.
3. Update all guarantee-stating docs (parser.rs header, plan doc) to the
   final story: what is proven, what is tested, what is trusted.

## Acceptance

- `scripts/verus/verify.sh` green; `cargo test --lib` green;
  `verified_coverage.py --check` green.
- The stated-guarantee text matches what the theorems actually say; quote
  both in the report.
