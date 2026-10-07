# Trace-step validation

Baseline: `c23eebe8` on `yl/raft-safety-refine`. Implementation branch:
`kg/trace-step-macro`. Tests run on aws-dev with Rust 1.97.1 and the pinned
`basis-11305b4a05` TLC jar.

- All **58 goldenscript logs / 2,786 model transitions conform**. Normalizing the
  new framed logs gives exactly the same headers and model-step records as the
  pre-migration logs, not just the same TLC verdict.
- Both original negative fixtures still diverge: bad ack at step **10**, bad
  quorum at step **15**.
- A 20-step election log converted to diffs conforms after reconstruction.
- Appending an unfinished `t_panicked` begin to that log causes the runner to
  reject it at step **21**, with exit status 1, before TLC can accept the prefix.
- The 305 library tests pass both with and without `tla-trace`. The complete
  `cargo test` suites pass with and without the feature, including five integration
  tests in each run.
- The emitter has **15 unit/integration tests**, **7 doctests** (including five
  compile-fail cases), and **7 Python reader tests**. Coverage includes nested
  calls, early returns, disabled tracing, moved and concurrent objects, caught
  panics, automatic IDs and collisions, generic equality interning, collections,
  enum encoding, field removal, cfg preservation (including inactive unsupported
  signatures), impl-member overrides (direct, conditional, and aliased, including
  log-handle replacement), explicit constructor opt-outs, and equality-preserving
  generic interning with explicit default and custom collection hashers.
- An additional **exporter-backed integration test** runs in the trace CI job
  with Java and the pinned jar. Full and diff logs containing reserved field
  names and nested unit tuples conform; incorrect record and enum field values
  diverge. Legacy logs with omitted `state`, `params`, or both have identical
  direct and normalized TLC verdicts. The real export checks the raw parameter
  `r#type` under its exported name `r_type`; changing only that parameter makes
  the trace diverge. The fixture and regeneration instructions
  are in [tests/exporter/README.md](tests/exporter/README.md).
- Formatting and warnings-as-errors Clippy pass for the root with tracing, the
  emitter, and the proc-macro crate. CI includes the reader and macro checks.
- Each goldenscript TLC invocation uses a 120-second timeout; the full runner was additionally
  bounded to 1,800 seconds. No Verus proof bodies changed or were reverified.

## Instrumentation size

Count nonblank, non-comment code lines (including braces and attributes), excluding
unchanged test-harness log setup. The baseline emitter includes the shell's local
macro, observer bridge, all 20 emission invocations and their tracing-only control
flow. The new emitter includes the complete adapter module and the shell's module
registration, model bridge, and restart invocation. Both include the dedicated
`refine::tla_view` state observer, including its feature attribute.

| Component | Before | After |
| --- | ---: | ---: |
| Emission and boundary adapters | 79 | 176 |
| State observer | 68 | 68 |
| **Total instrumentation code lines** | **147** | **244** |
| Emission call sites / annotated methods | 20 | 15 |

**This is not a Raft line-count reduction.** The 97 additional lines make the
boundaries explicit and begin-framed, while keeping the verified core untouched.
Raft's verified calls can implement several model steps and its observer reads
storage; pretending each existing shell method is one model step would be wrong.
The cheap path demonstrated in README is a structural `Observe` derive, a trace
field, and an impl annotation. It does not need these adapters.

## Compatibility and remaining limits, in priority order

1. **Normalize v2 before old checker tools.** The header's `format`, begin/end
   framing, and optional `diff`/`remove` are new. `normalize.py` is the adapter;
   `tla/conform.sh` invokes it automatically. No exporter or MCP binary was changed.
2. **Borrowed returns and asynchronous methods need explicit boundaries.** The
   attribute rejects these rather than logging an inaccurate post-state. The
   same applies to const methods and consuming receivers; impls use `trace_skip`.
3. **Raft recovery and races have scope limits.** The restart event observes
   recovered storage, but the recovery preceding it is not framed. Shared-object
   trace reservations serialize execution and can perturb concurrent bugs.
4. **Diffs are field-level; interning retains equality representatives.** Changed
   collections are emitted whole, and interning uses linear lookup. No claims
   of byte-level identity or sublinear sequence-update logging are made.
