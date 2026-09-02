# Phase 1: verified-but-unexecuted flagger

Branch `kg/parser-fix-phase-1-coverage` off `kg/verified-parser-cutover`.

## Context (self-contained)

A review found that this repo's largest verified artefacts are dead
code: production calls `verified_control::parse_control_at` (weak
no-panic contract), while the round-trip-proven parsers in
`src/sql/parser/verified_stmt.rs` (8,543 lines,
`#![allow(dead_code)]`), `verified_lexer.rs` (`lex_all_exec`), and
`verified.rs` are never called. No tooling caught this. Build the tool
that does: flag any verified exec function that tests never execute,
and any verified function unreachable from production entry points.

Existing infrastructure to reuse, all under `scripts/verus/`:

- `verify.sh` — runs `cargo verus focus` over an explicit module list; CI
  runs exactly this script.
- `extract_metrics.py` — already parses Verus `--output-json` output,
  including per-function `func-details`, for dashboard coverage metrics
  (functions_verified / functions_total etc.).
- `extract_graph.py` — extracts a file/module/function-level graph with
  nodes and edges per `CONTRACTS.md` (repo one level up); has a static
  Rust structure-extraction fallback when Verus dependency info is absent.
- `test_extract.py` — existing test conventions for these scripts.

## Tasks

1. New script `scripts/verus/verified_coverage.py` with two lenses:
   - **Dynamic.** Build the verified-function set (name, file, line span)
     from Verus JSON func-details via the `extract_metrics.py` machinery.
     Partition exec functions from spec/proof functions: ghost code is
     erased from the normal build, can never execute, and must be reported
     separately, never flagged. Get per-line execution counts from
     `cargo llvm-cov test --lib --json` (install `cargo-llvm-cov` if
     missing; goldenscripts run under the lib test harness, so they count).
     Join on file + line range: a verified exec function whose span has
     zero executed lines is flagged. Roll up per module.
   - **Static.** Using the `extract_graph.py` call graph, compute
     reachability from the production entry points (`Session::execute` in
     `src/sql/execution/session.rs`, `Parser::parse` in
     `src/sql/parser/parser.rs`). Verified exec functions outside the
     reachable set get a second flag. This catches a twin that has its own
     unit tests (so coverage looks fine) but that production can never
     reach. If the graph's edge extraction is too coarse for function-level
     reachability, say so in the report and flag at module level.
2. Output modes: a human-readable table; a JSON block shaped for the
   dashboard ingest alongside the existing metrics (follow `CONTRACTS.md`);
   and `--check`, which exits nonzero when the flagged set minus a
   committed allowlist file (`scripts/verus/verified_coverage_allow.txt`)
   is nonempty.
3. Seed the allowlist with the currently-known dead modules, each with a
   one-line reason and a pointer to the phase that clears it (phase 4).
4. Tests in the style of `test_extract.py`: span-join logic, exec/ghost
   partition, allowlist filtering. Use fixtures, not live cargo runs.
5. Wire `--check` into CI next to the verus-gate job if a workflow file
   exists in-repo; otherwise document the invocation in the script header.

## Constraints

- Python, stdlib only, matching the existing scripts' conventions
  (SPDX headers, docstrings, best-effort/never-raising metrics style).
- No changes to Rust source.
- Do not push or open a PR; commit locally and report.

## Acceptance

- On this branch, the tool (without the allowlist) flags at minimum:
  the exec layer of `src/sql/parser/verified_stmt.rs`
  (`parse_stmt_exec`, `parse_stmt_full_exec`), `lex_all_exec` in
  `verified_lexer.rs`, and `verified.rs`. Include the tool's own output in
  your report.
- With the seeded allowlist, `--check` passes.
- `python3 scripts/verus/test_extract.py` and the new tests pass.
- `scripts/verus/verify.sh` and `cargo test --lib` are untouched and green.
