#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
"""Tests for verified_coverage.py (stdlib unittest, fixtures only).

Covers the four load-bearing pieces the phase brief calls out:
  - span-join logic (llvm-cov line counts -> per-function executed?),
  - exec/ghost partition (spec/proof never flagged),
  - allowlist filtering (module- and function-keyed),
  - static reachability (function granularity when call edges exist; module
    granularity otherwise).

No live cargo/verus runs: every input is a committed fixture.

Run: python3 scripts/verus/test_verified_coverage.py
"""

from __future__ import annotations

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, "fixtures")
COV_CRATE = os.path.join(FIXTURES, "coverage_crate")
sys.path.insert(0, HERE)

import verified_coverage as vc  # noqa: E402


def read(path: str) -> str:
    with open(path, "r", encoding="utf-8") as fh:
        return fh.read()


def load(path: str):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


class ScanPartitionTest(unittest.TestCase):
    def setUp(self) -> None:
        # Scan just parser.rs so the load-bearing line-number asserts below are
        # unaffected by the other fixture files.
        self.fns = vc.scan_verified_fns(COV_CRATE, ["src/parser.rs"])
        self.by_name = {f.name: f for f in self.fns}

    def test_only_verus_block_functions_scanned(self) -> None:
        # outside_block is outside the verus! block -> not scanned.
        self.assertNotIn("outside_block", self.by_name)
        self.assertEqual(
            set(self.by_name), {"reached_exec", "dead_exec", "a_spec", "a_proof"}
        )

    def test_exec_ghost_partition(self) -> None:
        self.assertTrue(self.by_name["reached_exec"].is_exec)
        self.assertTrue(self.by_name["dead_exec"].is_exec)
        # spec/proof are ghost, never exec.
        self.assertFalse(self.by_name["a_spec"].is_exec)
        self.assertFalse(self.by_name["a_proof"].is_exec)
        self.assertEqual(self.by_name["a_spec"].mode, "spec")
        self.assertEqual(self.by_name["a_proof"].mode, "proof")

    def test_line_spans(self) -> None:
        # Spans are 1-based inclusive; brace-counted.
        self.assertEqual(
            (self.by_name["reached_exec"].line_start,
             self.by_name["reached_exec"].line_end), (18, 20)
        )
        self.assertEqual(
            (self.by_name["dead_exec"].line_start,
             self.by_name["dead_exec"].line_end), (22, 24)
        )

    def test_module_from_path(self) -> None:
        self.assertEqual(self.by_name["reached_exec"].module, "parser")

    def test_span_skips_spec_clause_braces(self) -> None:
        # Regression: a function whose `ensures ({ ... })` clause contains braces
        # must not have its span truncated to the signature. The body brace is on
        # its own line at base indent AFTER the clause; the span must reach it.
        fns = vc.scan_verified_fns(COV_CRATE, ["src/spec_clause.rs"])
        clause = {f.name: f for f in fns}["clause_body"]
        # Body `{` is line 17, closes line 20; span must include the executable
        # body, not stop at the ensures clause's closing brace on line 16.
        self.assertEqual((clause.line_start, clause.line_end), (11, 20))
        self.assertGreaterEqual(clause.line_end, 17)


class SpanJoinTest(unittest.TestCase):
    def setUp(self) -> None:
        cov_json = load(os.path.join(FIXTURES, "llvm_cov.json"))
        self.cov = vc.parse_llvm_cov(cov_json)
        self.fns = {f.name: f for f in vc.scan_verified_fns(COV_CRATE)}

    def test_llvm_cov_line_counts(self) -> None:
        # One file, executed and non-executed lines both present.
        self.assertEqual(len(self.cov), 1)
        (pairs,) = self.cov.values()
        d = dict(pairs)
        self.assertEqual(d[18], 5)
        self.assertEqual(d[22], 0)

    def test_executed_span_true(self) -> None:
        # reached_exec has an executed line in its span.
        self.assertIs(
            vc.span_executed(self.fns["reached_exec"], COV_CRATE, self.cov), True
        )

    def test_unexecuted_span_false(self) -> None:
        # dead_exec's whole span has zero counts.
        self.assertIs(
            vc.span_executed(self.fns["dead_exec"], COV_CRATE, self.cov), False
        )

    def test_no_file_data_returns_none(self) -> None:
        # A function in a file llvm-cov never saw -> None (not False).
        ghost_file_fn = vc.VerifiedFn(
            "x", "exec", "src/never_seen.rs", "never_seen", 1, 3
        )
        self.assertIsNone(vc.span_executed(ghost_file_fn, COV_CRATE, self.cov))


class VerusJoinTest(unittest.TestCase):
    def test_func_details_excludes_vstd(self) -> None:
        out = read(os.path.join(FIXTURES, "verus_coverage.json"))
        fd = vc.parse_func_details(out)
        # vstd axiom excluded; crate functions kept.
        self.assertNotIn("vstd::seq::axiom_seq_len", fd)
        self.assertIn("toydb::parser::reached_exec", fd)

    def test_suffix_join_matches_scan(self) -> None:
        out = read(os.path.join(FIXTURES, "verus_coverage.json"))
        fd = vc.parse_func_details(out)
        suffixes = vc.verified_qual_suffixes(fd)
        self.assertIn("parser::reached_exec", suffixes)
        fn = vc.VerifiedFn("reached_exec", "exec", "src/parser.rs", "parser", 1, 2)
        self.assertTrue(vc.fn_verified_by_verus(fn, suffixes, have_details=True))
        # A function Verus never reported is not treated as verified.
        missing = vc.VerifiedFn("nope", "exec", "src/parser.rs", "parser", 1, 2)
        self.assertFalse(
            vc.fn_verified_by_verus(missing, suffixes, have_details=True)
        )

    def test_no_details_trusts_static_scan(self) -> None:
        fn = vc.VerifiedFn("any", "exec", "src/parser.rs", "parser", 1, 2)
        self.assertTrue(
            vc.fn_verified_by_verus(fn, set(), have_details=False)
        )


class StaticReachabilityTest(unittest.TestCase):
    def test_function_granularity_with_call_edges(self) -> None:
        graph = load(os.path.join(FIXTURES, "graph_with_calls.json"))
        self.assertTrue(vc.graph_has_call_edges(graph))
        fns = [f for f in vc.scan_verified_fns(COV_CRATE) if f.is_exec]
        unreach_fns, unreach_mods, gran = vc.static_unreachable(graph, fns)
        self.assertEqual(gran, "function")
        self.assertEqual(unreach_mods, [])
        names = {f.name for f in unreach_fns}
        # dead_exec is not reachable from the parse entry point; reached_exec is.
        self.assertIn("dead_exec", names)
        self.assertNotIn("reached_exec", names)

    def test_module_granularity_without_call_edges(self) -> None:
        # Containment-only graph -> module granularity, flags said explicitly.
        graph = {
            "nodes": [
                {"id": "src/parser.rs", "level": "file", "parent": None,
                 "file": "src/parser.rs", "module": None, "function": None,
                 "kind": "file", "status": "unverified"},
                {"id": "src/parser.rs::parser", "level": "module",
                 "parent": "src/parser.rs", "file": "src/parser.rs",
                 "module": "parser", "function": None, "kind": "mod",
                 "status": "unverified"},
            ],
            "edges": [
                {"from": "src/parser.rs::parser", "to": "src/parser.rs",
                 "level": "module"},
            ],
        }
        self.assertFalse(vc.graph_has_call_edges(graph))
        fns = [f for f in vc.scan_verified_fns(COV_CRATE) if f.is_exec]
        unreach_fns, unreach_mods, gran = vc.static_unreachable(graph, fns)
        self.assertEqual(gran, "module")
        self.assertEqual(unreach_fns, [])
        # parser module is not an entry-point module -> unreachable.
        self.assertIn("parser", unreach_mods)

    def test_no_graph_unavailable(self) -> None:
        fns = [f for f in vc.scan_verified_fns(COV_CRATE) if f.is_exec]
        unreach_fns, unreach_mods, gran = vc.static_unreachable(None, fns)
        self.assertEqual(gran, "unavailable")
        self.assertEqual(unreach_fns, [])
        self.assertEqual(unreach_mods, [])


class AllowlistTest(unittest.TestCase):
    def test_parse_allowlist(self) -> None:
        import tempfile
        with tempfile.NamedTemporaryFile(
            "w", suffix=".txt", delete=False
        ) as fh:
            fh.write("# comment\n")
            fh.write("\n")
            fh.write("sql::parser::verified_stmt  cleared in phase 4\n")
            fh.write("parser::dead_exec some reason\n")
            path = fh.name
        try:
            allow = vc.load_allowlist(path)
        finally:
            os.unlink(path)
        self.assertEqual(
            allow, {"sql::parser::verified_stmt", "parser::dead_exec"}
        )

    def test_flag_allowed_by_module_or_key(self) -> None:
        allow = {"sql::parser::verified_stmt"}
        # module-level allow covers a function flag in that module.
        self.assertTrue(
            vc.flag_allowed(
                "sql::parser::verified_stmt::parse_stmt_exec",
                "sql::parser::verified_stmt", allow,
            )
        )
        # unrelated module not allowed.
        self.assertFalse(
            vc.flag_allowed("other::fn", "other", allow)
        )
        # exact key allow.
        self.assertTrue(vc.flag_allowed("k", "m", {"k"}))


class ReportTest(unittest.TestCase):
    def _report(self, allow):
        cov = vc.parse_llvm_cov(load(os.path.join(FIXTURES, "llvm_cov.json")))
        graph = load(os.path.join(FIXTURES, "graph_with_calls.json"))
        verus = read(os.path.join(FIXTURES, "verus_coverage.json"))
        return vc.build_report(COV_CRATE, verus, cov, graph, allow)

    def test_ghost_never_flagged(self) -> None:
        report = self._report(set())
        flagged_names = {
            fl["name"] for fl in report["flags"] if fl["name"] is not None
        }
        self.assertNotIn("a_spec", flagged_names)
        self.assertNotIn("a_proof", flagged_names)

    def test_dead_exec_flagged_both_lenses(self) -> None:
        report = self._report(set())
        kinds = {
            (fl["name"], fl["kind"]) for fl in report["flags"]
        }
        self.assertIn(("dead_exec", "unexecuted"), kinds)
        self.assertIn(("dead_exec", "unreachable"), kinds)
        # reached_exec clean.
        self.assertNotIn("reached_exec", {n for n, _ in kinds})

    def test_allowlist_suppresses_check(self) -> None:
        # With dead_exec on the allowlist, no unallowed flags remain.
        report = self._report({"parser::dead_exec"})
        self.assertEqual(report["unallowed_flags"], [])

    def test_json_block_shape(self) -> None:
        report = self._report(set())
        block = vc.build_json_block(report)
        self.assertIn("verified_coverage", block)
        vc_block = block["verified_coverage"]
        for key in (
            "exec_total", "ghost_total", "flags_total", "unallowed_total",
            "dynamic_available", "static_granularity", "flags", "modules",
        ):
            self.assertIn(key, vc_block)
        self.assertEqual(vc_block["exec_total"], 2)
        self.assertEqual(vc_block["ghost_total"], 2)


class CliCheckTest(unittest.TestCase):
    def test_check_exit_nonzero_without_allowlist(self) -> None:
        rc = vc.main([
            "--repo-root", COV_CRATE,
            "--verus-json", os.path.join(FIXTURES, "verus_coverage.json"),
            "--llvm-cov", os.path.join(FIXTURES, "llvm_cov.json"),
            "--graph", os.path.join(FIXTURES, "graph_with_calls.json"),
            "--allowlist", "/dev/null",
            "--check", "--output", os.devnull,
        ])
        self.assertEqual(rc, 1)

    def test_check_exit_zero_with_allowlist(self) -> None:
        import tempfile
        with tempfile.NamedTemporaryFile(
            "w", suffix=".txt", delete=False
        ) as fh:
            fh.write("parser::dead_exec cleared\n")
            path = fh.name
        try:
            rc = vc.main([
                "--repo-root", COV_CRATE,
                "--verus-json", os.path.join(FIXTURES, "verus_coverage.json"),
                "--llvm-cov", os.path.join(FIXTURES, "llvm_cov.json"),
                "--graph", os.path.join(FIXTURES, "graph_with_calls.json"),
                "--allowlist", path,
                "--check", "--output", os.devnull,
            ])
        finally:
            os.unlink(path)
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
