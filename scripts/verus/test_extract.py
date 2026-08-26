#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
"""Tests for extract_metrics and extract_graph (stdlib unittest).

Asserts both scripts produce CONTRACTS.md-conformant payloads:
  - metrics: exactly the six required keys, correct roll-ups from fixtures.
  - graph: all three node levels present, parent links coherent, edges only
    reference existing nodes.

Also exercises the ingest POST path with VERUS_INGEST_DRY_RUN so it runs with
no live endpoint.

Run: python3 scripts/verus/test_extract.py
"""

from __future__ import annotations

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, "fixtures")
sys.path.insert(0, HERE)

import extract_graph  # noqa: E402
import extract_metrics  # noqa: E402

METRIC_KEYS = {
    "functions_verified", "functions_with_errors", "functions_total",
    "files_clean", "files_total",
    "lines_verified", "lines_total",
}
NODE_KEYS = {"id", "level", "parent", "file", "module", "function", "kind", "status"}
EDGE_KEYS = {"from", "to", "level"}
LEVELS = {"file", "module", "function"}
STATUSES = {"verified", "unverified", "frontier"}


def read(path: str) -> str:
    with open(path, "r", encoding="utf-8") as fh:
        return fh.read()


class MetricsTest(unittest.TestCase):
    def _assert_shape(self, metrics: dict) -> None:
        self.assertEqual(set(metrics.keys()), METRIC_KEYS)
        for k, v in metrics.items():
            self.assertIsInstance(v, int, f"{k} must be int")
            self.assertGreaterEqual(v, 0)

    def test_json_summary(self) -> None:
        out = read(os.path.join(FIXTURES, "verus_summary.json"))
        m = extract_metrics.build_metrics(
            os.path.join(FIXTURES, "sample_crate"), out, verus_ran=True
        )
        self._assert_shape(m)
        self.assertEqual(m["functions_verified"], 12)
        self.assertEqual(m["functions_with_errors"], 3)
        # per-file detail: 2 of 3 files clean.
        self.assertEqual(m["files_clean"], 2)

    def test_parses_pretty_json_after_banner(self) -> None:
        # Regression: verify.sh printed a banner to stdout ahead of the
        # pretty-printed --output-json object; the old line-based parser saw no
        # single-line {...} and reported 0 despite Verus verifying cleanly.
        payload = {
            "verification-results": {"verified": 3, "errors": 0},
            "func-details": {
                "toydb::encoding::keycode::i64_key": {"failed_proof_notes": []},
                "toydb::encoding::keycode::encode_i64_key": {"failed_proof_notes": []},
                "toydb::encoding::keycode::decode_i64_key": {"failed_proof_notes": []},
                "vstd::function::axiom": {"failed_proof_notes": []},
            },
        }
        out = (
            "verus: verifying 1 module(s): encoding::keycode\n"
            + json.dumps(payload, indent=2)
            + "\n"
        )
        m = extract_metrics.build_metrics(
            os.path.join(FIXTURES, "sample_crate"), out, verus_ran=True
        )
        self.assertEqual(m["functions_verified"], 3)  # crate-local, vstd excluded
        self.assertEqual(m["functions_with_errors"], 0)

    def test_human_summary(self) -> None:
        out = read(os.path.join(FIXTURES, "verus_human.txt"))
        m = extract_metrics.build_metrics(
            os.path.join(FIXTURES, "sample_crate"), out, verus_ran=True
        )
        self._assert_shape(m)
        self.assertEqual(m["functions_verified"], 12)
        self.assertEqual(m["functions_with_errors"], 3)
        # whole-repo rollup with errors present -> 0 clean.
        self.assertEqual(m["files_clean"], 0)

    def test_verus_absent_best_effort(self) -> None:
        m = extract_metrics.build_metrics(
            os.path.join(FIXTURES, "sample_crate"), "", verus_ran=False
        )
        self._assert_shape(m)
        self.assertEqual(m["functions_verified"], 0)
        self.assertEqual(m["functions_with_errors"], 0)
        # File/line totals still computed over the walked crate.
        self.assertGreater(m["files_total"], 0)
        self.assertGreater(m["lines_total"], 0)

    def test_totals_reflect_sources(self) -> None:
        crate = os.path.join(FIXTURES, "sample_crate")
        m = extract_metrics.build_metrics(crate, "", verus_ran=False)
        self.assertEqual(m["files_total"], 2)  # lib.rs, math.rs

    def test_functions_total_counted(self) -> None:
        # The coverage denominator counts fn definitions across the crate.
        crate = os.path.join(FIXTURES, "sample_crate")
        m = extract_metrics.build_metrics(crate, "", verus_ran=False)
        self.assertGreater(m["functions_total"], 0)

    def test_crate_local_function_counts_exclude_vstd(self) -> None:
        # func-details with a vstd axiom must not inflate the numerator.
        out = json.dumps(
            {
                "verification-results": {"verified": 3, "errors": 0},
                "func-details": {
                    "toydb::m::a": {"failed_proof_notes": []},
                    "toydb::m::b": {"failed_proof_notes": []},
                    "vstd::function::axiom": {"failed_proof_notes": []},
                },
            }
        )
        m = extract_metrics.build_metrics(
            os.path.join(FIXTURES, "sample_crate"), out, verus_ran=True
        )
        self.assertEqual(m["functions_verified"], 2)  # vstd axiom excluded
        self.assertEqual(m["functions_with_errors"], 0)

    def test_line_coverage_from_verus_blocks(self) -> None:
        # A verus! block's lines count as verified; surrounding code does not.
        import tempfile

        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, "src")
            os.makedirs(src)
            with open(os.path.join(src, "lib.rs"), "w", encoding="utf-8") as fh:
                fh.write(
                    "fn plain() {}\n"
                    "verus! {\n"
                    "proof fn p() {}\n"
                    "} // verus!\n"
                    "fn other() {}\n"
                )
            out = json.dumps(
                {
                    "verification-results": {"verified": 1, "errors": 0},
                    "func-details": {"crate::p": {"failed_proof_notes": []}},
                }
            )
            m = extract_metrics.build_metrics(d, out, verus_ran=True)
            self.assertEqual(m["lines_verified"], 3)  # the 3 verus! block lines
            self.assertEqual(m["files_clean"], 1)
            self.assertGreater(m["lines_total"], m["lines_verified"])


class GraphStructureMixin:
    def assert_graph_conformant(self, payload: dict) -> None:
        self.assertIn("nodes", payload)
        self.assertIn("edges", payload)
        self.assertIn("branch", payload)
        self.assertIn("commit_sha", payload)
        self.assertIn("ts", payload)

        ids = set()
        levels_seen = set()
        for n in payload["nodes"]:
            self.assertEqual(set(n.keys()), NODE_KEYS, f"bad node keys: {n}")
            self.assertIn(n["level"], LEVELS)
            self.assertIn(n["status"], STATUSES)
            self.assertNotIn(n["id"], ids, f"duplicate node id {n['id']}")
            ids.add(n["id"])
            levels_seen.add(n["level"])

        # All three levels present.
        self.assertEqual(levels_seen, LEVELS, "all three node levels required")

        # Parent links coherent: parent (when set) references an existing node
        # exactly one level coarser.
        coarser = {"function": "module", "module": "file", "file": None}
        by_id = {n["id"]: n for n in payload["nodes"]}
        for n in payload["nodes"]:
            if n["parent"] is None:
                self.assertEqual(
                    n["level"], "file",
                    f"only file nodes may have null parent: {n['id']}",
                )
                continue
            self.assertIn(n["parent"], by_id, f"dangling parent {n['parent']}")
            self.assertEqual(
                by_id[n["parent"]]["level"], coarser[n["level"]],
                f"parent of {n['id']} at wrong level",
            )

        # Edges reference existing nodes.
        for e in payload["edges"]:
            self.assertEqual(set(e.keys()), EDGE_KEYS)
            self.assertIn(e["from"], ids, f"edge from missing node {e['from']}")
            self.assertIn(e["to"], ids, f"edge to missing node {e['to']}")


class GraphStaticTest(unittest.TestCase, GraphStructureMixin):
    def test_static_fallback(self) -> None:
        crate = os.path.join(FIXTURES, "sample_crate")
        payload = extract_graph.build_payload(crate, verus_graph_path=None)
        self.assert_graph_conformant(payload)
        # Static fallback: everything unverified.
        for n in payload["nodes"]:
            self.assertEqual(n["status"], "unverified")
        # Known items present.
        fns = {n["function"] for n in payload["nodes"] if n["level"] == "function"}
        self.assertIn("add", fns)
        self.assertIn("run", fns)


class GraphVerusTest(unittest.TestCase, GraphStructureMixin):
    def test_from_verus_deps(self) -> None:
        crate = os.path.join(FIXTURES, "sample_crate")
        payload = extract_graph.build_payload(
            crate, verus_graph_path=os.path.join(FIXTURES, "verus_graph.json")
        )
        self.assert_graph_conformant(payload)
        by_id = {n["id"]: n for n in payload["nodes"]}
        # add/mul verified from Verus.
        self.assertEqual(by_id["src/math.rs::math::add"]["status"], "verified")
        # run depends only on add (verified) but is itself unverified -> frontier.
        self.assertEqual(by_id["src/lib.rs::crate::run"]["status"], "frontier")
        # math module all-verified -> verified rollup.
        self.assertEqual(by_id["src/math.rs::math"]["status"], "verified")
        self.assertEqual(by_id["src/math.rs"]["status"], "verified")


class IngestDryRunTest(unittest.TestCase):
    def test_dry_run_post_helper(self) -> None:
        """post_ingest with VERUS_INGEST_DRY_RUN must not hit the network."""
        os.environ["VERUS_INGEST_DRY_RUN"] = "1"
        try:
            ok = post_ingest(
                "https://example.invalid/verus/ingest/verification",
                {"metrics": {}}, token="dummy",
            )
        finally:
            del os.environ["VERUS_INGEST_DRY_RUN"]
        self.assertTrue(ok)


def post_ingest(url: str, payload: dict, token: str) -> bool:
    """Minimal ingest POST helper honouring VERUS_INGEST_DRY_RUN.

    Kept here (stdlib urllib) so the test can exercise the POST path without a
    live endpoint; the workflow uses the same env flag semantics via curl.
    """
    body = json.dumps(payload).encode("utf-8")
    if os.environ.get("VERUS_INGEST_DRY_RUN"):
        sys.stderr.write(
            f"[dry-run] would POST {len(body)} bytes to {url}\n"
        )
        return True
    import urllib.request  # local import: only needed for live POST
    req = urllib.request.Request(
        url, data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=30) as resp:  # pragma: no cover
        return 200 <= resp.status < 300


if __name__ == "__main__":
    unittest.main(verbosity=2)
