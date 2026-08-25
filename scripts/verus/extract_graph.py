#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
"""Extract the blueprint-graph snapshot from toyDB.

Component 3 / blueprint-graph part of Component 4. Emits, per CONTRACTS.md
``POST /verus/ingest/graph``:

    { "branch", "commit_sha", "ts",
      "nodes": [ { "id", "level", "parent", "file", "module", "function",
                   "kind", "status" } ],
      "edges": [ { "from", "to", "level" } ] }

All THREE levels (file, module, function) are extracted in one pass. Every node
carries its ``level`` and its ``parent`` at the next-coarser level:

    function.parent  -> module node
    module.parent    -> file node
    file.parent      -> null

Status:
  - Function-level status and dependency edges come from Verus's own dependency
    information when available (``--output-json`` with a dependency graph).
  - File and module levels are roll-ups: a coarse node is ``verified`` when all
    its children verify, ``frontier`` when it is unverified but every dependency
    is verified, else ``unverified``.

FALLBACK (documented): Verus dependency info is not wired over toyDB yet. When
no Verus graph is supplied, we fall back to a *static* Rust structure extraction
-- walk ``src/``, and regex-parse ``mod`` / ``fn`` / ``struct`` / ``impl`` /
``trait`` / ``enum`` items per file. Every node gets ``status = "unverified"``,
edges are the structural containment/dependency edges we can see statically
(module tree), and the schema is exercised end to end so the dashboard renders.
This fallback is intentionally conservative: it never claims verification that
Verus did not confirm.

Stdlib only.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Set

SOURCE_EXTS = (".rs",)

# Item-declaration regexes. Deliberately line-oriented and forgiving; this is a
# structural approximation, not a Rust parser.
_ITEM_RES = [
    ("fn", re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")),
    ("struct", re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?struct\s+([A-Za-z_][A-Za-z0-9_]*)")),
    ("enum", re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?enum\s+([A-Za-z_][A-Za-z0-9_]*)")),
    ("trait", re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?trait\s+([A-Za-z_][A-Za-z0-9_]*)")),
    ("impl", re.compile(r"^\s*impl(?:\s*<[^>]*>)?\s+(?:([A-Za-z_][A-Za-z0-9_:<>, ]*?)\s+for\s+)?([A-Za-z_][A-Za-z0-9_:<>, ]*)")),
]
# Inline module declarations `mod foo {` (not `mod foo;` file declarations).
_INLINE_MOD_RE = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{"
)


def log(msg: str) -> None:
    sys.stderr.write(f"[extract_graph] {msg}\n")


def iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def git_branch(root: str) -> str:
    env_branch = os.environ.get("VERUS_BRANCH")
    if env_branch:
        return env_branch
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=root, stderr=subprocess.DEVNULL,
        )
        return out.decode().strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def git_commit(root: str) -> str:
    env_sha = os.environ.get("VERUS_COMMIT_SHA")
    if env_sha:
        return env_sha
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, stderr=subprocess.DEVNULL
        )
        return out.decode().strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def walk_sources(root: str) -> List[str]:
    out: List[str] = []
    src_root = os.path.join(root, "src")
    scan_root = src_root if os.path.isdir(src_root) else root
    for dirpath, dirnames, filenames in os.walk(scan_root):
        dirnames[:] = [
            d for d in dirnames if d not in ("target", ".git", "node_modules")
        ]
        for fn in filenames:
            if fn.endswith(SOURCE_EXTS):
                full = os.path.join(dirpath, fn)
                out.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return sorted(out)


def module_path_for_file(rel: str) -> str:
    """Derive a Rust-ish module path from a file path.

    ``src/sql/parser/lexer.rs`` -> ``sql::parser::lexer``. ``mod.rs`` and
    ``lib.rs``/``main.rs`` collapse to their directory's module path.
    """
    parts = rel.split("/")
    if parts and parts[0] == "src":
        parts = parts[1:]
    if not parts:
        return "crate"
    fname = parts[-1]
    stem = fname[:-3] if fname.endswith(".rs") else fname
    dirs = parts[:-1]
    if stem in ("mod", "lib", "main"):
        comps = dirs
    else:
        comps = dirs + [stem]
    return "::".join(comps) if comps else "crate"


class GraphBuilder:
    def __init__(self) -> None:
        self.nodes: Dict[str, Dict[str, Any]] = {}
        self.edges: List[Dict[str, str]] = []
        self._edge_seen: Set[str] = set()

    def add_node(self, node: Dict[str, Any]) -> None:
        self.nodes.setdefault(node["id"], node)

    def add_edge(self, frm: str, to: str, level: str) -> None:
        if frm == to:
            return
        key = f"{frm}|{to}|{level}"
        if key in self._edge_seen:
            return
        self._edge_seen.add(key)
        self.edges.append({"from": frm, "to": to, "level": level})

    def as_payload(self) -> Dict[str, Any]:
        return {"nodes": list(self.nodes.values()), "edges": list(self.edges)}


def static_extract(root: str, default_status: str = "unverified") -> GraphBuilder:
    """Fallback: build the graph from static Rust structure under ``src/``."""
    gb = GraphBuilder()
    sources = walk_sources(root)

    for rel in sources:
        module = module_path_for_file(rel)
        file_id = rel
        gb.add_node({
            "id": file_id, "level": "file", "parent": None,
            "file": rel, "module": None, "function": None,
            "kind": "file", "status": default_status,
        })
        module_id = f"{rel}::{module}"
        gb.add_node({
            "id": module_id, "level": "module", "parent": file_id,
            "file": rel, "module": module, "function": None,
            "kind": "mod", "status": default_status,
        })
        gb.add_edge(module_id, file_id, "module")

        _parse_file_items(root, rel, module, module_id, gb, default_status)

    _link_module_tree(gb)
    return gb


def _parse_file_items(
    root: str,
    rel: str,
    module: str,
    module_id: str,
    gb: GraphBuilder,
    status: str,
) -> None:
    full = os.path.join(root, rel)
    try:
        with open(full, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except OSError as exc:
        log(f"could not read {rel}: {exc}")
        return

    impl_counter = 0
    for raw in lines:
        # Inline nested modules become their own module node under the file.
        m = _INLINE_MOD_RE.match(raw)
        if m:
            inner = m.group(1)
            inner_mod = f"{module}::{inner}" if module != "crate" else inner
            inner_id = f"{rel}::{inner_mod}"
            gb.add_node({
                "id": inner_id, "level": "module", "parent": rel,
                "file": rel, "module": inner_mod, "function": None,
                "kind": "mod", "status": status,
            })
            gb.add_edge(inner_id, module_id, "module")
            continue

        for kind, rx in _ITEM_RES:
            im = rx.match(raw)
            if not im:
                continue
            if kind == "impl":
                target = (im.group(2) or "").strip()
                target = re.split(r"[<\s]", target)[0] or "impl"
                impl_counter += 1
                name = f"impl_{target}_{impl_counter}"
            else:
                name = im.group(1)
            fn_id = f"{rel}::{module}::{name}"
            gb.add_node({
                "id": fn_id, "level": "function", "parent": module_id,
                "file": rel, "module": module, "function": name,
                "kind": kind, "status": status,
            })
            gb.add_edge(fn_id, module_id, "function")
            break


def _link_module_tree(gb: GraphBuilder) -> None:
    """Add module-level edges from child modules to parent modules by prefix."""
    module_nodes = [n for n in gb.nodes.values() if n["level"] == "module"]
    by_module: Dict[str, str] = {}
    for n in module_nodes:
        by_module.setdefault(n["module"], n["id"])
    for n in module_nodes:
        mod = n["module"]
        if mod and "::" in mod:
            parent_mod = mod.rsplit("::", 1)[0]
            parent_id = by_module.get(parent_mod)
            if parent_id:
                gb.add_edge(n["id"], parent_id, "module")


def graph_from_verus(verus_graph: Dict[str, Any], root: str) -> GraphBuilder:
    """Build the graph from Verus dependency info.

    Expected (best-effort) shape:
      { "functions": [ { "id"/"function", "file", "module", "kind",
                         "verified"/"status", "deps": [ids] } ] }
    Function status comes from Verus; file/module levels are rolled up.
    """
    gb = GraphBuilder()
    functions = verus_graph.get("functions")
    if not isinstance(functions, list):
        raise ValueError("verus graph has no 'functions' list")

    # File and module node registries so we can attach and roll up.
    file_children: Dict[str, List[str]] = {}
    module_children: Dict[str, List[str]] = {}
    fn_status: Dict[str, str] = {}

    for f in functions:
        if not isinstance(f, dict):
            continue
        rel = str(f.get("file", "")).replace(os.sep, "/")
        module = f.get("module") or module_path_for_file(rel)
        name = f.get("function") or f.get("id") or "?"
        kind = f.get("kind", "fn")
        raw_status = f.get("status")
        if raw_status is None:
            verified = f.get("verified")
            raw_status = "verified" if verified else "unverified"
        status = str(raw_status)

        file_id = rel
        module_id = f"{rel}::{module}"
        fn_id = f.get("id") or f"{rel}::{module}::{name}"

        gb.add_node({
            "id": file_id, "level": "file", "parent": None,
            "file": rel, "module": None, "function": None,
            "kind": "file", "status": "unverified",
        })
        gb.add_node({
            "id": module_id, "level": "module", "parent": file_id,
            "file": rel, "module": module, "function": None,
            "kind": "mod", "status": "unverified",
        })
        gb.add_node({
            "id": fn_id, "level": "function", "parent": module_id,
            "file": rel, "module": module, "function": name,
            "kind": kind, "status": status,
        })
        gb.add_edge(module_id, file_id, "module")
        gb.add_edge(fn_id, module_id, "function")
        file_children.setdefault(file_id, []).append(fn_id)
        module_children.setdefault(module_id, []).append(fn_id)
        fn_status[fn_id] = status

        for dep in f.get("deps", []) or []:
            gb.add_edge(fn_id, str(dep), "function")

    _rollup_status(gb, fn_status)
    return gb


def _rollup_status(gb: GraphBuilder, fn_status: Dict[str, str]) -> None:
    """Fold coarse-node status from children.

    verified: all children verified.
    frontier: unverified but every dependency (outgoing function edges) verified.
    else unverified.
    """
    # Build function dependency map from edges.
    deps: Dict[str, List[str]] = {}
    for e in gb.edges:
        if e["level"] == "function" and gb.nodes.get(e["to"], {}).get("level") == "function":
            deps.setdefault(e["from"], []).append(e["to"])

    # Frontier computation at function level.
    for node in gb.nodes.values():
        if node["level"] != "function":
            continue
        if node["status"] == "verified":
            continue
        node_deps = deps.get(node["id"], [])
        if node_deps and all(
            fn_status.get(d) == "verified" for d in node_deps
        ):
            node["status"] = "frontier"

    # Roll up module then file.
    def children_of(parent_id: str, level: str) -> List[Dict[str, Any]]:
        return [
            n for n in gb.nodes.values()
            if n["level"] == level and n["parent"] == parent_id
        ]

    for node in gb.nodes.values():
        if node["level"] == "module":
            node["status"] = _fold(children_of(node["id"], "function"))
    for node in gb.nodes.values():
        if node["level"] == "file":
            node["status"] = _fold(children_of(node["id"], "module"))


def _fold(children: List[Dict[str, Any]]) -> str:
    if not children:
        return "unverified"
    statuses = [c["status"] for c in children]
    if all(s == "verified" for s in statuses):
        return "verified"
    if any(s == "verified" for s in statuses) and all(
        s in ("verified", "frontier") for s in statuses
    ):
        return "frontier"
    return "unverified"


def build_payload(
    root: str,
    verus_graph_path: Optional[str],
) -> Dict[str, Any]:
    gb: Optional[GraphBuilder] = None
    if verus_graph_path:
        try:
            with open(verus_graph_path, "r", encoding="utf-8") as fh:
                verus_graph = json.load(fh)
            gb = graph_from_verus(verus_graph, root)
            log("built graph from Verus dependency info")
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            log(f"could not use Verus graph ({exc}); falling back to static extraction")
            gb = None
    if gb is None:
        log("using STATIC fallback extraction (all nodes status=unverified)")
        gb = static_extract(root)

    payload = gb.as_payload()
    payload["branch"] = git_branch(root)
    payload["commit_sha"] = git_commit(root)
    payload["ts"] = iso_now()
    return payload


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument(
        "--verus-graph",
        default=None,
        help="path to Verus dependency JSON; omitted/unreadable -> static fallback",
    )
    parser.add_argument("--output", default=None, help="write graph JSON here")
    args = parser.parse_args(argv)

    payload = build_payload(os.path.abspath(args.repo_root), args.verus_graph)
    text = json.dumps(payload, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
        log(
            f"wrote graph to {args.output}: "
            f"{len(payload['nodes'])} nodes, {len(payload['edges'])} edges"
        )
    else:
        sys.stdout.write(text + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
