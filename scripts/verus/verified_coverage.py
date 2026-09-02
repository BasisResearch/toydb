#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
"""Flag verified-but-unexecuted / unreachable exec functions in toyDB.

Motivation
----------
A review found this repo's largest verified artefacts were dead code: production
called ``verified_control::parse_control_at`` (then a weak no-panic contract),
while the round-trip-proven parsers in ``verified_stmt.rs`` (``parse_stmt_exec``
/ ``parse_stmt_full_exec``), ``lex_all_exec`` in ``verified_lexer.rs``, and
``verified.rs`` were never called. (Phase 4, ``plans/phase-4-delete-twins.md``,
deleted those twins in 2026-09; this gate keeps new ones from accumulating.) A
verified function that nothing executes is a proof about dead code. This tool
makes that visible, with two independent lenses.

Two lenses
----------
* **Dynamic** (``--llvm-cov FILE``): build the verified-exec-function set (name,
  file, line span) from the Verus ``--output-json`` ``func-details`` plus a
  static scan of the ``verus!`` blocks that supplies mode (spec/proof/exec) and
  line spans (``func-details`` carries no spans). Ghost code (``spec``/``proof``)
  is erased from the normal build, can never execute, and is reported separately
  -- never flagged. Per-line execution counts come from
  ``cargo llvm-cov test --lib --json``; goldenscripts run under the lib test
  harness so they count. A verified *exec* function whose line span has zero
  executed lines is flagged. Rolled up per module.
* **Static** (``--graph FILE``): using the ``extract_graph.py`` call graph,
  compute reachability from the production entry points (``Session::execute`` in
  ``session.rs``, ``Parser::parse`` in ``parser.rs``). A verified exec function
  outside the reachable set gets a second flag -- this catches a twin with its
  own unit tests (coverage looks fine) that production can never reach. The
  static fallback graph only carries module-tree containment edges, not call
  edges, so function-level reachability is not possible from it: when the graph
  lacks call edges we say so and flag at MODULE level instead (a module none of
  whose functions are reachable from an entry-point module).

Both lenses degrade gracefully: with no llvm-cov / no graph the tool still lists
the verified exec/ghost partition so the report is never empty.

Output modes
------------
* default: a human-readable table (partition + per-module rollup + flags).
* ``--json``: a block shaped for dashboard ingest alongside the existing metrics
  (see CONTRACTS.md one level up).
* ``--check``: exits nonzero when (flagged set) minus (committed allowlist,
  ``verified_coverage_allow.txt``) is nonempty. Wired into the verus-gate CI job
  (``.github/workflows/verus-gate.yml``) with the precise dynamic lens:

      python3 scripts/verus/verified_coverage.py --check \\
          --verus-json <verify.sh --output-json capture> \\
          --llvm-cov <cargo llvm-cov test --lib --json capture>

  CI does NOT pass ``--graph``: the only graph available today is the
  extract_graph.py static fallback, which carries module-tree containment edges
  but no call edges, so its reachability is module-coarse and over-flags live
  modules (see the "module granularity" note the report prints). Pass ``--graph``
  locally for the advisory static lens once a real Verus call graph exists.

Stdlib only. Best-effort / never-raising, matching the sibling metrics scripts.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List, Optional, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ALLOWLIST = os.path.join(HERE, "verified_coverage_allow.txt")

SOURCE_EXTS = (".rs",)

# Verus internal prefixes to exclude from the crate-authored function set (same
# convention as extract_metrics._crate_function_counts).
_INTERNAL_PREFIXES = ("vstd::", "builtin::", "core::", "alloc::", "std::")

# Production entry points for the static reachability lens. Format is
# "file::symbol" for reporting; reachability is computed at whatever granularity
# the supplied graph supports.
ENTRY_POINTS = (
    ("src/sql/execution/session.rs", "Session::execute"),
    ("src/sql/parser/parser.rs", "Parser::parse"),
)


def log(msg: str) -> None:
    sys.stderr.write(f"[verified_coverage] {msg}\n")


# ---------------------------------------------------------------------------
# Static scan of verus! blocks: mode (spec/proof/exec) + line spans.
# ---------------------------------------------------------------------------

# A function signature inside a verus! block. Captures the optional mode
# keyword. A plain `fn` inside a verus! block is EXEC (the default mode).
_FN_SIG_RE = re.compile(
    r"^(?P<indent>\s*)"
    r"(?:pub(?:\([^)]*\))?\s+)?"
    r"(?:(?:open|closed)\s+)?"
    r"(?:(?P<mode>spec|proof|exec)\s+)?"
    r"fn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
)

_VERUS_OPEN_RE = re.compile(r"\bverus!\s*\{")
_VERUS_CLOSE = "} // verus!"


class VerifiedFn:
    """A function declared inside a verus! block.

    ``mode`` is one of "spec", "proof", "exec". ``line_start``/``line_end`` are
    1-based inclusive. ``module`` is the crate-relative ``::`` module path of the
    containing file. ``qual`` is ``module::name`` for joining against Verus
    func-details keys by suffix.
    """

    __slots__ = ("name", "mode", "file", "module", "line_start", "line_end")

    def __init__(self, name: str, mode: str, file: str, module: str,
                 line_start: int, line_end: int) -> None:
        self.name = name
        self.mode = mode
        self.file = file
        self.module = module
        self.line_start = line_start
        self.line_end = line_end

    @property
    def qual(self) -> str:
        return f"{self.module}::{self.name}"

    @property
    def is_exec(self) -> bool:
        return self.mode == "exec"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name, "mode": self.mode, "file": self.file,
            "module": self.module,
            "line_start": self.line_start, "line_end": self.line_end,
        }


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
    """``src/sql/parser/lexer.rs`` -> ``sql::parser::lexer`` (mirrors graph)."""
    parts = rel.split("/")
    if parts and parts[0] == "src":
        parts = parts[1:]
    if not parts:
        return "crate"
    fname = parts[-1]
    stem = fname[:-3] if fname.endswith(".rs") else fname
    dirs = parts[:-1]
    comps = dirs if stem in ("mod", "lib", "main") else dirs + [stem]
    return "::".join(comps) if comps else "crate"


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip())


def _find_body_open(lines: List[str], sig_idx: int) -> Optional[int]:
    """Index of the line where the function *body* ``{`` begins.

    Verus signatures are followed by spec clauses (``requires`` / ``ensures`` /
    ``decreases`` / ``invariant`` ...) whose expressions can themselves contain
    braces (``ensures ({ ... })``). Naively matching the first ``{`` therefore
    stops inside a spec clause and truncates the span to the signature. In this
    codebase the body brace is written on its own line at the function's base
    indentation (``\\n{`` after the clauses), or terminates the signature line
    itself when there are no clauses. Detect that specific body-open ``{``:
    the first line at index >= sig_idx whose stripped text starts with ``{`` and
    whose indent is <= the signature indent; failing that, a signature line that
    itself ends in ``{`` with no ``requires``/``ensures`` clause.
    """
    sig_indent = _indent(lines[sig_idx])
    # No-clause inline body: signature line ends with `{`.
    first = lines[sig_idx].rstrip()
    if first.endswith("{") and "requires" not in first and "ensures" not in first:
        return sig_idx
    n = len(lines)
    i = sig_idx
    while i < n:
        line = lines[i]
        stripped = line.strip()
        if i > sig_idx and stripped.startswith("{") and _indent(line) <= sig_indent:
            return i
        # No-body declaration (trait method): a `;` that terminates the decl at
        # the signature's own indentation (spec-clause bodies are indented
        # DEEPER, so their `;`s never match here). Only fires before any body
        # brace is seen.
        if (
            stripped.endswith(";")
            and not stripped.startswith("{")
            and _indent(line) <= sig_indent
            and i >= sig_idx
        ):
            return None
        i += 1
    return None


def _span_end(lines: List[str], sig_idx: int) -> int:
    """Return the 1-based inclusive end line of a function starting at sig_idx.

    Locate the body-opening ``{`` (skipping Verus spec clauses) and brace-count
    to its match. For a no-body trait-method declaration (``fn f(..);``) the span
    is just the signature line. Comments/strings are not stripped; this is a
    line-span approximation, robustly bounded, good enough for a coverage join.
    """
    body_idx = _find_body_open(lines, sig_idx)
    if body_idx is None:
        return sig_idx + 1  # declaration with no body
    depth = 0
    started = False
    i = body_idx
    n = len(lines)
    while i < n:
        for ch in lines[i]:
            if ch == "{":
                depth += 1
                started = True
            elif ch == "}":
                depth -= 1
                if started and depth == 0:
                    return i + 1  # 1-based inclusive
        i += 1
    return n


def scan_verified_fns(root: str, rel_paths: Optional[List[str]] = None
                      ) -> List[VerifiedFn]:
    """Scan every verus! block and return the functions inside it.

    Only functions physically inside a ``verus! { ... } // verus!`` block are
    verified; everything else is external-by-default and never verified.
    """
    if rel_paths is None:
        rel_paths = walk_sources(root)
    out: List[VerifiedFn] = []
    for rel in rel_paths:
        try:
            with open(os.path.join(root, rel), "r",
                      encoding="utf-8", errors="replace") as fh:
                lines = fh.readlines()
        except OSError as exc:
            log(f"could not read {rel}: {exc}")
            continue
        module = module_path_for_file(rel)
        in_block = False
        for idx, raw in enumerate(lines):
            if not in_block:
                if _VERUS_OPEN_RE.search(raw):
                    in_block = True
                continue
            if _VERUS_CLOSE in raw:
                in_block = False
                continue
            m = _FN_SIG_RE.match(raw)
            if not m:
                continue
            mode = m.group("mode") or "exec"
            name = m.group("name")
            end = _span_end(lines, idx)
            out.append(VerifiedFn(name, mode, rel, module, idx + 1, end))
    return out


# ---------------------------------------------------------------------------
# Verus func-details: the set of functions Verus actually verified.
# ---------------------------------------------------------------------------

def _iter_json_objects(text: str):
    dec = json.JSONDecoder()
    i, n = 0, len(text)
    while i < n:
        if text[i] == "{":
            try:
                obj, end = dec.raw_decode(text, i)
                yield obj
                i = max(end, i + 1)
                continue
            except json.JSONDecodeError:
                pass
        i += 1


def parse_func_details(verus_output: str) -> Dict[str, Any]:
    """Return the ``func-details`` dict from a Verus ``--output-json`` capture.

    Crate-internal names only (vstd/builtin/core/alloc/std excluded). Empty dict
    when absent -- callers treat that as "Verus detail unavailable" and fall back
    to trusting the static scan for the verified set.
    """
    for obj in _iter_json_objects(verus_output):
        if not isinstance(obj, dict):
            continue
        fd = obj.get("func-details")
        if isinstance(fd, dict) and fd:
            return {
                name: det for name, det in fd.items()
                if not name.startswith(_INTERNAL_PREFIXES)
            }
    return {}


def verified_qual_suffixes(func_details: Dict[str, Any]) -> Set[str]:
    """Set of ``module::name`` suffixes (last 2 path components) Verus verified.

    Verus keys are fully-qualified (``toydb::sql::parser::verified_stmt::foo``);
    we match the static scan's ``module::name`` (``sql::parser::verified_stmt``
    truncates to ``verified_stmt::foo``) on the trailing ``mod::fn`` pair, which
    is unique enough across this crate's parser modules.
    """
    out: Set[str] = set()
    for key in func_details:
        parts = key.split("::")
        if len(parts) >= 2:
            out.add("::".join(parts[-2:]))
    return out


def fn_verified_by_verus(fn: VerifiedFn, suffixes: Set[str],
                         have_details: bool) -> bool:
    """Was ``fn`` verified according to Verus func-details?

    When func-details is unavailable (empty), trust the static scan: every
    function in an opted-in verus! block is treated as verified. When it is
    present, require the ``mod::name`` suffix to appear.
    """
    if not have_details:
        return True
    tail = "::".join(fn.module.split("::")[-1:] + [fn.name])
    return tail in suffixes


# ---------------------------------------------------------------------------
# Dynamic lens: llvm-cov per-line execution join.
# ---------------------------------------------------------------------------

def parse_llvm_cov(cov_json: Any) -> Dict[str, List[Tuple[int, int]]]:
    """Parse ``cargo llvm-cov ... --json`` into per-file (line, count) pairs.

    The llvm-cov "export" JSON shape is::

        { "data": [ { "files": [ { "filename": "...",
              "segments": [ [line, col, count, hasCount, isRegionEntry, ...] ]
          } ] } ] }

    We collapse segments to a per-line executed-count: a line is "executed" if
    any covering segment with ``hasCount`` true has count > 0. Returns a map from
    absolute filename to a list of (line, count).
    """
    out: Dict[str, List[Tuple[int, int]]] = {}
    if not isinstance(cov_json, dict):
        return out
    for data in cov_json.get("data", []) or []:
        if not isinstance(data, dict):
            continue
        for f in data.get("files", []) or []:
            if not isinstance(f, dict):
                continue
            fname = f.get("filename")
            if not fname:
                continue
            line_counts: Dict[int, int] = {}
            for seg in f.get("segments", []) or []:
                # [line, col, count, hasCount, isRegionEntry, isGapRegion?]
                if not isinstance(seg, list) or len(seg) < 4:
                    continue
                line, _col, count, has_count = seg[0], seg[1], seg[2], seg[3]
                if not has_count:
                    continue
                try:
                    ln = int(line)
                    cnt = int(count)
                except (TypeError, ValueError):
                    continue
                prev = line_counts.get(ln, 0)
                line_counts[ln] = max(prev, cnt)
            out[os.path.abspath(fname)] = sorted(line_counts.items())
    return out


def span_executed(fn: VerifiedFn, root: str,
                  cov: Dict[str, List[Tuple[int, int]]]) -> Optional[bool]:
    """Did any line in ``fn``'s span execute at least once?

    Returns True/False, or None when coverage has no data for the file (so the
    caller can distinguish "not covered" from "instrumented but never ran").
    """
    abs_path = os.path.abspath(os.path.join(root, fn.file))
    pairs = cov.get(abs_path)
    if pairs is None:
        # Try a suffix match (llvm-cov emits absolute paths that may differ by
        # symlink/prefix from our root).
        for k, v in cov.items():
            if k.endswith("/" + fn.file) or k.endswith(os.sep + fn.file):
                pairs = v
                break
    if pairs is None:
        return None
    for ln, cnt in pairs:
        if fn.line_start <= ln <= fn.line_end and cnt > 0:
            return True
    return False


# ---------------------------------------------------------------------------
# Static lens: reachability over the extract_graph graph.
# ---------------------------------------------------------------------------

def graph_has_call_edges(graph: Dict[str, Any]) -> bool:
    """True iff the graph carries function->function edges beyond containment.

    The static fallback only emits containment edges (child->parent, level
    "function"/"module" pointing at the parent node). A real call graph has
    function-level edges between two DISTINCT function nodes. We detect the
    latter: any "function"-level edge whose endpoints are both function nodes and
    whose ``to`` is not the ``from``'s parent module.
    """
    nodes = {n["id"]: n for n in graph.get("nodes", [])}
    for e in graph.get("edges", []):
        if e.get("level") != "function":
            continue
        frm = nodes.get(e.get("from"))
        to = nodes.get(e.get("to"))
        if not frm or not to:
            continue
        if frm.get("level") == "function" and to.get("level") == "function":
            return True
    return False


def _entry_node_ids(graph: Dict[str, Any], level: str) -> Set[str]:
    """Resolve the production entry points to node ids at the given level."""
    ids: Set[str] = set()
    nodes = graph.get("nodes", [])
    for ep_file, ep_sym in ENTRY_POINTS:
        sym_fn = ep_sym.split("::")[-1]
        for n in nodes:
            if n.get("level") != level:
                continue
            if n.get("file") != ep_file:
                continue
            if level == "function" and n.get("function") == sym_fn:
                ids.add(n["id"])
            elif level == "module":
                ids.add(n["id"])
    return ids


def reachable_ids(graph: Dict[str, Any], seeds: Set[str], level: str
                  ) -> Set[str]:
    """BFS over edges of ``level`` from seeds, following from->to."""
    adj: Dict[str, List[str]] = {}
    for e in graph.get("edges", []):
        if e.get("level") != level:
            continue
        adj.setdefault(e["from"], []).append(e["to"])
    seen: Set[str] = set(seeds)
    stack = list(seeds)
    while stack:
        cur = stack.pop()
        for nxt in adj.get(cur, []):
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return seen


def static_unreachable(graph: Optional[Dict[str, Any]],
                       fns: List[VerifiedFn]) -> Tuple[List[VerifiedFn], List[str], str]:
    """Compute verified exec functions unreachable from production entry points.

    Returns (unreachable_exec_fns, unreachable_modules, granularity) where
    granularity is "function" or "module". When the graph carries call edges we
    flag at function granularity; otherwise at module granularity (and the
    ``unreachable_exec_fns`` list is empty, the modules list carries the flag).
    """
    exec_fns = [f for f in fns if f.is_exec]
    if graph is None:
        return [], [], "unavailable"

    if graph_has_call_edges(graph):
        seeds = _entry_node_ids(graph, "function")
        reach = reachable_ids(graph, seeds, "function")
        # Map each exec fn to its graph node id (file::module::name).
        unreachable: List[VerifiedFn] = []
        for f in exec_fns:
            node_id = f"{f.file}::{f.module}::{f.name}"
            if node_id not in reach:
                unreachable.append(f)
        return unreachable, [], "function"

    # Module granularity: a verified module is unreachable if its module node is
    # not reachable from the entry-point modules over containment edges.
    seeds = _entry_node_ids(graph, "module")
    reach = reachable_ids(graph, seeds, "module")
    verified_modules = sorted({f.module for f in exec_fns})
    node_by_module: Dict[str, str] = {}
    for n in graph.get("nodes", []):
        if n.get("level") == "module" and n.get("module"):
            node_by_module.setdefault(n["module"], n["id"])
    unreachable_mods: List[str] = []
    for mod in verified_modules:
        nid = node_by_module.get(mod)
        if nid is None or nid not in reach:
            unreachable_mods.append(mod)
    return [], unreachable_mods, "module"


# ---------------------------------------------------------------------------
# Allowlist.
# ---------------------------------------------------------------------------

def load_allowlist(path: str) -> Set[str]:
    """Load allowlist keys (one per line; ``#`` comments and blanks ignored).

    A key is either a module path (``sql::parser::verified_stmt``) or a
    ``module::function`` qualifier. The token before any whitespace is the key;
    the rest of the line is a free-form reason.
    """
    out: Set[str] = set()
    if not os.path.exists(path):
        return out
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                s = line.strip()
                if not s or s.startswith("#"):
                    continue
                key = s.split()[0]
                out.add(key)
    except OSError as exc:
        log(f"could not read allowlist {path}: {exc}")
    return out


def flag_allowed(flag_key: str, module: str, allow: Set[str]) -> bool:
    """A flag is allowed if its own key or its module is on the allowlist."""
    return flag_key in allow or module in allow


# ---------------------------------------------------------------------------
# Report assembly.
# ---------------------------------------------------------------------------

def build_report(
    root: str,
    verus_output: str,
    cov: Optional[Dict[str, List[Tuple[int, int]]]],
    graph: Optional[Dict[str, Any]],
    allow: Set[str],
) -> Dict[str, Any]:
    """Assemble the full coverage report (partition, flags, rollups)."""
    fns = scan_verified_fns(root)
    func_details = parse_func_details(verus_output) if verus_output else {}
    have_details = bool(func_details)
    suffixes = verified_qual_suffixes(func_details)

    verified = [
        f for f in fns if fn_verified_by_verus(f, suffixes, have_details)
    ]
    exec_fns = [f for f in verified if f.is_exec]
    ghost_fns = [f for f in verified if not f.is_exec]

    # Dynamic flags: exec fns whose span never executed.
    dynamic_flags: List[Dict[str, Any]] = []
    dynamic_available = cov is not None
    if dynamic_available:
        for f in exec_fns:
            executed = span_executed(f, root, cov)  # None => no file data
            if executed is False:
                dynamic_flags.append({
                    "kind": "unexecuted",
                    "name": f.name, "module": f.module, "file": f.file,
                    "line_start": f.line_start, "line_end": f.line_end,
                    "key": f.qual,
                })

    # Static flags: exec fns / modules unreachable from production.
    unreachable_fns, unreachable_mods, granularity = static_unreachable(
        graph, exec_fns
    )
    static_flags: List[Dict[str, Any]] = []
    for f in unreachable_fns:
        static_flags.append({
            "kind": "unreachable",
            "name": f.name, "module": f.module, "file": f.file,
            "line_start": f.line_start, "line_end": f.line_end,
            "key": f.qual,
        })
    for mod in unreachable_mods:
        static_flags.append({
            "kind": "unreachable_module",
            "name": None, "module": mod, "file": None,
            "key": mod,
        })

    all_flags = dynamic_flags + static_flags
    unallowed = [
        fl for fl in all_flags
        if not flag_allowed(fl["key"], fl["module"], allow)
    ]

    # Per-module rollup.
    modules: Dict[str, Dict[str, int]] = {}
    for f in exec_fns:
        m = modules.setdefault(
            f.module, {"exec": 0, "ghost": 0, "unexecuted": 0, "unreachable": 0}
        )
        m["exec"] += 1
    for f in ghost_fns:
        modules.setdefault(
            f.module, {"exec": 0, "ghost": 0, "unexecuted": 0, "unreachable": 0}
        )["ghost"] += 1
    for fl in dynamic_flags:
        modules.setdefault(
            fl["module"],
            {"exec": 0, "ghost": 0, "unexecuted": 0, "unreachable": 0},
        )["unexecuted"] += 1
    for fl in static_flags:
        modules.setdefault(
            fl["module"],
            {"exec": 0, "ghost": 0, "unexecuted": 0, "unreachable": 0},
        )["unreachable"] += 1

    return {
        "exec_functions": [f.to_dict() for f in exec_fns],
        "ghost_functions": [f.to_dict() for f in ghost_fns],
        "dynamic_available": dynamic_available,
        "static_granularity": granularity,
        "have_verus_details": have_details,
        "flags": all_flags,
        "unallowed_flags": unallowed,
        "modules": modules,
    }


# ---------------------------------------------------------------------------
# Rendering.
# ---------------------------------------------------------------------------

def render_table(report: Dict[str, Any]) -> str:
    lines: List[str] = []
    ex = report["exec_functions"]
    gh = report["ghost_functions"]
    lines.append("=== verified function partition ===")
    lines.append(
        f"exec (executable, MUST be exercised): {len(ex)}"
    )
    lines.append(
        f"ghost (spec/proof, erased -- never flagged): {len(gh)}"
    )
    lines.append("")

    lines.append("=== per-module rollup ===")
    lines.append(
        f"{'module':<44} {'exec':>5} {'ghost':>6} "
        f"{'unexec':>7} {'unreach':>8}"
    )
    for mod in sorted(report["modules"]):
        m = report["modules"][mod]
        lines.append(
            f"{mod:<44} {m['exec']:>5} {m['ghost']:>6} "
            f"{m['unexecuted']:>7} {m['unreachable']:>8}"
        )
    lines.append("")

    if not report["dynamic_available"]:
        lines.append(
            "(dynamic lens skipped: no --llvm-cov supplied)"
        )
    if report["static_granularity"] == "unavailable":
        lines.append("(static lens skipped: no --graph supplied)")
    elif report["static_granularity"] == "module":
        lines.append(
            "(static lens at MODULE granularity: graph lacks call edges)"
        )
    lines.append("")

    lines.append("=== FLAGS (verified but dead) ===")
    if not report["flags"]:
        lines.append("(none)")
    for fl in report["flags"]:
        loc = fl["module"] if fl["name"] is None else \
            f"{fl['module']}::{fl['name']}  ({fl['file']}:"\
            f"{fl.get('line_start')}-{fl.get('line_end')})"
        lines.append(f"[{fl['kind']:<18}] {loc}")
    lines.append("")

    unallowed = report["unallowed_flags"]
    lines.append(
        f"=== UNALLOWED flags (fail --check): {len(unallowed)} ==="
    )
    for fl in unallowed:
        loc = fl["module"] if fl["name"] is None else \
            f"{fl['module']}::{fl['name']}"
        lines.append(f"[{fl['kind']:<18}] {loc}")
    return "\n".join(lines)


def build_json_block(report: Dict[str, Any]) -> Dict[str, Any]:
    """Dashboard-ingest-shaped JSON alongside the existing metrics block."""
    return {
        "verified_coverage": {
            "exec_total": len(report["exec_functions"]),
            "ghost_total": len(report["ghost_functions"]),
            "flags_total": len(report["flags"]),
            "unallowed_total": len(report["unallowed_flags"]),
            "dynamic_available": report["dynamic_available"],
            "static_granularity": report["static_granularity"],
            "flags": report["flags"],
            "modules": report["modules"],
        }
    }


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------

def _read_file(path: Optional[str]) -> str:
    if not path:
        return ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            return fh.read()
    except OSError as exc:
        log(f"could not read {path}: {exc}")
        return ""


def _load_json(path: Optional[str]) -> Optional[Any]:
    if not path:
        return None
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        log(f"could not load JSON {path}: {exc}")
        return None


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".",
                        help="repo root to scan for verus! blocks")
    parser.add_argument("--verus-json", default=None,
                        help="captured `verify.sh --output-json` (func-details)")
    parser.add_argument("--llvm-cov", default=None,
                        help="`cargo llvm-cov test --lib --json` export file")
    parser.add_argument("--graph", default=None,
                        help="`extract_graph.py` graph JSON for static lens")
    parser.add_argument("--allowlist", default=DEFAULT_ALLOWLIST,
                        help="allowlist file (default: verified_coverage_allow.txt)")
    parser.add_argument("--json", action="store_true",
                        help="emit the dashboard JSON block instead of a table")
    parser.add_argument("--check", action="store_true",
                        help="exit nonzero when unallowed flags remain")
    parser.add_argument("--output", default=None, help="write output here")
    args = parser.parse_args(argv)

    root = os.path.abspath(args.repo_root)
    verus_output = _read_file(args.verus_json)
    cov_json = _load_json(args.llvm_cov)
    cov = parse_llvm_cov(cov_json) if cov_json is not None else None
    graph = _load_json(args.graph)
    allow = load_allowlist(args.allowlist)

    report = build_report(root, verus_output, cov, graph, allow)

    if args.json:
        out = json.dumps(build_json_block(report), indent=2, sort_keys=True)
    else:
        out = render_table(report)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as fh:
            fh.write(out + "\n")
        log(f"wrote report to {args.output}")
    else:
        sys.stdout.write(out + "\n")

    if args.check:
        n = len(report["unallowed_flags"])
        if n:
            log(f"--check: {n} unallowed flag(s) remain; failing.")
            return 1
        log("--check: no unallowed flags; passing.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
