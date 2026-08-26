#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research. MIT header over toyDB's Apache-2.0 base;
# see LICENSE-MIT / NOTICE.
"""Extract the three verification-progress metrics from Verus output.

Component 3 of the Verus telemetry project. This script turns Verus's stdout
(structured ``--output-json`` summary when present, otherwise the human summary
line) into the ``metrics`` block of the ``POST /verus/ingest/verification``
payload defined in CONTRACTS.md:

    { "functions_verified": N, "functions_with_errors": M,
      "files_clean": N, "files_total": M,
      "lines_verified": N, "lines_total": M }

Three metrics, computed as follows:

  (a) Verus outcome counts (functions_verified / functions_with_errors) come
      straight from Verus's own summary.
  (b) files_clean / files_total is a roll-up over per-file outcomes. When Verus
      reports per-file/per-function structure we use it; otherwise files_total
      is the count of source files walked and files_clean is derived from the
      absence of errors.
  (c) lines_verified / lines_total is a roll-up over source lines: lines_total
      is the physical line count of the walked sources, lines_verified is the
      line count of files that verified clean.

Robustness: Verus is not fully wired over toyDB yet. If Verus could not run,
or produced no parseable summary, we still emit a *valid* metrics payload
(best-effort / zeros) and log clearly to stderr. CI must never hard-fail the
telemetry POST because of this.

Stdlib only.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List, Optional, Tuple

# Files considered "source" for the file/line roll-ups.
SOURCE_EXTS = (".rs",)

# Human summary line, e.g. "verification results:: 12 verified, 3 errors"
# or "3 verified, 1 error". We accept singular/plural and optional prefix.
_HUMAN_SUMMARY_RE = re.compile(
    r"(?P<verified>\d+)\s+verified,\s+(?P<errors>\d+)\s+error",
    re.IGNORECASE,
)


def log(msg: str) -> None:
    sys.stderr.write(f"[extract_metrics] {msg}\n")


def walk_sources(root: str) -> List[str]:
    """Return sorted relative paths of source files under ``root``/src."""
    out: List[str] = []
    src_root = os.path.join(root, "src")
    scan_root = src_root if os.path.isdir(src_root) else root
    for dirpath, dirnames, filenames in os.walk(scan_root):
        # Skip build artefacts / VCS dirs.
        dirnames[:] = [
            d for d in dirnames if d not in ("target", ".git", "node_modules")
        ]
        for fn in filenames:
            if fn.endswith(SOURCE_EXTS):
                full = os.path.join(dirpath, fn)
                out.append(os.path.relpath(full, root))
    return sorted(out)


def count_lines(root: str, rel_paths: List[str]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for rel in rel_paths:
        full = os.path.join(root, rel)
        try:
            with open(full, "r", encoding="utf-8", errors="replace") as fh:
                counts[rel] = sum(1 for _ in fh)
        except OSError as exc:
            log(f"could not read {rel}: {exc}")
            counts[rel] = 0
    return counts


# `fn name` definitions, for the function-coverage denominator.
_FN_RE = re.compile(r"\bfn\s+[A-Za-z_][A-Za-z0-9_]*")


def count_functions(root: str, rel_paths: List[str]) -> int:
    """Total function definitions across the walked sources (coverage total)."""
    total = 0
    for rel in rel_paths:
        try:
            with open(os.path.join(root, rel), "r", encoding="utf-8", errors="replace") as fh:
                total += len(_FN_RE.findall(fh.read()))
        except OSError:
            continue
    return total


def scan_verus_blocks(root: str, rel_paths: List[str]) -> Tuple[int, int]:
    """Return (files_with_verus_blocks, total_lines_inside_verus_blocks).

    A ``verus! { ... } // verus!`` block is the only *verified* code in toyDB
    (everything outside is external-by-default). Counting those blocks — rather
    than whole files — is what keeps line/file coverage honest: keycode.rs is a
    ~800-line file with a ~40-line proof block, so only ~40 lines are verified.
    """
    files = 0
    lines = 0
    for rel in rel_paths:
        try:
            with open(os.path.join(root, rel), "r", encoding="utf-8", errors="replace") as fh:
                src = fh.read()
        except OSError:
            continue
        in_block = False
        block_lines = 0
        seen = False
        for ln in src.splitlines():
            if not in_block and "verus!" in ln and "{" in ln:
                in_block = True
                seen = True
            if in_block:
                block_lines += 1
            if in_block and "} // verus!" in ln:
                in_block = False
        if seen:
            files += 1
            lines += block_lines
    return files, lines


def _crate_function_counts(summary: Dict[str, Any]) -> Tuple[int, int]:
    """(verified, errors) for CRATE-authored functions.

    Prefers per-function detail so Verus's own vstd/builtin proof obligations
    are excluded from the numerator; falls back to the raw verified/errors
    counts when the release gives no per-function breakdown.
    """
    fd = summary.get("func_details")
    if isinstance(fd, dict) and fd:
        internal = ("vstd::", "builtin::", "core::", "alloc::", "std::")
        verified = errors = 0
        for name, det in fd.items():
            if name.startswith(internal):
                continue
            failed = det.get("failed_proof_notes") if isinstance(det, dict) else None
            if failed:
                errors += 1
            else:
                verified += 1
        if verified or errors:
            return verified, errors
    return int(summary.get("verified") or 0), int(summary.get("errors") or 0)


def parse_json_summary(text: str) -> Optional[Dict[str, Any]]:
    """Parse a Verus ``--output-json`` structured summary if present.

    Verus emits a JSON object on stdout. The shape has drifted across releases,
    so we look for any of the recognised carriers of the verified/errors counts
    and (optionally) per-file/per-function detail. Returns a dict with keys
    ``verified``, ``errors`` and optional ``files`` / ``functions`` lists, or
    None if nothing parseable was found.
    """
    # Verus prints the JSON as a single object; other lines may be human text.
    # Try whole-text parse first, then scan for JSON object lines.
    candidates: List[Any] = []
    stripped = text.strip()
    if stripped:
        try:
            candidates.append(json.loads(stripped))
        except json.JSONDecodeError:
            pass
    if not candidates:
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("{") and line.endswith("}"):
                try:
                    candidates.append(json.loads(line))
                except json.JSONDecodeError:
                    continue

    for obj in candidates:
        if not isinstance(obj, dict):
            continue
        vr = _find_verification_results(obj)
        if vr is not None:
            return vr
    return None


def _find_verification_results(obj: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Locate verified/errors counts inside a Verus JSON object.

    Recognises both the top-level ``{"verified": .., "errors": ..}`` shape and
    a nested ``{"verification-results": {..}}`` carrier.
    """
    # Nested carrier used by recent Verus releases.
    nested = obj.get("verification-results")
    if isinstance(nested, dict):
        base = nested
    else:
        base = obj

    verified = base.get("verified")
    errors = base.get("errors")
    if verified is None and errors is None:
        return None

    result: Dict[str, Any] = {
        "verified": int(verified or 0),
        "errors": int(errors or 0),
    }
    # Optional richer detail if the release provides it.
    if isinstance(base.get("files"), list):
        result["files"] = base["files"]
    if isinstance(base.get("functions"), list):
        result["functions"] = base["functions"]
    # Per-function detail (top-level sibling of verification-results). Lets us
    # count crate-authored proven functions, excluding Verus's own vstd/builtin
    # obligations, for an honest function-coverage numerator.
    fd = obj.get("func-details")
    if isinstance(fd, dict):
        result["func_details"] = fd
    return result


def parse_human_summary(text: str) -> Optional[Tuple[int, int]]:
    """Parse the human summary line ``N verified, M errors``.

    Returns the *last* match in the text (Verus prints one summary at the end).
    """
    matches = list(_HUMAN_SUMMARY_RE.finditer(text))
    if not matches:
        return None
    m = matches[-1]
    return int(m.group("verified")), int(m.group("errors"))


def build_metrics(
    root: str,
    verus_output: str,
    verus_ran: bool,
) -> Dict[str, int]:
    """Compute the coverage metrics block, best-effort and never raising.

    Coverage is measured against the WHOLE crate, so the dashboard can report
    what fraction of toyDB is verified:
      * functions_verified / functions_total  (function coverage)
      * lines_verified     / lines_total      (line coverage; verus! block lines)
      * files_clean        / files_total      (file coverage)
    """
    sources = walk_sources(root)
    line_counts = count_lines(root, sources)
    files_total = len(sources)
    lines_total = sum(line_counts.values())
    functions_total = count_functions(root, sources)
    verus_files, verus_lines = scan_verus_blocks(root, sources)

    functions_verified = 0
    functions_with_errors = 0
    files_clean = 0
    lines_verified = 0

    summary = parse_json_summary(verus_output) if verus_output else None
    if summary is not None:
        functions_verified, functions_with_errors = _crate_function_counts(summary)
        log(
            "parsed structured JSON summary: "
            f"{functions_verified} crate functions verified, "
            f"{functions_with_errors} errors"
        )
        files = summary.get("files")
        if isinstance(files, list) and files:
            # Release provided per-file outcomes: trust them directly.
            files_clean, lines_verified = _rollup_from_files(
                files, root, line_counts
            )
        else:
            files_clean, lines_verified = _verus_block_coverage(
                verus_files, verus_lines, functions_verified, functions_with_errors
            )
    else:
        human = parse_human_summary(verus_output) if verus_output else None
        if human is not None:
            functions_verified, functions_with_errors = human
            log(
                "parsed human summary line: "
                f"{functions_verified} verified, {functions_with_errors} errors"
            )
            files_clean, lines_verified = _verus_block_coverage(
                verus_files, verus_lines, functions_verified, functions_with_errors
            )
        elif verus_ran:
            log(
                "Verus ran but produced no parseable summary; "
                "emitting best-effort zeros for outcome counts."
            )
        else:
            log(
                "Verus did not run (not wired / unavailable); "
                "emitting zero outcome counts with file/line totals only."
            )

    return {
        "functions_verified": int(functions_verified),
        "functions_with_errors": int(functions_with_errors),
        "functions_total": int(functions_total),
        "files_clean": int(files_clean),
        "files_total": int(files_total),
        "lines_verified": int(lines_verified),
        "lines_total": int(lines_total),
    }


def _verus_block_coverage(
    verus_files: int,
    verus_lines: int,
    functions_verified: int,
    functions_with_errors: int,
) -> Tuple[int, int]:
    """Honest file/line coverage from the opted-in verus! blocks.

    Attributes coverage to the verified proof blocks, NEVER the whole repo. A
    file/line only counts once something actually verified with no errors."""
    if functions_verified > 0 and functions_with_errors == 0:
        return verus_files, verus_lines
    return 0, 0


def _rollup_from_files(
    files: List[Any],
    root: str,
    line_counts: Dict[str, int],
) -> Tuple[int, int]:
    """Roll up files_clean / lines_verified from per-file Verus detail.

    Each entry is expected to look like ``{"path"/"file": str, "errors": int}``
    or ``{"path": str, "success": bool}``. Unknown shapes count as not-clean.
    """
    files_clean = 0
    lines_verified = 0
    for entry in files:
        if not isinstance(entry, dict):
            continue
        path = entry.get("path") or entry.get("file") or ""
        errors = entry.get("errors")
        success = entry.get("success")
        clean = False
        if errors is not None:
            clean = int(errors) == 0
        elif success is not None:
            clean = bool(success)
        if clean:
            files_clean += 1
            rel = os.path.relpath(os.path.join(root, path), root)
            lines_verified += line_counts.get(rel, line_counts.get(path, 0))
    return files_clean, lines_verified


def _rollup_whole_repo(
    functions_verified: int,
    functions_with_errors: int,
    files_total: int,
    lines_total: int,
) -> Tuple[int, int]:
    """Whole-repo roll-up when Verus gives no per-file breakdown.

    Verus was run over the repo as a unit, so we cannot attribute outcomes to
    individual files. A file/line only counts as *clean* once something was
    actually proven: we require at least one verified function AND zero errors.
    Absent any proof outcome (the initial state, before specs exist) nothing is
    clean, so the metrics read 0 rather than a misleading 100%. Only when the
    whole repo verifies with real proven functions do we roll every file/line up
    as clean; any error drops it back to zero.
    """
    if functions_verified > 0 and functions_with_errors == 0:
        return files_total, lines_total
    return 0, 0


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root", default=".", help="repo root to walk for file/line totals"
    )
    parser.add_argument(
        "--verus-output",
        default=None,
        help="path to captured Verus stdout/JSON (default: read stdin)",
    )
    parser.add_argument(
        "--verus-ran",
        default=None,
        help="'true'/'false' whether verus executed (default: infer from output)",
    )
    parser.add_argument(
        "--output", default=None, help="write metrics JSON here (default: stdout)"
    )
    args = parser.parse_args(argv)

    if args.verus_output:
        try:
            with open(args.verus_output, "r", encoding="utf-8", errors="replace") as fh:
                verus_output = fh.read()
        except OSError as exc:
            log(f"could not read verus output {args.verus_output}: {exc}")
            verus_output = ""
    elif not sys.stdin.isatty():
        verus_output = sys.stdin.read()
    else:
        verus_output = ""

    if args.verus_ran is not None:
        verus_ran = args.verus_ran.strip().lower() in ("1", "true", "yes")
    else:
        verus_ran = bool(verus_output.strip())

    metrics = build_metrics(
        os.path.abspath(args.repo_root), verus_output, verus_ran
    )
    payload = json.dumps(metrics, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as fh:
            fh.write(payload + "\n")
        log(f"wrote metrics to {args.output}")
    else:
        sys.stdout.write(payload + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
