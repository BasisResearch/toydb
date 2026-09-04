# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# SMT query capture: collect the Verus --log-all diagnostic artifacts that
# scripts/verus/verify.sh (and, later, the MCP server's verify tool) writes
# per verification run, key them to the exact agent tool call, and upload
# them to the dashboard (POST /verus/ingest/smt).
#
# Division of labour (mirrors the rest of verus_trace):
#   * verify.sh PRODUCES a fresh log dir per run and announces it with a
#     `verus-smt-log-dir: <path>` line on stderr.
#   * The PostToolUse hook (../smt_capture.py) KEYS it: moves the dir to
#     ~/.verus-trace/smt/<session_id>/<tool_use_id>/, writes meta.json, and
#     spawns a detached background upload.
#   * This module implements collection and upload; the Stop hook calls
#     upload_pending() as a catch-up for anything the background upload
#     missed. Server-side the blobs are ground truth and re-ingest upserts,
#     so retrying a partial upload is always safe.
#
# Stdlib only, fail-soft: telemetry must never break a verification run.

import glob
import gzip
import hashlib
import json
import os
import re
import shutil
import sys
import time
import urllib.error
import urllib.request

from . import envelope as _env

MARKER = "verus-smt-log-dir:"

# Batch limit for one POST body. Files are gzipped then base64'd (~4/3
# overhead); 18 MB of gzip per batch keeps the body well under the 32 MB
# nginx cap on /verus/ingest/.
BATCH_GZ_BYTES = 18 * 1024 * 1024

# Housekeeping: producer dirs that nothing ever collected (non-Claude runs of
# verify.sh, crashes) are pruned from the pending root after this many days.
PENDING_TTL_DAYS = 7

# Map Verus log filenames to the dashboard's kind vocabulary. Ordered:
# first match wins (e.g. `-final.air` before `.air`).
_KIND_SUFFIXES = (
    (".smt_transcript", "smt_transcript"),
    (".smt2", "smt2"),
    ("-final.air", "air_final"),
    (".air", "air"),
    ("-poly.vir", "vir_poly"),
    ("-sst.vir", "vir_sst"),
    ("-simple.vir", "vir_simple"),
    (".vir", "vir"),
    (".triggers", "triggers"),
    (".dot", "call_graph"),
    (".interp", "interp"),
    (".impl_names", "impl_names"),
    ("-trait-conflicts.rs", "trait_conflicts"),
)

_META_NAME = "meta.json"
_UPLOADED_NAME = ".uploaded"
_SAFE_ID_RE = re.compile(r"[^A-Za-z0-9._:-]")


def _log(msg):
    sys.stderr.write("[verus-smt] %s\n" % msg)


def smt_url():
    """Derive the SMT ingest URL from VERUS_INGEST_URL (which points at the
    /session endpoint) so one env var configures every upload."""
    explicit = os.environ.get("VERUS_SMT_INGEST_URL")
    if explicit:
        return explicit
    base = os.environ.get("VERUS_INGEST_URL") or _env.DEFAULT_INGEST_URL
    if base.rstrip("/").endswith("/session"):
        return base.rstrip("/")[: -len("/session")] + "/smt"
    return base.rstrip("/") + "/smt"


def capture_root():
    root = os.environ.get("VERUS_SMT_CAPTURE_ROOT")
    if root:
        return os.path.expanduser(root)
    return os.path.expanduser("~/.verus-trace/smt")


def artifact_name(name):
    """Logical filename: producers zstd artifacts in place (x -> x.zst)."""
    return name[:-4] if name.endswith(".zst") else name


def _read_artifact(path):
    """Raw artifact bytes, transparently decompressing producer-side zstd."""
    with open(path, "rb") as fh:
        raw = fh.read()
    if path.endswith(".zst"):
        try:
            from compression.zstd import decompress  # stdlib, Python >= 3.14
        except ImportError:  # pragma: no cover
            from zstandard import decompress  # pip fallback
        raw = decompress(raw)
    return raw


def kind_of(filename):
    filename = artifact_name(filename)
    for suffix, kind in _KIND_SUFFIXES:
        if filename.endswith(suffix):
            return kind
    return "other"


def find_log_dir(text):
    """Extract the last `verus-smt-log-dir: <path>` marker from tool output."""
    if not text:
        return None
    found = None
    for line in text.splitlines():
        line = line.strip()
        if line.startswith(MARKER):
            found = line[len(MARKER):].strip()
    return found or None


def _safe_id(value):
    return _SAFE_ID_RE.sub("_", str(value))[:200] or "unknown"


def artifact_files(dest):
    """The artifact filenames in a capture dir (meta/markers excluded)."""
    names = []
    for name in sorted(os.listdir(dest)):
        if name in (_META_NAME, _UPLOADED_NAME):
            continue
        if os.path.isfile(os.path.join(dest, name)):
            names.append(name)
    return names


def collect(log_dir, session_id, tool_use_id, meta, root=None):
    """Move a producer log dir into the keyed capture layout and stamp meta.

    Returns the capture dir path, or None when there was nothing to keep (an
    empty producer dir — cargo considered the crate fresh, so Verus never
    ran — is deleted). Never raises."""
    try:
        root = root or capture_root()
        if not os.path.isdir(log_dir) or not os.listdir(log_dir):
            if os.path.isdir(log_dir):
                shutil.rmtree(log_dir, ignore_errors=True)
            return None
        dest = os.path.join(root, _safe_id(session_id), _safe_id(tool_use_id))
        os.makedirs(dest, exist_ok=True)
        for name in os.listdir(log_dir):
            target = os.path.join(dest, name)
            if os.path.exists(target):
                os.remove(target)
            shutil.move(os.path.join(log_dir, name), target)
        shutil.rmtree(log_dir, ignore_errors=True)
        # A re-run of the same tool call replaces the capture: drop any
        # previous uploaded marker so the new content gets shipped.
        marker = os.path.join(dest, _UPLOADED_NAME)
        if os.path.exists(marker):
            os.remove(marker)
        doc = dict(meta or {})
        doc.setdefault("session_id", session_id)
        doc.setdefault("tool_use_id", tool_use_id)
        with open(os.path.join(dest, _META_NAME), "w", encoding="utf-8") as fh:
            json.dump(doc, fh, indent=2, default=str)
        return dest
    except Exception as exc:  # pragma: no cover - defensive
        _log("collect failed for %s: %s" % (log_dir, exc))
        return None


def _post_batch(payload, url, token):
    body = json.dumps(payload, default=str).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "Authorization": "Bearer " + token,
        },
    )
    with urllib.request.urlopen(req, timeout=120) as resp:
        return json.loads(resp.read().decode("utf-8"))


def upload(dest, url=None, token=None):
    """Upload one capture dir (all artifact files + meta), batched to respect
    the ingest body cap. Files may span several POSTs: the server upserts by
    (session_id, tool_use_id, filename) and re-indexes when a .smt2 lands
    after its transcript. On full success writes the .uploaded marker.

    Returns True when every batch was accepted. Fail-soft otherwise: the dir
    stays pending and the Stop-hook catch-up (or a later run) retries."""
    import base64

    try:
        with open(os.path.join(dest, _META_NAME), "r", encoding="utf-8") as fh:
            meta = json.load(fh)
    except Exception as exc:
        _log("no readable meta.json in %s: %s" % (dest, exc))
        return False
    session_id = meta.get("session_id")
    tool_use_id = meta.get("tool_use_id")
    if not session_id or not tool_use_id:
        _log("meta.json in %s lacks session_id/tool_use_id" % dest)
        return False

    url = url or smt_url()
    token = token or os.environ.get("VERUS_INGEST_TOKEN")
    base = {
        "session_id": session_id,
        "tool_use_id": tool_use_id,
        "source": meta.get("source") or "agent",
        "branch": meta.get("branch"),
        "commit_sha": meta.get("commit_sha"),
        "invocation": meta.get("invocation"),
        "cwd": meta.get("cwd"),
        "verus_version": meta.get("verus_version"),
        "exit_code": meta.get("exit_code"),
        "duration_ms": meta.get("duration_ms"),
        "ts": meta.get("ts"),
        "success": meta.get("success"),
        "verified": meta.get("verified"),
        "errors": meta.get("errors"),
        "meta": meta,
    }

    names = artifact_files(dest)
    if not names:
        _log("nothing to upload in %s" % dest)
        return False

    # Ship transcripts and their .smt2 siblings first so the server can
    # attribute queries as soon as possible (order within a POST is free; this
    # only matters when files span batches).
    names.sort(key=lambda n: (kind_of(n) not in ("smt_transcript", "smt2"), n))

    batches = []
    cur, cur_bytes = [], 0
    for name in names:
        try:
            raw = _read_artifact(os.path.join(dest, name))
        except Exception as exc:
            _log("unreadable artifact %s: %s" % (name, exc))
            continue
        blob = gzip.compress(raw, 6)
        entry = {
            "filename": artifact_name(name),
            "kind": kind_of(name),
            "encoding": "gzip",
            "sha256": hashlib.sha256(raw).hexdigest(),
            "data_b64": base64.b64encode(blob).decode("ascii"),
        }
        if cur and cur_bytes + len(blob) > BATCH_GZ_BYTES:
            batches.append(cur)
            cur, cur_bytes = [], 0
        cur.append(entry)
        cur_bytes += len(blob)
    if cur:
        batches.append(cur)

    if _env.is_dry_run():
        sys.stdout.write(json.dumps({
            "smt_capture_dry_run": True,
            "dest": dest,
            "url": url,
            "batches": [
                [{k: v for k, v in e.items() if k != "data_b64"} for e in b]
                for b in batches
            ],
        }, indent=2))
        sys.stdout.write("\n")
        return True

    if not token:
        _log("no VERUS_INGEST_TOKEN set; capture stays pending (fail soft)")
        return False

    ok = True
    for i, batch in enumerate(batches):
        payload = dict(base)
        payload["files"] = batch
        try:
            res = _post_batch(payload, url, token)
            rejected = res.get("rejected") or []
            if rejected:
                ok = False
                _log("batch %d/%d: server rejected %d file(s): %s"
                     % (i + 1, len(batches), len(rejected), rejected[:3]))
            else:
                _log("batch %d/%d: stored %d file(s), %d queries indexed"
                     % (i + 1, len(batches), res.get("stored", 0),
                        res.get("indexed_queries", 0)))
        except urllib.error.HTTPError as exc:
            ok = False
            _log("batch %d/%d HTTP %s: %s" % (i + 1, len(batches), exc.code, exc.reason))
        except Exception as exc:
            ok = False
            _log("batch %d/%d failed: %s" % (i + 1, len(batches), exc))
    if ok:
        try:
            with open(os.path.join(dest, _UPLOADED_NAME), "w", encoding="utf-8") as fh:
                fh.write(_env.iso_now() + "\n")
        except OSError:
            pass
    return ok


def pending(session_id=None, root=None):
    """Capture dirs not yet fully uploaded, newest last."""
    root = root or capture_root()
    pat = os.path.join(root, _safe_id(session_id) if session_id else "*", "*")
    dirs = []
    for d in sorted(glob.glob(pat)):
        if not os.path.isdir(d):
            continue
        if os.path.basename(os.path.dirname(d)) == "pending":
            continue  # producer scratch, not a keyed capture
        if os.path.exists(os.path.join(d, _UPLOADED_NAME)):
            continue
        if not os.path.exists(os.path.join(d, _META_NAME)):
            continue
        dirs.append(d)
    return dirs


def upload_pending(session_id=None, root=None, url=None, token=None):
    """Catch-up: upload every pending capture (for one session when given).
    Returns (uploaded, failed) counts. Fail-soft."""
    uploaded = failed = 0
    for d in pending(session_id=session_id, root=root):
        if upload(d, url=url, token=token):
            uploaded += 1
        else:
            failed += 1
    return uploaded, failed


def prune_pending_scratch(root=None, ttl_days=PENDING_TTL_DAYS):
    """Delete producer dirs under <root>/pending older than the TTL — runs of
    verify.sh that nothing collected (non-Claude agents, crashes)."""
    root = root or capture_root()
    cutoff = time.time() - ttl_days * 86400
    for d in glob.glob(os.path.join(root, "pending", "*")):
        try:
            if os.path.isdir(d) and os.path.getmtime(d) < cutoff:
                shutil.rmtree(d, ignore_errors=True)
        except OSError:
            pass
