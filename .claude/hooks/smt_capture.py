#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code `PostToolUse` hook (matcher: Bash | mcp__verus__verify): key the
# SMT diagnostic artifacts a Verus run just produced to this exact tool call.
#
# scripts/verus/verify.sh logs --log-all into a fresh dir and announces it via
# a `verus-smt-log-dir: <path>` stderr line; the MCP server's verify tool
# reports the same as an `smt_log_dir` field in its result. This hook finds
# either in `tool_response`, moves the dir to
# ~/.verus-trace/smt/<session_id>/<tool_use_id>/, stamps meta.json (git
# branch/commit, invocation, cwd), and spawns a DETACHED background upload so
# the agent loop is never blocked on the network. The Stop hook's
# upload_pending() catch-up retries anything the background upload missed.
#
# FAIL-SOFT: every path exits 0; telemetry must never disrupt the session.

import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verus_trace import envelope as _env  # noqa: E402
from verus_trace import smt_capture as _smt  # noqa: E402


def _strings(obj, out, depth=0):
    """All string values in a nested structure (tool_response shape varies by
    tool and is not a documented contract — search everything)."""
    if depth > 6:
        return
    if isinstance(obj, str):
        out.append(obj)
    elif isinstance(obj, dict):
        for v in obj.values():
            _strings(v, out, depth + 1)
    elif isinstance(obj, list):
        for v in obj:
            _strings(v, out, depth + 1)


def _find_key(obj, key, depth=0):
    """First value of `key` anywhere in a nested structure."""
    if depth > 6:
        return None
    if isinstance(obj, dict):
        if key in obj and obj[key]:
            return obj[key]
        for v in obj.values():
            found = _find_key(v, key, depth + 1)
            if found:
                return found
    elif isinstance(obj, list):
        for v in obj:
            found = _find_key(v, key, depth + 1)
            if found:
                return found
    return None


def _find_verdict_dict(obj, depth=0):
    """A dict carrying a Verus tool verdict: MCP verify's VerifyResult
    ({success, summary:{verified,errors}, ...}) or check's CheckResult
    ({success, verified, errors, ...}), anywhere in the response."""
    if depth > 6:
        return None
    if isinstance(obj, dict):
        if "success" in obj and ("summary" in obj or "verified" in obj):
            return obj
        for v in obj.values():
            found = _find_verdict_dict(v, depth + 1)
            if found is not None:
                return found
    elif isinstance(obj, list):
        for v in obj:
            found = _find_verdict_dict(v, depth + 1)
            if found is not None:
                return found
    return None


def _find_int_key(obj, keys, depth=0):
    """First int value under any of `keys` (0 counts, unlike _find_key)."""
    if depth > 6:
        return None
    if isinstance(obj, dict):
        for k in keys:
            v = obj.get(k)
            if isinstance(v, int) and not isinstance(v, bool):
                return v
        for v in obj.values():
            found = _find_int_key(v, keys, depth + 1)
            if found is not None:
                return found
    elif isinstance(obj, list):
        for v in obj:
            found = _find_int_key(v, keys, depth + 1)
            if found is not None:
                return found
    return None


def _verdict(docs, texts):
    """Best-effort success/verified/errors/exit_code from a tool response.

    MCP verify/check: the structured result dict. Bash: verify.sh
    --output-json prints a JSON doc with `verification-results` on stdout
    (a truncated response simply yields no verdict — fail-soft). Returns {}
    when nothing recognisable is present; absent keys mean "unknown", which
    the dashboard stores as NULL rather than failure."""
    out = {}
    d = None
    for doc in docs:
        d = _find_verdict_dict(doc)
        if d is not None:
            break
    if d is not None:
        out["success"] = bool(d.get("success"))
        summary = d.get("summary") if isinstance(d.get("summary"), dict) else d
        for key in ("verified", "errors"):
            v = summary.get(key)
            if isinstance(v, int) and not isinstance(v, bool):
                out[key] = v
    else:
        for doc in docs:
            vr = doc.get("verification-results") if isinstance(doc, dict) else None
            if isinstance(vr, dict):
                out["success"] = bool(vr.get("success"))
                for key in ("verified", "errors"):
                    v = vr.get(key)
                    if isinstance(v, int) and not isinstance(v, bool):
                        out[key] = v
                break
    ec = None
    for doc in docs:
        ec = _find_int_key(doc, ("exitCode", "exit_code", "returnCode"))
        if ec is not None:
            break
    if ec is not None:
        out["exit_code"] = ec
    return out


_SMT_DIR_JSON_RE = re.compile(r'"smt_log_dir"\s*:\s*"([^"]+)"')


def _parsed_docs(tool_response, texts):
    """The response plus every JSON document hiding in its strings.

    MCP tool results reach PostToolUse as JSON *text* (a content block whose
    payload is the serialized structured result), so key lookups must also
    search parsed string content, not just the response object itself."""
    docs = [tool_response]
    for t in texts:
        t = t.strip()
        if t.startswith("{") or t.startswith("["):
            try:
                docs.append(json.loads(t))
            except ValueError:
                pass
    return docs


def _invocation(tool_name, tool_input):
    if tool_name == "Bash" and isinstance(tool_input, dict):
        return str(tool_input.get("command") or "")[:2000]
    try:
        return (tool_name + " " + json.dumps(tool_input, default=str))[:2000]
    except Exception:
        return tool_name


def handle_post_tool_use(hook_input):
    if str(os.environ.get("VERUS_SMT_LOG_DISABLE", "")).strip() == "1":
        return
    tool_name = hook_input.get("tool_name") or ""
    tool_response = hook_input.get("tool_response")
    tool_input = hook_input.get("tool_input") or {}

    # Locate the producer's log dir: the MCP result's `smt_log_dir` field
    # (which reaches us serialized as JSON text, hence the parsed-docs pass
    # and the regex fallback for truncated JSON), or the verify.sh stderr
    # marker anywhere in the response.
    texts = []
    _strings(tool_response, texts)
    docs = _parsed_docs(tool_response, texts)
    log_dir = None
    for doc in docs:
        log_dir = _find_key(doc, "smt_log_dir")
        if log_dir:
            break
    if not log_dir:
        m = _SMT_DIR_JSON_RE.search("\n".join(texts))
        if m:
            log_dir = m.group(1)
    if not log_dir:
        log_dir = _smt.find_log_dir("\n".join(texts))
    if not log_dir:
        return
    log_dir = os.path.expanduser(str(log_dir))
    if not os.path.isdir(log_dir):
        return

    session_id = hook_input.get("session_id") or "unknown-session"
    tool_use_id = hook_input.get("tool_use_id") or ("unmatched-" + _env.iso_now())
    cwd = hook_input.get("cwd") or os.getcwd()
    root = _env.repo_root(cwd)
    meta = {
        "session_id": session_id,
        "tool_use_id": tool_use_id,
        "source": "agent",
        "invocation": _invocation(tool_name, tool_input),
        "tool_name": tool_name,
        "cwd": cwd,
        "branch": _env.branch(root),
        "commit_sha": _env.commit_sha(root),
        "ts": _env.iso_now(),
    }
    # The tool's own verdict (success/verified/errors/exit_code): what makes
    # a pre-SMT failure (type error, VIR error: zero queries, few artifacts)
    # distinguishable from "nothing to verify" on the dashboard.
    meta.update(_verdict(docs, texts))
    dest = _smt.collect(log_dir, session_id, tool_use_id, meta)
    if dest is None:
        # Empty producer dir: cargo considered the crate fresh, Verus never
        # ran. Nothing to capture.
        return
    sys.stderr.write("[verus-smt] captured %s\n" % dest)

    # Detached background upload: keeps the agent loop free. Output goes to a
    # log next to the captures for debugging.
    try:
        log_path = os.path.join(_smt.capture_root(), "upload.log")
        with open(log_path, "ab") as log_fh:
            subprocess.Popen(
                [sys.executable, os.path.abspath(__file__), "--upload", dest],
                stdout=log_fh,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
    except Exception as exc:
        sys.stderr.write(
            "[verus-smt] background upload spawn failed (Stop hook will "
            "catch up): %s\n" % exc
        )

    _smt.prune_pending_scratch()


def main(argv):
    if len(argv) >= 3 and argv[1] == "--upload":
        # Background mode (also usable manually): upload one capture dir.
        ok = _smt.upload(argv[2])
        sys.stderr.write("[verus-smt] upload %s: %s\n"
                         % (argv[2], "ok" if ok else "FAILED (stays pending)"))
        return 0

    try:
        raw = sys.stdin.read()
        hook_input = json.loads(raw) if raw.strip() else {}
    except Exception as exc:
        sys.stderr.write("[verus-smt] bad hook input: %s\n" % exc)
        return 0
    try:
        handle_post_tool_use(hook_input)
    except Exception as exc:
        sys.stderr.write("[verus-smt] capture failed (fail-soft): %s\n" % exc)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
