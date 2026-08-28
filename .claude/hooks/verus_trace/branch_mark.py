# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Branch outcome marks: flag a branch as a FAILED ATTEMPT (or clear such a
# mark) on the Verus dashboard, with a short, not-necessarily-precise reason
# and an optional category tag. The goal is to keep the information around so
# failures can be filtered and analysed later (what went wrong, what tooling
# change would have prevented it) -- not to write a post-mortem.
#
# Agent-agnostic and stdlib only, like the rest of verus_trace. The CLI entry
# point is ../mark_branch.py; Claude (/mark-failed skill), opencode
# (/mark-failed command), Codex (AGENTS.md instructions) and humans all end up
# calling that script.
#
# Unlike session capture this is an EXPLICIT user action, so it is NOT
# fail-soft: post_mark() reports failure with a non-zero exit from the CLI.
# Every mark is also appended to a local JSONL log (~/.verus-trace/
# branch_marks.jsonl) so nothing is lost if the upload fails.

import json
import os
import sys
import urllib.error
import urllib.request

from . import envelope as _env

DEFAULT_MARK_URL = "https://verus.kirancodes.me/verus/ingest/branch_mark"
STATUSES = ("failed", "cleared")
AGENTS = ("claude", "codex", "opencode", "human")

# Suggested category vocabulary. Free-form on the server (normalised to a
# lowercase kebab tag); these are just the tags we want to converge on so the
# analysis pass can group like with like.
SUGGESTED_CATEGORIES = (
    "verus-timeout",      # Z3/Verus timed out or blew up (rlimit)
    "spec-too-strong",    # could not prove the spec as written; spec needs weakening
    "spec-wrong",         # the spec did not capture the intended property
    "missing-lemma",      # needed a lemma / trigger / invariant we could not find
    "verus-unsupported",  # Rust feature Verus does not support (traits, closures, ...)
    "tooling-bug",        # MCP server / verify script / CI misbehaved
    "scope-too-big",      # attempted too much at once; should be split
    "agent-stuck",        # agent looped or gave up without a clear technical cause
    "abandoned",          # dropped for non-technical reasons (priority, superseded)
    "other",
)


def mark_url():
    """Derive the branch_mark ingest URL from VERUS_INGEST_URL (which points at
    the /session endpoint) so one env var configures every upload."""
    explicit = os.environ.get("VERUS_MARK_URL")
    if explicit:
        return explicit
    base = os.environ.get("VERUS_INGEST_URL")
    if base:
        if base.rstrip("/").endswith("/session"):
            return base.rstrip("/")[: -len("/session")] + "/branch_mark"
        return base.rstrip("/") + "/branch_mark"
    return DEFAULT_MARK_URL


def detect_agent(environ=None):
    """Best-effort: which agent is running this? Claude Code exports
    CLAUDECODE=1; Codex exports CODEX_* variables in its sandbox; opencode
    exports OPENCODE*. Falls back to `human`. Callers may override with
    --agent / VERUS_MARK_AGENT."""
    environ = os.environ if environ is None else environ
    forced = (environ.get("VERUS_MARK_AGENT") or "").strip().lower()
    if forced in AGENTS:
        return forced
    if environ.get("CLAUDECODE") or environ.get("CLAUDE_CODE_ENTRYPOINT"):
        return "claude"
    if any(k.startswith("OPENCODE") for k in environ):
        return "opencode"
    if any(k.startswith("CODEX_") for k in environ):
        return "codex"
    return "human"


def normalize_category(cat):
    if not cat:
        return None
    cat = "-".join(str(cat).strip().lower().split())
    return cat.strip("-") or None


def build_mark(reason, status="failed", category=None, branch=None, cwd=None,
               agent=None, session_id=None, commit=None):
    """Build the POST /verus/ingest/branch_mark payload. Git fields are
    gathered from `cwd` (default: current dir) the same way the session
    envelope does, so the mark joins the session telemetry on branch name."""
    if status not in STATUSES:
        raise ValueError("status must be one of %s" % ", ".join(STATUSES))
    reason = (reason or "").strip()
    if status == "failed" and not reason:
        raise ValueError("a reason is required to mark a branch as failed")
    cwd = os.path.abspath(cwd or os.getcwd())
    root = _env.repo_root(cwd)
    branch = (branch or _env.branch(root)).strip()
    if not branch or branch == "HEAD":
        raise ValueError(
            "could not determine the branch (detached HEAD?); pass --branch"
        )
    if branch in ("main", "master"):
        raise ValueError(
            "refusing to mark %s: marks are for feature branches (pass --branch)"
            % branch
        )
    return {
        "branch": branch,
        "status": status,
        "category": normalize_category(category),
        "reason": reason,
        "author_email": _env.author_email(root),
        "agent": agent or detect_agent(),
        "machine": _env.machine(),
        "repo": _env.REPO_SLUG,
        "commit_sha": commit or _env.commit_sha(root),
        "session_id": session_id or None,
        "marked_at": _env.iso_now(),
    }


def local_log_path():
    override = os.environ.get("VERUS_MARK_LOG")
    if override:
        return os.path.expanduser(override)
    return os.path.expanduser("~/.verus-trace/branch_marks.jsonl")


def append_local_log(mark, uploaded):
    """Append the mark to the local JSONL log (fail-soft; the log is a
    convenience backstop, never a reason to fail the mark)."""
    try:
        path = local_log_path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        rec = dict(mark)
        rec["uploaded"] = bool(uploaded)
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(rec, default=str) + "\n")
        return path
    except Exception as exc:  # pragma: no cover - defensive
        _env._log("could not write local mark log: %s" % exc)
        return None


def post_mark(mark, url=None, token=None):
    """POST the mark. Returns (ok, message). Dry-run prints the payload and
    returns ok. Missing token / HTTP error / network error -> (False, why)."""
    url = url or mark_url()
    token = token or os.environ.get("VERUS_INGEST_TOKEN")
    if _env.is_dry_run():
        sys.stdout.write(json.dumps(mark, indent=2, default=str) + "\n")
        return True, "dry run: not posted"
    if not token:
        return False, "VERUS_INGEST_TOKEN is not set"
    body = json.dumps(mark, default=str).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "Authorization": "Bearer " + token,
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return True, "HTTP %s" % resp.status
    except urllib.error.HTTPError as exc:
        detail = ""
        try:
            detail = exc.read().decode("utf-8", "replace")[:300]
        except Exception:
            pass
        return False, "HTTP %s %s %s" % (exc.code, exc.reason, detail)
    except Exception as exc:
        return False, "upload failed: %s" % exc
