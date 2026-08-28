#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Mark the current branch (or --branch) as a FAILED ATTEMPT on the Verus
# dashboard, or clear such a mark. One script for every agent and for humans:
#
#   python3 .claude/hooks/mark_branch.py failed "why it failed" [--category TAG]
#   python3 .claude/hooks/mark_branch.py clear  ["why we are retrying"]
#   python3 .claude/hooks/mark_branch.py categories
#
# The reason is meant to be SHORT and may be imprecise: a sentence or two on
# what went wrong is enough. Its purpose is to keep the failure around so we
# can filter and analyse failed attempts later and improve the tooling.
#
# Env: VERUS_INGEST_TOKEN (required to upload), VERUS_INGEST_URL (endpoint
# base, shared with session capture), VERUS_INGEST_DRY_RUN=1 (print, do not
# post), VERUS_MARK_AGENT (override agent detection), VERUS_MARK_LOG (local
# JSONL backstop path; default ~/.verus-trace/branch_marks.jsonl).
#
# Exit codes: 0 uploaded (or dry run), 1 bad usage, 2 upload failed (the mark
# is still appended to the local log so it can be re-sent).

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verus_trace import branch_mark as bm  # noqa: E402


def _parser():
    p = argparse.ArgumentParser(
        prog="mark_branch.py",
        description="Mark a toyDB branch as a failed attempt on the Verus dashboard.",
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(sp):
        sp.add_argument("--branch", help="branch to mark (default: current)")
        sp.add_argument("--agent", choices=bm.AGENTS, help="who is marking (auto-detected)")
        sp.add_argument("--session-id", help="agent session id, if known")
        sp.add_argument("--commit", help="commit sha (default: HEAD)")
        sp.add_argument("-C", "--cwd", default=None, help="repo dir (default: .)")

    f = sub.add_parser("failed", help="mark the branch as a failed attempt")
    f.add_argument("reason", nargs="+", help="short description of why it failed")
    f.add_argument(
        "--category", "-c",
        help="short tag for grouping; see `categories` (free-form allowed)",
    )
    common(f)

    c = sub.add_parser("clear", help="un-mark: the branch is no longer considered failed")
    c.add_argument("reason", nargs="*", help="optional note, e.g. why we are retrying")
    common(c)

    sub.add_parser("categories", help="print the suggested category tags")
    return p


def main(argv=None):
    args = _parser().parse_args(argv)
    if args.cmd == "categories":
        for c in bm.SUGGESTED_CATEGORIES:
            print(c)
        return 0

    status = "failed" if args.cmd == "failed" else "cleared"
    reason = " ".join(args.reason or [])
    category = getattr(args, "category", None)
    if status == "failed" and not category:
        sys.stderr.write(
            "[verus-mark] note: no --category given; consider one of: %s\n"
            % ", ".join(bm.SUGGESTED_CATEGORIES)
        )
    try:
        mark = bm.build_mark(
            reason,
            status=status,
            category=category,
            branch=args.branch,
            cwd=args.cwd,
            agent=args.agent,
            session_id=args.session_id,
            commit=args.commit,
        )
    except ValueError as exc:
        sys.stderr.write("[verus-mark] error: %s\n" % exc)
        return 1

    ok, msg = bm.post_mark(mark)
    log_path = bm.append_local_log(mark, ok)
    verb = "marked FAILED" if status == "failed" else "cleared"
    if ok:
        sys.stderr.write(
            "[verus-mark] %s %s (%s%s) -> %s\n"
            % (
                verb,
                mark["branch"],
                ("[" + mark["category"] + "] ") if mark.get("category") else "",
                mark["reason"] or "no reason",
                msg,
            )
        )
        return 0
    sys.stderr.write(
        "[verus-mark] %s %s locally but UPLOAD FAILED: %s\n"
        "[verus-mark] the mark was appended to %s; re-run once the token/network is fixed\n"
        % (verb, mark["branch"], msg, log_path or "(no local log)")
    )
    return 2


if __name__ == "__main__":
    sys.exit(main())
