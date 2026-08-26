#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Claude Code `PreToolUse` hook (Bash): enforce the repo's branch discipline.
#
#   1. Every branch name is prefixed with the author's unique initials:
#      `<initials>/<topic>` (2-3 lowercase letters + "/"), e.g. `yl/fix-gate`.
#      The Verus dashboard rolls a branch's telemetry into the `main` view by
#      branch name once its PR merges, so names must never collide between
#      collaborators.
#   2. `main` is never committed to or pushed directly; changes land via PRs.
#
# Blocks by exiting 2 with the reason on stderr (fed back to the agent so it
# can correct itself). FAIL-OPEN: unparseable input exits 0 — the guard must
# never brick the Bash tool.

import json
import os
import re
import shlex
import subprocess
import sys

BRANCH_RE = re.compile(r"^[a-z]{2,3}/[A-Za-z0-9._/-]+$")
OPERATORS = {"&&", "||", ";", "|", "&"}
PROTECTED = ("main", "master")

POLICY = (
    "Branch policy: name branches '<initials>/<topic>' (2-3 lowercase letters "
    "+ '/', e.g. yl/fix-stop-hook) so collaborators' branches never collide, "
    "and never commit to or push main directly - open a PR instead."
)


def _tokens(command):
    try:
        return shlex.split(command, posix=True)
    except ValueError:
        return command.split()


def _segments(tokens):
    """Split a token stream on shell operators into simple-command segments."""
    cur = []
    for tok in tokens:
        if tok in OPERATORS:
            if cur:
                yield cur
            cur = []
        else:
            cur.append(tok)
    if cur:
        yield cur


def _strip_git_globals(args):
    """Drop `git` global options (-C <dir>, -c <k=v>, --git-dir[=..] ...) so
    args[0] is the subcommand."""
    out = list(args)
    while out:
        a = out[0]
        if a in ("-C", "-c", "--git-dir", "--work-tree", "--namespace", "--exec-path"):
            out = out[2:]
        elif a.startswith("--") and "=" in a:
            out = out[1:]
        elif a in ("-p", "--paginate", "--no-pager", "--bare"):
            out = out[1:]
        else:
            break
    return out


def _positionals(args):
    return [a for a in args if not a.startswith("-")]


def _conforms(name):
    return bool(BRANCH_RE.match(name))


def _current_branch():
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if out.returncode == 0:
            return out.stdout.strip()
    except (subprocess.SubprocessError, OSError):
        pass
    return ""


def _new_branch_from_checkout(rest):
    """Branch name created by `git checkout`/`git switch`, or None."""
    for i, tok in enumerate(rest):
        if tok in ("-b", "-B", "-c", "-C", "--create", "--force-create", "--orphan"):
            if i + 1 < len(rest):
                return rest[i + 1]
    return None


def _new_branch_from_branch(rest):
    """Branch name created/renamed-to by `git branch`, or None.

    Deletion/listing/upstream forms create nothing. For rename/copy the NEW
    name is the last positional; for plain creation it is the first.
    """
    non_creating = {
        "-d", "-D", "--delete", "-l", "--list", "-a", "--all", "-r", "--remotes",
        "-v", "-vv", "--verbose", "--show-current", "-u", "--set-upstream-to",
        "--unset-upstream", "--contains", "--no-contains", "--merged",
        "--no-merged", "--edit-description", "--points-at",
    }
    if any(t in non_creating or t.split("=", 1)[0] in non_creating for t in rest):
        return None
    pos = _positionals(rest)
    if not pos:
        return None
    if any(t in ("-m", "-M", "--move", "-c", "-C", "--copy") for t in rest):
        return pos[-1]
    return pos[0]


def _push_dsts(rest):
    """Destination ref names of a `git push`, resolving `HEAD`/bare pushes to
    the current branch. Deletions are exempt (cleanup of legacy names)."""
    if any(t in ("-d", "--delete") for t in rest):
        return []
    pos = _positionals(rest)
    refspecs = pos[1:]  # pos[0] is the remote, when given
    dsts = []
    if not refspecs:
        # `git push` / `git push origin` / `git push -u origin` push the
        # current branch.
        cur = _current_branch()
        if cur and cur != "HEAD":
            dsts.append(cur)
        return dsts
    for spec in refspecs:
        spec = spec.lstrip("+")
        dst = spec.split(":", 1)[1] if ":" in spec else spec
        if dst.startswith("refs/heads/"):
            dst = dst[len("refs/heads/"):]
        if dst == "HEAD":
            dst = _current_branch()
        if dst:
            dsts.append(dst)
    return dsts


def violations(command):
    probs = []
    for seg in _segments(_tokens(command)):
        if not seg or os.path.basename(seg[0]) != "git":
            continue
        args = _strip_git_globals(seg[1:])
        if not args:
            continue
        sub, rest = args[0], args[1:]
        if sub in ("checkout", "switch"):
            name = _new_branch_from_checkout(rest)
            if name and not _conforms(name):
                probs.append("new branch '%s' is not initials-prefixed" % name)
        elif sub == "branch":
            name = _new_branch_from_branch(rest)
            if name and not _conforms(name):
                probs.append("new branch '%s' is not initials-prefixed" % name)
        elif sub == "push":
            for dst in _push_dsts(rest):
                if dst in PROTECTED:
                    probs.append("direct push to '%s' is forbidden; open a PR" % dst)
                elif not _conforms(dst):
                    probs.append(
                        "push of branch '%s' blocked: not initials-prefixed "
                        "(rename with: git branch -m <initials>/%s)" % (dst, dst)
                    )
        elif sub == "commit":
            cur = _current_branch()
            if cur in PROTECTED:
                probs.append(
                    "committing on '%s' is forbidden; create an "
                    "initials-prefixed feature branch first" % cur
                )
    return probs


def main():
    try:
        raw = sys.stdin.read()
        data = json.loads(raw) if raw.strip() else {}
    except Exception:
        return 0
    if data.get("tool_name") != "Bash":
        return 0
    command = (data.get("tool_input") or {}).get("command") or ""
    if not command:
        return 0
    probs = violations(command)
    if probs:
        sys.stderr.write(
            "[branch-guard] BLOCKED:\n"
            + "".join("  - %s\n" % p for p in probs)
            + POLICY
            + "\n"
        )
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
