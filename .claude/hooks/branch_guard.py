#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Basis Research
#
# Branch-discipline guard, shared across agents (like verus_trace):
#
#   1. Every branch name is prefixed with the author's unique initials:
#      `<initials>/<topic>` (2-3 lowercase letters + "/"), e.g. `yl/fix-gate`.
#      The Verus dashboard rolls a branch's telemetry into the `main` view by
#      branch name once its PR merges, so names must never collide between
#      collaborators.
#   2. `main` is never committed to or pushed directly; changes land via PRs.
#   3. `gh pr create` always carries `--repo <BASE_REPO>`: this clone is a fork,
#      so without it gh targets the *upstream* repo and the PR fails with a
#      "no commits between" / "Head sha can't be blank" error.
#
# Entry points (one script, four modes):
#
#   branch_guard.py                    Claude Code PreToolUse hook: reads the
#                                      hook JSON on stdin, inspects Bash
#                                      commands.
#   branch_guard.py check --command C  Agent-agnostic: check one shell command
#                                      (used by the opencode plugin's
#                                      tool.execute.before handler).
#   branch_guard.py pre-commit         Git pre-commit hook body: block commits
#                                      on main (warn on a non-prefixed branch).
#   branch_guard.py pre-push           Git pre-push hook body: reads refspec
#                                      lines on stdin, blocks pushes to main
#                                      and of non-prefixed branches.
#
# The git-hook modes are the agent-agnostic backstop (they cover Codex, which
# has no pre-tool event, and humans). The committed shims live in .githooks/;
# ensure_hooks_path() self-provisions `core.hooksPath .githooks` and is called
# fail-soft from the session-start/stop paths of all three agents.
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
# Shell reserved words and grouping tokens that may lead a simple command.
# Without stripping them, `for b in x; do <cmd>; done` looks like a command
# called `do` and slips past every check in this module.
RESERVED = {
    "if", "then", "elif", "else", "fi",
    "for", "while", "until", "do", "done", "select",
    "case", "esac", "in", "function", "{", "}", "!", "(", ")",
}
PROTECTED = ("main", "master")
# This clone is a fork; `gh pr create` must target this repo explicitly or gh
# defaults the base to the upstream and the PR fails.
BASE_REPO = "BasisResearch/toydb"

POLICY = (
    "Branch policy: name branches '<initials>/<topic>' (2-3 lowercase letters "
    "+ '/', e.g. yl/fix-stop-hook) so collaborators' branches never collide, "
    "and never commit to or push main directly - open a PR instead."
)


HEREDOC_RE = re.compile(r"<<-?\s*(['\"]?)([A-Za-z_][A-Za-z0-9_]*)\1")


def _strip_heredocs(command):
    """Drop heredoc *bodies* before tokenizing. A `gh pr create ... --body
    "$(cat <<'EOF' ... EOF)"` carries example commands (`gh pr create`, `git
    push origin main`) in its body; those are data, not commands to run, and
    must not trip the guard. Keep each opening line (the real command lives
    there) and the delimiter, drop everything in between."""
    lines = command.splitlines()
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        out.append(line)
        delims = [m.group(2) for m in HEREDOC_RE.finditer(line)]
        i += 1
        for delim in delims:
            while i < len(lines) and lines[i].strip() != delim:
                i += 1
            if i < len(lines):
                i += 1  # skip the closing delimiter line itself
    return "\n".join(out)


def _tokens(line):
    """Tokenize one line. punctuation_chars makes shlex split operators off
    words (`bad-name;` -> `bad-name`, `;`) instead of leaving them attached."""
    try:
        lex = shlex.shlex(line, posix=True, punctuation_chars=True)
        lex.whitespace_split = True
        return list(lex)
    except ValueError:
        return line.split()


def _is_redirect(tok):
    """A redirection operator token: `>`, `>>`, `<`, `>&`, `&>`, ... (made of
    `<>&` and containing an angle bracket). `&` alone is the background/join
    operator, not a redirect."""
    return bool(tok) and all(c in "<>&" for c in tok) and (">" in tok or "<" in tok)


def _strip_reserved(seg):
    """Drop leading shell reserved words / grouping tokens so seg[0] is the
    program actually being run."""
    i = 0
    while i < len(seg) and seg[i] in RESERVED:
        i += 1
    return seg[i:]


def _segments(command):
    """Split a (possibly multi-line) command into simple-command segments:
    per line, then on shell operators. Backslash continuations are joined
    first so a wrapped command stays one segment. Redirections are dropped, not
    treated as command boundaries: `git push origin br 2>&1` is one command, so
    the fd number (`2`) and target (`&1`, `/dev/null`) must not leak in as a
    bogus positional (which read as a branch named `2`)."""
    for line in command.replace("\\\n", " ").splitlines():
        cur = []
        toks = _tokens(line)
        i = 0
        while i < len(toks):
            tok = toks[i]
            if _is_redirect(tok):
                if cur and cur[-1].isdigit():
                    cur.pop()  # drop the leading fd, e.g. the 2 in `2>foo`
                i += 2  # skip the operator and its target token
                continue
            if tok in OPERATORS or all(c in "|&;()" for c in tok):
                if cur:
                    stripped = _strip_reserved(cur)
                    if stripped:
                        yield stripped
                cur = []
            else:
                cur.append(tok)
            i += 1
        if cur:
            stripped = _strip_reserved(cur)
            if stripped:
                yield stripped


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


def _gh_pr_create_missing_repo(args):
    """True if `args` (tokens after `gh`) is a `pr create` that omits `--repo`
    / `-R`. This clone is a fork, so gh otherwise picks the upstream as the base
    repo and the PR fails. Only the create subcommand is guarded; `pr view`,
    `pr list`, etc. are unaffected."""
    if len(args) < 2 or args[0] != "pr" or args[1] != "create":
        return False
    for a in args[2:]:
        if a in ("-R", "--repo") or a.startswith("--repo="):
            return False
    return True


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


def _repo_root():
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if out.returncode == 0:
            return out.stdout.strip()
    except (subprocess.SubprocessError, OSError):
        pass
    return ""


def ensure_hooks_path():
    """Self-provision the committed git hooks: point the clone's local
    core.hooksPath at .githooks so the pre-commit/pre-push backstop is active
    regardless of which agent (or human) runs git. Idempotent and fail-soft;
    never overrides a hooksPath the user set to something else."""
    root = _repo_root()
    if not root or not os.path.isdir(os.path.join(root, ".githooks")):
        return
    try:
        cur = subprocess.run(
            ["git", "config", "--local", "core.hooksPath"],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if cur.stdout.strip():
            return  # already set (ours or the user's own choice)
        subprocess.run(
            ["git", "config", "--local", "core.hooksPath", ".githooks"],
            cwd=root,
            capture_output=True,
            timeout=5,
        )
    except (subprocess.SubprocessError, OSError):
        pass


def violations(command):
    probs = []
    for seg in _segments(_strip_heredocs(command)):
        if not seg:
            continue
        prog = os.path.basename(seg[0])
        if prog == "gh":
            if _gh_pr_create_missing_repo(seg[1:]):
                probs.append(
                    "gh pr create without --repo: this clone is a fork, so gh "
                    "targets the upstream repo and the PR fails. Re-run with: "
                    "gh pr create --repo %s --base main" % BASE_REPO
                )
            continue
        if prog != "git":
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


def precommit_violations(current):
    """Blocking problems for a commit on branch `current` (git pre-commit)."""
    if current in PROTECTED:
        return [
            "committing on '%s' is forbidden; create an initials-prefixed "
            "feature branch first" % current
        ]
    return []


def prepush_violations(lines):
    """Blocking problems for a push, from git pre-push refspec stdin lines
    (`<local_ref> <local_sha> <remote_ref> <remote_sha>`). Deletions are
    exempt (legacy-name cleanup); tags are ignored."""
    probs = []
    for line in lines:
        parts = line.split()
        if len(parts) < 4:
            continue
        local_ref, local_sha, remote_ref = parts[0], parts[1], parts[2]
        if local_ref == "(delete)" or set(local_sha) == {"0"}:
            continue
        if not remote_ref.startswith("refs/heads/"):
            continue
        name = remote_ref[len("refs/heads/"):]
        if name in PROTECTED:
            probs.append("direct push to '%s' is forbidden; open a PR" % name)
        elif not _conforms(name):
            probs.append(
                "push of branch '%s' blocked: not initials-prefixed "
                "(rename with: git branch -m <initials>/%s)" % (name, name)
            )
    return probs


def _block(probs):
    sys.stderr.write(
        "[branch-guard] BLOCKED:\n"
        + "".join("  - %s\n" % p for p in probs)
        + POLICY
        + "\n"
    )
    return 2


def cmd_claude_hook():
    """Default mode: Claude Code PreToolUse hook (hook JSON on stdin)."""
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
        return _block(probs)
    return 0


def cmd_check(argv):
    """`check --command <cmd>` (or `check <cmd>`): agent-agnostic single-
    command check, used by the opencode plugin."""
    command = ""
    if len(argv) >= 2 and argv[0] == "--command":
        command = argv[1]
    elif argv:
        command = argv[0]
    probs = violations(command)
    if probs:
        return _block(probs)
    return 0


def cmd_pre_commit():
    current = _current_branch()
    probs = precommit_violations(current)
    if probs:
        return _block(probs)
    if current and current != "HEAD" and not _conforms(current):
        # Warn only: local commits on a legacy branch stay possible; the
        # pre-push hook is where a non-conforming name becomes a hard stop.
        sys.stderr.write(
            "[branch-guard] warning: branch '%s' is not initials-prefixed; "
            "rename before pushing (git branch -m <initials>/%s)\n"
            % (current, current)
        )
    return 0


def cmd_pre_push():
    try:
        lines = sys.stdin.read().splitlines()
    except Exception:
        return 0
    probs = prepush_violations(lines)
    if probs:
        return _block(probs)
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        return cmd_claude_hook()
    sub = argv[0]
    if sub == "check":
        return cmd_check(argv[1:])
    if sub == "pre-commit":
        return cmd_pre_commit()
    if sub == "pre-push":
        return cmd_pre_push()
    if sub == "ensure-hooks-path":
        ensure_hooks_path()
        return 0
    # Unknown mode: fail open — the guard must never brick a hook chain.
    sys.stderr.write("[branch-guard] unknown mode '%s' (ignored)\n" % sub)
    return 0


if __name__ == "__main__":
    sys.exit(main())
