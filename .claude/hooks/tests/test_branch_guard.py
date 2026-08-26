#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Unit tests for branch_guard.py (PreToolUse branch-discipline hook).

Run: python3 .claude/hooks/tests/test_branch_guard.py
"""

import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import branch_guard  # noqa: E402


class BranchNameTest(unittest.TestCase):
    def test_conforming_names(self):
        for name in ("yl/fix-stop-hook", "kg/keycode-2", "abc/x", "yl/a/b.c_d"):
            self.assertTrue(branch_guard._conforms(name), name)

    def test_non_conforming_names(self):
        for name in ("fix-stop-hook", "main", "YL/x", "y/x", "abcd/x", "yl-x", "yl/"):
            self.assertFalse(branch_guard._conforms(name), name)


class ViolationsTest(unittest.TestCase):
    def v(self, cmd):
        return branch_guard.violations(cmd)

    # -- branch creation ---------------------------------------------------
    def test_checkout_b_bad(self):
        self.assertTrue(self.v("git checkout -b keycode-4"))

    def test_checkout_b_good(self):
        self.assertFalse(self.v("git checkout -b yl/keycode-4 origin/main"))

    def test_switch_c_bad(self):
        self.assertTrue(self.v("git switch -c feature"))

    def test_switch_create_good(self):
        self.assertFalse(self.v("git switch --create yl/feature"))

    def test_branch_create_bad(self):
        self.assertTrue(self.v("git branch topic main"))

    def test_branch_rename_checks_new_name(self):
        self.assertTrue(self.v("git branch -m old new"))
        self.assertFalse(self.v("git branch -m fix-stop-hook yl/fix-stop-hook"))

    def test_branch_delete_and_list_allowed(self):
        self.assertFalse(self.v("git branch -d legacy-name"))
        self.assertFalse(self.v("git branch --list"))
        self.assertFalse(self.v("git branch -vv"))

    def test_plain_checkout_allowed(self):
        self.assertFalse(self.v("git checkout main"))
        self.assertFalse(self.v("git switch yl/feature"))

    # -- push --------------------------------------------------------------
    def test_push_main_blocked(self):
        self.assertTrue(self.v("git push origin main"))
        self.assertTrue(self.v("git push -u origin main"))
        self.assertTrue(self.v("git push origin yl/x:main"))

    def test_push_head_resolves_current_branch(self):
        with mock.patch.object(branch_guard, "_current_branch", return_value="main"):
            self.assertTrue(self.v("git push origin HEAD"))
        with mock.patch.object(
            branch_guard, "_current_branch", return_value="yl/feature"
        ):
            self.assertFalse(self.v("git push origin HEAD"))

    def test_bare_push_resolves_current_branch(self):
        with mock.patch.object(
            branch_guard, "_current_branch", return_value="fix-stop-hook"
        ):
            self.assertTrue(self.v("git push"))
        with mock.patch.object(
            branch_guard, "_current_branch", return_value="yl/feature"
        ):
            self.assertFalse(self.v("git push -u origin"))

    def test_push_nonconforming_branch_blocked(self):
        self.assertTrue(self.v("git push origin fix-stop-hook"))
        self.assertFalse(self.v("git push origin yl/fix-stop-hook"))

    def test_push_delete_exempt(self):
        self.assertFalse(self.v("git push origin --delete legacy-name"))

    # -- commit ------------------------------------------------------------
    def test_commit_on_main_blocked(self):
        with mock.patch.object(branch_guard, "_current_branch", return_value="main"):
            self.assertTrue(self.v("git commit -m x"))
        with mock.patch.object(
            branch_guard, "_current_branch", return_value="yl/feature"
        ):
            self.assertFalse(self.v('git commit -m "x"'))

    # -- compound commands & non-git ---------------------------------------
    def test_compound_command_scanned_per_segment(self):
        self.assertTrue(self.v("cargo test && git checkout -b bad-name"))
        self.assertFalse(self.v("cargo test && git checkout -b yl/good"))

    def test_semicolons_attached_to_words(self):
        self.assertTrue(self.v("git checkout -b bad-name; echo done"))
        self.assertFalse(self.v("git checkout -b yl/good; echo done"))
        # The word after `;` starts a new segment, not extra push refspecs.
        self.assertEqual(len(self.v("git push origin bad; echo x")), 1)

    def test_multiline_commands_split_per_line(self):
        self.assertTrue(self.v("cargo test\ngit checkout -b bad-name"))
        self.assertFalse(self.v("git checkout -b yl/a\ngit push origin yl/a"))
        # A following line never bleeds into the previous push's refspecs.
        self.assertEqual(len(self.v("git push origin bad\necho x\ngit status")), 1)

    def test_backslash_continuation_joined(self):
        self.assertTrue(self.v("git push origin \\\n  main"))

    def test_git_global_flags_stripped(self):
        self.assertTrue(self.v("git -C /tmp/x checkout -b bad"))

    def test_non_git_commands_ignored(self):
        self.assertFalse(self.v("ls -la && echo checkout -b nope"))

    def test_unparseable_fails_open(self):
        self.assertFalse(self.v('echo "unclosed'))


class GitHookModesTest(unittest.TestCase):
    """The agent-agnostic backstop modes used by .githooks/ (Codex, humans)."""

    def test_precommit_blocks_protected(self):
        self.assertTrue(branch_guard.precommit_violations("main"))
        self.assertTrue(branch_guard.precommit_violations("master"))
        self.assertFalse(branch_guard.precommit_violations("yl/feature"))
        # Non-conforming branch: warn-only at commit time, not a block.
        self.assertFalse(branch_guard.precommit_violations("legacy-name"))

    def test_prepush_blocks_main_and_nonconforming(self):
        sha = "a" * 40
        lines = [
            "refs/heads/yl/x %s refs/heads/main %s" % (sha, sha),
            "refs/heads/yl/ok %s refs/heads/yl/ok %s" % (sha, sha),
            "refs/heads/legacy %s refs/heads/legacy %s" % (sha, sha),
        ]
        probs = branch_guard.prepush_violations(lines)
        self.assertEqual(len(probs), 2)
        self.assertIn("main", probs[0])
        self.assertIn("legacy", probs[1])

    def test_prepush_exempts_deletes_and_tags(self):
        sha = "a" * 40
        lines = [
            "(delete) %s refs/heads/legacy-name %s" % ("0" * 40, sha),
            "refs/tags/v1.0 %s refs/tags/v1.0 %s" % (sha, "0" * 40),
        ]
        self.assertFalse(branch_guard.prepush_violations(lines))

    def test_prepush_garbage_lines_ignored(self):
        self.assertFalse(branch_guard.prepush_violations(["", "not a refspec"]))

    def test_check_mode_exit_codes(self):
        self.assertEqual(branch_guard.cmd_check(["--command", "git checkout -b bad"]), 2)
        self.assertEqual(branch_guard.cmd_check(["--command", "git checkout -b yl/ok"]), 0)
        self.assertEqual(branch_guard.cmd_check([]), 0)

    def test_unknown_mode_fails_open(self):
        self.assertEqual(branch_guard.main(["no-such-mode"]), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
