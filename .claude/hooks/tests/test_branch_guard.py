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

    def test_git_global_flags_stripped(self):
        self.assertTrue(self.v("git -C /tmp/x checkout -b bad"))

    def test_non_git_commands_ignored(self):
        self.assertFalse(self.v("ls -la && echo checkout -b nope"))

    def test_unparseable_fails_open(self):
        self.assertFalse(self.v('echo "unclosed'))


if __name__ == "__main__":
    unittest.main(verbosity=2)
