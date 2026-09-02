#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Unit tests for verus_cli_guard.py (PreToolUse "Verus goes through MCP" hook).

Run: python3 .claude/hooks/tests/test_verus_cli_guard.py
"""

import json
import os
import subprocess
import sys
import unittest
from unittest import mock

HOOKS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, HOOKS)

import verus_cli_guard as g  # noqa: E402

GUARD = os.path.join(HOOKS, "verus_cli_guard.py")


class BlockedTest(unittest.TestCase):
    def v(self, cmd):
        with mock.patch.dict(os.environ, {g.DISABLE_ENV: ""}):
            return g.violations(cmd)

    def test_bare_verus(self):
        self.assertTrue(self.v("verus src/lib.rs --crate-type=lib"))
        self.assertTrue(self.v("~/.local/verus/verus-x86-linux/verus model.rs"))
        self.assertTrue(self.v("/opt/verus/source/target-verus/release/rust_verify x.rs"))

    def test_cargo_verus(self):
        self.assertTrue(self.v("cargo verus focus --lib -- --verify-module raft::log"))
        self.assertTrue(self.v("cargo verus verify"))
        self.assertTrue(self.v("cargo +nightly verus focus"))
        self.assertTrue(self.v("cargo-verus focus --lib"))

    def test_verify_script(self):
        self.assertTrue(self.v("scripts/verus/verify.sh"))
        self.assertTrue(self.v("./scripts/verus/verify.sh --output-json > out.json 2> err.log"))
        self.assertTrue(self.v("bash scripts/verus/verify.sh 2>&1 | tail -15"))
        self.assertTrue(self.v("/home/x/toydb/scripts/verus/verify.sh"))

    # -- wrappers seen in real transcripts ---------------------------------
    def test_timeout_time_env_wrappers(self):
        self.assertTrue(self.v("timeout 570 cargo verus focus --lib -- --verify-module storage::mvcc"))
        self.assertTrue(self.v("timeout -k 5 570 bash scripts/verus/verify.sh"))
        self.assertTrue(self.v("time cargo verus focus --lib 2>&1 | grep -vE 'warning'"))
        self.assertTrue(self.v("(time ./scripts/verus/verify.sh --time) > v.log 2>&1; echo $?"))
        self.assertTrue(self.v("VERUS_SMT_LOG_DISABLE=1 scripts/verus/verify.sh"))
        self.assertTrue(self.v("env VERUS_SMT_LOG_ROOT=/tmp/x bash scripts/verus/verify.sh"))
        self.assertTrue(self.v("nice -n 10 cargo verus focus"))
        self.assertTrue(self.v("nohup cargo verus focus &"))

    def test_shell_dash_c(self):
        self.assertTrue(self.v('bash -c "cargo verus focus --lib"'))
        self.assertTrue(self.v("sh -c 'scripts/verus/verify.sh'"))

    def test_shell_c_bundled_with_other_short_flags(self):
        """`bash -lc "..."` is a common agent idiom; matching only a bare
        `-c` token let every bundled form through."""
        self.assertTrue(self.v('bash -lc "cargo verus focus --lib"'))
        self.assertTrue(self.v('sh -xc "verus src/lib.rs"'))
        self.assertTrue(self.v('zsh -ic "cargo verus focus"'))
        self.assertTrue(self.v('bash -o pipefail -c "verus x.rs"'))
        # A bundled cluster without `c` is not a command string.
        self.assertFalse(self.v('bash -l scripts/build.sh'))

    def test_noexec_syntax_check_is_not_a_run(self):
        """`bash -n <script>` parses and exits; nothing executes."""
        self.assertFalse(self.v("bash -n scripts/verus/verify.sh"))
        self.assertFalse(self.v("sh -n scripts/verus/verify.sh"))
        self.assertTrue(self.v("bash scripts/verus/verify.sh"))

    def test_shell_reserved_words_do_not_hide_the_command(self):
        """Without stripping reserved words the program reads as `do` / `then`
        / `{`, and a loop over modules — the natural way to use this — runs
        Verus unnoticed."""
        self.assertTrue(self.v(
            "for m in a b; do cargo verus focus --lib -- --verify-module $m; done"))
        self.assertTrue(self.v("while read m; do verus $m; done < list"))
        self.assertTrue(self.v("if [ -f x ]; then scripts/verus/verify.sh; fi"))
        self.assertTrue(self.v("{ cargo verus focus; }"))
        self.assertTrue(self.v("! cargo verus focus"))
        # Ordinary loops stay allowed.
        self.assertFalse(self.v("for f in a b; do cargo test $f; done"))
        self.assertFalse(self.v("if true; then cargo build; fi"))

    def test_privilege_and_scheduling_wrappers(self):
        self.assertTrue(self.v("sudo verus x.rs"))
        self.assertTrue(self.v("sudo -u bob cargo verus focus"))
        self.assertTrue(self.v("setsid cargo verus focus"))
        self.assertTrue(self.v("ionice -c 3 verus a.rs"))
        self.assertTrue(self.v("taskset -c 0-3 cargo verus focus"))
        self.assertTrue(self.v("taskset 0x3 verus a.rs"))

    def test_env_options_are_skipped_not_treated_as_the_program(self):
        """An unknown `env` option used to end the walk, so `-C` became the
        program name and the real command was never inspected."""
        self.assertTrue(self.v("env -C /tmp verus a.rs"))
        self.assertTrue(self.v("env --chdir=/repo cargo verus focus"))
        self.assertTrue(self.v('env -S "verus a.rs"'))
        self.assertTrue(self.v('env --split-string="cargo verus focus"'))
        self.assertFalse(self.v("env -C /tmp cargo test"))

    def test_compound_and_pipes(self):
        self.assertTrue(self.v("touch src/raft/log.rs && cargo verus focus --lib -- --verify-module raft::log 2>&1 | tail -5"))
        self.assertTrue(self.v("cargo test\ncargo verus focus"))
        self.assertTrue(self.v("rm -rf target/vbase; cargo verus focus --target-dir target/vbase --lib"))

    def test_command_substitution(self):
        self.assertTrue(self.v("out=$(cargo verus focus --lib 2>&1); echo \"$out\""))
        self.assertTrue(self.v("echo `verus x.rs`"))


class AllowedTest(unittest.TestCase):
    def v(self, cmd):
        with mock.patch.dict(os.environ, {g.DISABLE_ENV: ""}):
            return g.violations(cmd)

    def test_help_and_version(self):
        self.assertFalse(self.v("verus --version"))
        self.assertFalse(self.v("verus --help"))
        self.assertFalse(self.v("cargo verus --help"))
        self.assertFalse(self.v("cargo verus focus --help 2>&1 | head -30"))
        self.assertFalse(self.v("cargo-verus -V"))

    def test_lookups_not_runs(self):
        self.assertFalse(self.v("command -v verus"))
        self.assertFalse(self.v("command -v cargo-verus || echo missing"))
        self.assertFalse(self.v("which verus cargo-verus"))
        self.assertFalse(self.v("verus_dir=$(dirname $(command -v verus)); ls \"$verus_dir\""))

    def test_mentions_are_not_runs(self):
        self.assertFalse(self.v("cat scripts/verus/verify.sh"))
        self.assertFalse(self.v("sed -n 40,80p scripts/verus/verify.sh"))
        self.assertFalse(self.v("grep -rn 'cargo verus' .github scripts"))
        self.assertFalse(self.v("echo 'run: cargo verus focus'"))
        self.assertFalse(self.v("python3 scripts/verus/extract_metrics.py --output m.json"))
        self.assertFalse(self.v("ls ~/.verus-trace/smt/pending"))

    def test_heredoc_bodies_ignored(self):
        cmd = "cat > notes.md <<'EOF'\nrun cargo verus focus --lib\nEOF\n"
        self.assertFalse(self.v(cmd))
        # Backticks / $(...) inside a heredoc body are prose, not substitutions.
        cmd = ("python3 - <<'PY'\ns = 'Uses `cargo verus focus` by default'\n"
               "t = '$(verus x.rs)'\nPY\ncargo build")
        self.assertFalse(self.v(cmd))
        # ... but a real substitution after the heredoc is still caught.
        self.assertTrue(self.v("cat <<'EOF'\nhi\nEOF\necho `cargo verus focus`"))

    def test_ordinary_cargo(self):
        self.assertFalse(self.v("cargo test --lib"))
        self.assertFalse(self.v("cargo build && cargo clippy --tests"))
        self.assertFalse(self.v("cargo +nightly fmt --check"))

    def test_mcp_dev_server_allowed(self):
        self.assertFalse(self.v("cd ../verus-tools-mcp && ./scripts/dev-http.sh"))
        self.assertFalse(self.v("verus-tools-mcp stdio"))

    def test_disable_env(self):
        with mock.patch.dict(os.environ, {g.DISABLE_ENV: "1"}):
            self.assertFalse(g.violations("cargo verus focus --lib"))

    def test_unparseable_fails_open(self):
        self.assertFalse(self.v('echo "unclosed'))


class EntryPointsTest(unittest.TestCase):
    def run_hook(self, payload, args=()):
        env = dict(os.environ)
        env[g.DISABLE_ENV] = ""
        return subprocess.run(
            [sys.executable, GUARD, *args],
            input=payload,
            capture_output=True,
            text=True,
            env=env,
            timeout=20,
        )

    def test_claude_hook_blocks_bash_verus(self):
        r = self.run_hook(json.dumps({
            "tool_name": "Bash",
            "tool_input": {"command": "cargo verus focus --lib"},
        }))
        self.assertEqual(r.returncode, 2)
        self.assertIn("[verus-guard] BLOCKED", r.stderr)
        self.assertIn("crate_name=", r.stderr)
        self.assertIn(g.DISABLE_ENV, r.stderr)

    def test_claude_hook_allows_other_tools_and_commands(self):
        r = self.run_hook(json.dumps({
            "tool_name": "Bash", "tool_input": {"command": "cargo test"},
        }))
        self.assertEqual(r.returncode, 0)
        r = self.run_hook(json.dumps({
            "tool_name": "Read", "tool_input": {"file_path": "x"},
        }))
        self.assertEqual(r.returncode, 0)

    def test_claude_hook_bad_input_fails_open(self):
        self.assertEqual(self.run_hook("not json").returncode, 0)
        self.assertEqual(self.run_hook("").returncode, 0)

    def test_check_mode_exit_codes(self):
        r = self.run_hook("", ["check", "--command", "verus x.rs"])
        self.assertEqual(r.returncode, 2)
        r = self.run_hook("", ["check", "--command", "cargo build"])
        self.assertEqual(r.returncode, 0)

    def test_unknown_mode_fails_open(self):
        self.assertEqual(self.run_hook("", ["bogus"]).returncode, 0)


if __name__ == "__main__":
    unittest.main()
