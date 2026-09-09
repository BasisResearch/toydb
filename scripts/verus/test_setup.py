#!/usr/bin/env python3
"""Exercise upstream installation without network, rustup, or solver execution."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import zipfile


class UpstreamSetupTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        scripts = self.root / "scripts/verus"
        scripts.mkdir(parents=True)
        self.script = scripts / "setup-upstream-verus.sh"
        shutil.copyfile(Path(__file__).with_name(self.script.name), self.script)
        self.verus_zip = self.root / "verus.zip"
        with zipfile.ZipFile(self.verus_zip, "w") as z:
            z.writestr("verus-x86-linux/version.json", json.dumps({"verus": {
                "commit": "a" * 40, "version": "test", "toolchain": "test-toolchain",
            }}))
            z.writestr("verus-x86-linux/vstd/Cargo.toml", '[package]\nversion = "test"\n')
            z.writestr("verus-x86-linux/z3", "bundled upstream z3")
        self.cvc5_zip = self.root / "cvc5.zip"
        with zipfile.ZipFile(self.cvc5_zip, "w") as z:
            z.writestr("cvc5-Linux-static/bin/cvc5", "official cvc5")
        self.pins = scripts / "pins.env"
        self.pins.write_text(
            "UPSTREAM_VERUS_TAG=release/test\n"
            f"UPSTREAM_VERUS_SHA256={hashlib.sha256(self.verus_zip.read_bytes()).hexdigest()}\n"
            "UPSTREAM_CVC5_TAG=cvc5-test\n"
            f"UPSTREAM_CVC5_SHA256={hashlib.sha256(self.cvc5_zip.read_bytes()).hexdigest()}\n"
        )
        (self.root / "Cargo.lock").write_text('[[package]]\nname = "vstd"\nversion = "test"\n')
        mocks = self.root / "mocks"
        mocks.mkdir()
        curl = mocks / "curl"
        curl.write_text('''#!/usr/bin/env python3
import os, shutil, sys
from pathlib import Path
url = sys.argv[-1]
with open(os.environ["DOWNLOAD_LOG"], "a") as f:
    f.write(url + "\\n")
if url == "https://github.com/verus-lang/verus/releases/download/release/test/verus-test-x86-linux.zip":
    source = os.environ["VERUS_FIXTURE"]
elif url == "https://github.com/cvc5/cvc5/releases/download/cvc5-test/cvc5-Linux-static.zip":
    source = os.environ["CVC5_FIXTURE"]
else:
    sys.exit("Unexpected download: " + url)
shutil.copyfile(source, sys.argv[sys.argv.index("-o") + 1])
''')
        curl.chmod(0o755)
        rustup = mocks / "rustup"
        rustup.write_text('#!/usr/bin/env bash\nprintf "%s\\n" "$*" >> "$RUSTUP_LOG"\n')
        rustup.chmod(0o755)
        self.env = dict(os.environ, PATH=str(mocks) + os.pathsep + os.environ["PATH"],
                        VERUS_UPSTREAM_CI_DIR=str(self.root / "installed"),
                        VERUS_FIXTURE=str(self.verus_zip), CVC5_FIXTURE=str(self.cvc5_zip),
                        DOWNLOAD_LOG=str(self.root / "downloads"), RUSTUP_LOG=str(self.root / "rustup"),
                        GITHUB_ENV=str(self.root / "env"), GITHUB_OUTPUT=str(self.root / "output"),
                        GITHUB_PATH=str(self.root / "path"))

    def run_setup(self, solver):
        return subprocess.run(["bash", str(self.script), solver], env=self.env,
                              capture_output=True, text=True)

    def test_z3_uses_only_official_verus_bundle(self):
        result = self.run_setup("z3")
        self.assertEqual(result.returncode, 0, result.stderr)
        env = (self.root / "env").read_text()
        self.assertIn("VERUS_Z3_PATH=", env)
        self.assertNotIn("VERUS_CVC5_PATH=", env)
        self.assertNotIn("VERUS_MCP_ENABLED=", env)
        self.assertEqual(len((self.root / "downloads").read_text().splitlines()), 1)
        self.assertIn("verus_commit=" + "a" * 40, (self.root / "output").read_text())

    def test_cvc5_installs_official_cvc5_and_bundled_z3(self):
        result = self.run_setup("cvc5")
        self.assertEqual(result.returncode, 0, result.stderr)
        env = dict(line.split("=", 1) for line in (self.root / "env").read_text().splitlines())
        self.assertEqual(Path(env["VERUS_CVC5_PATH"]).read_text(), "official cvc5")
        self.assertEqual(Path(env["VERUS_Z3_PATH"]).read_text(), "bundled upstream z3")

    def test_rejects_bad_verus_checksum_before_installation(self):
        with self.verus_zip.open("ab") as f:
            f.write(b"tampered")
        self.assertNotEqual(self.run_setup("z3").returncode, 0)
        self.assertFalse((self.root / "rustup").exists())

    def test_rejects_bad_cvc5_checksum(self):
        with self.cvc5_zip.open("ab") as f:
            f.write(b"tampered")
        self.assertNotEqual(self.run_setup("cvc5").returncode, 0)
        self.assertNotIn("VERUS_CVC5_PATH=", (self.root / "env").read_text())

    def test_rejects_vstd_mismatch_before_installation(self):
        (self.root / "Cargo.lock").write_text('[[package]]\nname = "vstd"\nversion = "other"\n')
        result = self.run_setup("z3")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("differs from Cargo.lock", result.stderr)
        self.assertFalse((self.root / "rustup").exists())

    def test_rejects_unknown_solver_before_download(self):
        self.assertNotEqual(self.run_setup("unknown").returncode, 0)
        self.assertFalse((self.root / "downloads").exists())

    def test_basis_installs_both_release_pinned_solvers_and_checks_hashes(self):
        script = self.script.with_name("setup-verus.sh")
        shutil.copyfile(Path(__file__).with_name(script.name), script)
        self.pins.write_text("VERUS_REF=main\n")
        solvers = {}
        assets = {}
        for name in ("z3", "cvc5"):
            asset = self.root / name
            asset.write_text(f"pinned Basis {name}")
            assets[name] = str(asset)
            solvers[name] = dict(repo=f"BasisResearch/{name}", tag="test", asset_x86_linux=name,
                                 sha256_x86_linux=hashlib.sha256(asset.read_bytes()).hexdigest())
        archive = self.root / "verus-x86-linux.zip"
        with zipfile.ZipFile(archive, "w") as z:
            z.writestr("verus-x86-linux/version.json", json.dumps({"verus": dict(
                commit="a" * 40, version="test", toolchain="1.97.1-x86_64-unknown-linux-gnu",
                solvers=solvers)}))
            z.writestr("verus-x86-linux/vstd/Cargo.toml", '[package]\nversion = "test"\n')
        checksum = self.root / "verus-x86-linux.zip.sha256"
        checksum.write_text(hashlib.sha256(archive.read_bytes()).hexdigest() + "  verus-x86-linux.zip\n")
        assets[archive.name] = str(archive)
        assets[checksum.name] = str(checksum)
        (self.root / "mocks/curl").write_text('''#!/usr/bin/env python3
import json, os, shutil, sys
name = sys.argv[-1].rsplit("/", 1)[1]
dest = sys.argv[sys.argv.index("-o") + 1] if "-o" in sys.argv else name
shutil.copyfile(json.loads(os.environ["ASSETS"])[name], dest)
''')
        env = dict(self.env, VERUS_TAG="basis-test", VERUS_CI_DIR=str(self.root / "basis"),
                   ASSETS=json.dumps(assets))
        result = subprocess.run(["bash", str(script), "install"], env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        exported = dict(line.split("=", 1) for line in (self.root / "env").read_text().splitlines())
        for name in ("z3", "cvc5"):
            self.assertEqual(Path(exported[f"VERUS_{name.upper()}_PATH"]).read_text(), f"pinned Basis {name}")
        self.assertEqual(exported["VERUS_MCP_ENABLED"], "1")
        (self.root / "cvc5").write_text("tampered")
        result = subprocess.run(["bash", str(script), "install"], env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)


class VerificationResultTest(unittest.TestCase):
    def test_only_completed_success_passes(self):
        script = Path(__file__).with_name("check_verification_result.sh")
        for setup, outcome, ran, rc, expected in [
            ("success", "success", "true", "0", 0),
            ("failure", "success", "false", "", 1),
            ("success", "success", "true", "1", 1),
            ("success", "failure", "true", "0", 1),
            ("success", "skipped", "", "", 1),
            ("success", "success", "true", "", 1),
            ("", "", "", "", 1),
        ]:
            with self.subTest(setup=setup, outcome=outcome, ran=ran, rc=rc):
                env = dict(os.environ, SETUP_OUTCOME=setup, VERIFY_OUTCOME=outcome,
                           VERUS_RAN=ran, VERUS_RC=rc)
                result = subprocess.run(["bash", str(script)], env=env, capture_output=True)
                self.assertEqual(result.returncode, expected, result.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
