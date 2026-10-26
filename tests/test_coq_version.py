"""Check version selection without installing multiple compiler versions."""
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class CoqVersionTests(unittest.TestCase):
    def run_check(self, version):
        with tempfile.TemporaryDirectory(prefix="ucos-coq-version-") as directory:
            compiler = Path(directory) / "coqc"
            compiler.write_text(
                f"#!/bin/sh\nprintf '%s\\n' 'The Coq Proof Assistant, version {version}'\n"
            )
            compiler.chmod(0o755)
            return subprocess.run(
                ["make", "--no-print-directory", "check-coq", f"COQBIN={directory}/"],
                cwd=ROOT, capture_output=True, text=True, check=False,
            )

    def test_required_version_is_accepted(self):
        result = self.run_check("8.18.0")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_other_version_is_rejected(self):
        for version in ("8.20.1", "8.18.1", "8.18.00"):
            with self.subTest(version=version):
                result = self.run_check(version)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("requires Coq 8.18.0", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
