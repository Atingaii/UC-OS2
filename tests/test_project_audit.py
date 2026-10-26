"""Exercise the actual audit CLI in independent, minimal project trees."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


AUDITOR = Path(__file__).resolve().parents[1] / "scripts/project-audit.py"


class ProjectAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ucos-audit-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("scripts/project-audit.py", AUDITOR.read_text())
        self.write("csrc/UPSTREAM.lock.json", "{}\n")
        self.write("certiucos/v293/proofs/Test.v", "Theorem ok : True. Proof. exact I. Qed.\n")
        self.write("_CoqProject", "-R . CertiOS\ncertiucos/v293/proofs/Test.v\n")

    def write(self, path, text):
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)

    def audit(self, expected):
        result = subprocess.run(
            ["python3", str(self.root / "scripts/project-audit.py")],
            cwd=self.root, capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result.stdout

    def test_minimal_active_project_passes(self):
        self.audit(0)

    def test_historical_text_is_not_an_active_dependency(self):
        for path in ("references/history.md", "start-prompt.md", "work-prompt.md"):
            self.write(path, "Historical uC/OS-II V2.52 / CertiOS.certiucos.v252\n")
        self.audit(0)

    def test_legacy_coq_dependency_is_rejected(self):
        self.write("certiucos/v293/proofs/Test.v", "Require Import CertiOS.certiucos.v252.Old.\n")
        self.assertIn("legacy-target", self.audit(1))

    def test_legacy_build_manifest_entry_is_rejected(self):
        self.write("_CoqProject", "-R . CertiOS\ncertiucos/v252/Old.v\n")
        self.assertIn("legacy-target", self.audit(1))

    def test_legacy_coq_outside_standard_directories_is_rejected(self):
        self.write("extra/Old.v", "Require Import CertiOS.certiucos.v252.Old.\n")
        self.write("_CoqProject", "-R . CertiOS\nextra/Old.v\n")
        self.assertIn("legacy-target", self.audit(1))

    def test_archive_loadpath_is_rejected(self):
        self.write("_CoqProject", "-R references CertiOS\n")
        self.assertIn("archived-input", self.audit(1))

    def test_archive_build_dependency_is_rejected(self):
        for path in ("_CoqProject", "Makefile", "scripts/build.sh"):
            with self.subTest(path=path):
                self.write(path, "references/old.v\n")
                self.assertIn("archived-input", self.audit(1))
                (self.root / path).unlink()

    def test_proof_escape_after_comment_is_rejected(self):
        self.write("certiucos/v293/proofs/Test.v", "Theorem bad : False.\n(* note *) Admitted.\n")
        self.assertIn("proof escape", self.audit(1))

    def test_nested_multiline_comments_do_not_create_proof_escapes(self):
        self.write("certiucos/v293/proofs/Test.v", (
            "(* Historical warning:\nAdmitted. (* Axiom fake : False. *)\n*)\n"
            'Definition message := "admit (* not a comment *)".\n'
            "Theorem ok : True. Proof. exact I. Qed.\n"
        ))
        self.audit(0)

    def test_plural_assumptions_are_rejected(self):
        for command in ("Axioms", "Parameters", "Conjectures"):
            with self.subTest(command=command):
                self.write("certiucos/v293/proofs/Test.v", f"{command} bad : False.\n")
                self.assertIn("proof escape", self.audit(1))

    def test_missing_active_tree_is_rejected(self):
        shutil.rmtree(self.root / "certiucos")
        self.audit(1)

    def test_missing_source_lock_is_rejected(self):
        (self.root / "csrc/UPSTREAM.lock.json").unlink()
        self.audit(1)


if __name__ == "__main__":
    unittest.main()
