"""Compile fixtures to test the actual choice-reduction foundation audit."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class ChoiceReductionAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lake = os.environ.get("LAKE", "lake")
        prefix = subprocess.check_output(
            [lake, "env", "lean", "--print-prefix"], cwd=ROOT, text=True
        ).strip()
        cls.lean = str(Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean"))
        cls.lean_path = subprocess.check_output(
            [lake, "env", os.sys.executable, "-c", "import os; print(os.environ.get('LEAN_PATH', ''))"],
            cwd=ROOT, text=True,
        ).strip()
        source = (ROOT / "checks" / "ChoiceReductionAxioms.lean").read_text()
        cls.audit_commands = source.split("open Lean Elab Command\n", 1)[1]

    def run_fixture(self, source: str, helper: str = ""):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(root) + os.pathsep + self.lean_path

            def compile_file(path: Path, contents: str):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents)
                result = subprocess.run(
                    [self.lean, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=root, env=env, text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, timeout=60,
                )
                self.assertEqual(result.returncode, 0, result.stdout)

            if helper:
                compile_file(root / "ExternalHelper.lean", helper)
                source = "import ExternalHelper\n" + source
            fixture = root / "Adiabatic" / "ChoiceReduction" / "AuditFixture.lean"
            compile_file(fixture, source)
            audit = root / "Audit.lean"
            audit.write_text(
                "import Adiabatic.ChoiceReduction.AuditFixture\n"
                "import Lean.Util.CollectAxioms\n"
                "import Lean.Elab.Command\n"
                "open Lean Elab Command\n" + self.audit_commands
            )
            return subprocess.run(
                [self.lean, str(audit)], cwd=root, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60,
            )

    def assert_rejected(self, source: str, helper: str = ""):
        result = self.run_fixture(source, helper)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Disallowed foundations", result.stdout)

    def test_constructive_proofs_pass(self):
        result = self.run_fixture(
            "private theorem checked : True := True.intro\n"
            "theorem OtherNamespace.result : True := checked\n"
            "theorem extensionality (p q : Prop) (h : p ↔ q) : p = q := propext h\n"
            "theorem functions (f g : Nat → Nat) (h : ∀ n, f n = g n) : f = g := funext h\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("Audited all", result.stdout)

    def test_unused_private_choice_definition_fails(self):
        self.assert_rejected(
            "private noncomputable def chosen : Nat := Classical.choice ⟨0⟩\n"
        )

    def test_classical_logic_fails(self):
        self.assert_rejected(
            "theorem OtherNamespace.excluded_middle (p : Prop) : p ∨ ¬p := Classical.em p\n"
        )

    def test_dependency_in_statement_alone_fails(self):
        self.assert_rejected(
            "theorem OtherNamespace.result : hiddenProposition := True.intro\n",
            "noncomputable def hiddenProposition : Prop := "
            "let _chosen : Nat := Classical.choice ⟨0⟩; True\n",
        )

    def test_imported_proof_dependency_fails(self):
        self.assert_rejected(
            "theorem OtherNamespace.result (p : Prop) : p ∨ ¬p := helper p\n",
            "theorem helper (p : Prop) : p ∨ ¬p := Classical.em p\n",
        )

    def test_added_axioms_and_placeholders_fail(self):
        for source in (
            "axiom OtherNamespace.unused : False\n",
            "theorem OtherNamespace.bad : False := by sorry\n",
        ):
            with self.subTest(source=source):
                self.assert_rejected(source)

    def test_unsafe_definition_fails(self):
        result = self.run_fixture("unsafe def OtherNamespace.unchecked : Nat := 0\n")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Unsafe choice-reduction declaration", result.stdout)

    def test_empty_selection_fails(self):
        result = self.run_fixture("")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("No declarations from the choice-reduction modules", result.stdout)


if __name__ == "__main__":
    unittest.main()
