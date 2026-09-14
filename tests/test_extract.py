from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "lean-extract"
LEAN = os.environ.get("TEST_LEAN") or shutil.which("lean") or "lean"
PREFIX = subprocess.check_output([LEAN, "--print-prefix"], cwd=ROOT, text=True).strip()
LEAN = str(Path(PREFIX) / "bin" / "lean")


class ExtractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lean-extract-test-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.source = self.directory / "Input.lean"
        self.output = self.directory / "Output.lean"

    def run_extract(self, source: str | bytes, target="target", extra=(), success=True):
        if isinstance(source, str):
            source = source.encode("utf-8")
        self.source.write_bytes(source)
        proc = subprocess.run(
            [sys.executable, str(CLI), str(self.source), "--theorem", target,
             "--output", str(self.output), "--lean", LEAN, *extra],
            text=True, capture_output=True, cwd=self.directory,
        )
        if success:
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            check = subprocess.run([LEAN, str(self.output)], text=True, capture_output=True, cwd=self.directory)
            self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
            return self.output.read_bytes()
        self.assertNotEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        return proc

    def test_transitive_proof_and_statement_dependencies(self):
        source = (ROOT / "tests/fixtures/Basic.lean").read_bytes()
        output = self.run_extract(source, "Example.target")
        for part in (b"import Lean", b"def base", b"def derived", b"theorem helper", b"namespace Example", b"end Example"):
            self.assertIn(part, output)
        self.assertNotIn(b"theorem irrelevant", output)
        self.assertNotIn(b"This declaration should be deleted", output)
        self.assertNotIn(b"theorem later", output)
        self.assertIn(b"/-- Keep this documentation and the original proof. -/\ntheorem target : derived = 8 := by\n  exact helper", output)

    def test_sorry_variables_notation_macro_and_unicode(self):
        source = """import Lean
namespace Demo
universe u
section
variable {\u03b1 : Type u} (x : \u03b1)
structure Box (\u03b1 : Type u) where
  value : \u03b1
local notation "BOX" => Box
macro "finish_here" : tactic => `(tactic| sorry)
theorem unused : True := by trivial
theorem target : \u2203 b : BOX \u03b1, b.value = x := by
  finish_here
end
end Demo
"""
        output = self.run_extract(source)
        self.assertNotIn(b"theorem unused", output)
        self.assertIn('theorem target : \u2203 b : BOX \u03b1, b.value = x := by\n  finish_here'.encode(), output)
        self.assertIn(b'(tactic| sorry)', output)

    def test_direct_sorry_keeps_statement_dependencies(self):
        output = self.run_extract("""def needed : Nat := 3
def unused : Nat := 9
theorem target : needed = 3 := by sorry
""")
        self.assertIn(b"def needed", output)
        self.assertIn(b"by sorry", output)
        self.assertNotIn(b"def unused", output)

    def test_proof_reference_even_when_tactic_does_not_use_it(self):
        output = self.run_extract("""theorem extraLemma : 1 = 1 := rfl
theorem unused : True := by trivial
theorem target (n : Nat) : n = n := by
  simp only [extraLemma]
""")
        self.assertIn(b"theorem extraLemma", output)
        self.assertNotIn(b"theorem unused", output)

    def test_structures_constructor_fields_and_opaque(self):
        output = self.run_extract("""structure Hidden where
  value : Nat
structure Box where
  hidden : Hidden
def seed : Nat := 3
opaque secret : Nat := seed
def unused : Nat := 99
theorem target (b : Box) : b = b \u2227 secret = secret := by
  constructor <;> rfl
""")
        for part in (b"structure Hidden", b"structure Box", b"def seed", b"opaque secret"):
            self.assertIn(part, output)
        self.assertNotIn(b"def unused", output)

    def test_attributes_instances_and_context_dependencies(self):
        output = self.run_extract("""def value : Nat := 3
theorem value_eq : value = 3 := rfl
attribute [simp] value_eq
class HasValue where
  value : Nat
instance : HasValue := \u27e83\u27e9
@[simp] theorem extra : 0 + 0 = 0 := rfl
theorem unrelated : True := by trivial
theorem target : value = 3 := by simp
""")
        for part in (b"theorem value_eq", b"attribute [simp]", b"instance : HasValue", b"@[simp] theorem extra"):
            self.assertIn(part, output)
        self.assertNotIn(b"theorem unrelated", output)

    def test_private_names_survive_module_and_counter_changes(self):
        output = self.run_extract("""namespace N
private def unused : Nat := 1
private def hidden : Nat := 3
private theorem support : hidden = 3 := rfl
private theorem target : hidden = 3 := support
end N
""", "N.target")
        self.assertNotIn(b"private def unused", output)
        self.assertIn(b"private def hidden", output)
        self.assertIn(b"private theorem support", output)

    def test_mutual_where_and_deriving(self):
        output = self.run_extract("""mutual
  def even : Nat \u2192 Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat \u2192 Bool
    | 0 => false
    | n + 1 => even n
end
structure S where
  n : Nat
deriving DecidableEq
def increment (n : Nat) : Nat := helper n
where
  helper (x : Nat) := x + 1
theorem unused : True := by trivial
theorem target : even 2 = true \u2227 increment 0 = 1 := by
  constructor <;> rfl
""")
        self.assertIn(b"mutual", output)
        self.assertIn(b"def odd", output)
        self.assertIn(b"helper (x : Nat)", output)
        self.assertIn(b"deriving DecidableEq", output)
        self.assertNotIn(b"theorem unused", output)

    def test_unrelated_mutual_block_is_removed(self):
        output = self.run_extract("""mutual
  def first : Nat := 1
  def second : Nat := 2
end
theorem target : True := by trivial
""")
        self.assertNotIn(b"mutual", output)
        self.assertNotIn(b"def first", output)

    def test_crlf_and_internal_comments_preserved(self):
        source = b"import Lean\r\n\r\ndef unused := 1\r\n/-- Kept. -/\r\ntheorem target : True := by\r\n  /- proof comment -/\r\n  trivial\r\n"
        output = self.run_extract(source)
        self.assertIn(source[source.index(b"/-- Kept."):], output)
        self.assertTrue(output.startswith(b"import Lean\r\n"))

    def test_error_after_target_and_existing_output_are_preserved(self):
        self.output.write_text("existing output", encoding="utf-8")
        proc = self.run_extract("theorem target : True := by trivial\ndef broken : Nat := missing\n", extra=("--force",), success=False)
        self.assertIn("failed Lean checking", proc.stderr)
        self.assertEqual(self.output.read_text(), "existing output")

    def test_ambiguous_missing_and_imported_theorem(self):
        proc = self.run_extract("namespace A\ntheorem target : True := by trivial\nend A\nnamespace B\ntheorem target : True := by trivial\nend B\n", success=False)
        self.assertIn("ambiguous", proc.stderr)
        self.assertIn("A.target", proc.stderr)
        self.assertIn("B.target", proc.stderr)
        proc = self.run_extract("import Lean\n", target="Nat.add_comm", success=False)
        self.assertIn("defined in the input file", proc.stderr)

    def test_no_overwrite_without_force(self):
        self.output.write_text("existing", encoding="utf-8")
        proc = self.run_extract("theorem target : True := by trivial\n", success=False)
        self.assertIn("--force", proc.stderr)
        self.assertEqual(self.output.read_text(), "existing")

    def test_escaped_short_name_and_successful_force(self):
        self.output.write_text("old output", encoding="utf-8")
        output = self.run_extract("""namespace N
theorem \u00abtarget.name\u00bb : True := by trivial
end N
""", "\u00abtarget.name\u00bb", extra=("--force",))
        self.assertNotIn(b"old output", output)
        self.assertIn("theorem \u00abtarget.name\u00bb".encode(), output)

    def test_module_sensitive_type_change_is_rejected(self):
        proc = self.run_extract("""import Lean
elab "ambientType" : term => do
  return if (\u2190 Lean.getEnv).mainModule == `Input then
    Lean.mkConst ``Nat
  else
    Lean.mkConst ``Bool
theorem target (x : ambientType) : x = x := rfl
""", success=False)
        self.assertIn("target theorem type changed", proc.stderr)
        self.assertFalse(self.output.exists())

    def test_new_sorry_from_tactic_execution_is_rejected(self):
        proc = self.run_extract("""import Lean
elab "finishHere" : tactic => do
  if (\u2190 Lean.getEnv).mainModule == `Input then
    Lean.Elab.Tactic.evalTactic (\u2190 `(tactic| trivial))
  else
    Lean.Elab.Tactic.evalTactic (\u2190 `(tactic| sorry))
theorem target : True := by finishHere
""", success=False)
        self.assertIn("introduced sorry", proc.stderr)
        self.assertFalse(self.output.exists())

    def test_type_verifier_rejects_dependency_body_change(self):
        self.source.write_text("def value : Nat := 1\ntheorem target : value = value := rfl\n", encoding="utf-8")
        plan = self.directory / "plan.json"
        request = self.directory / "request.json"
        config = {"mode": "extract", "input": str(self.source), "moduleName": "Input",
                  "theoremName": "target", "result": str(plan), "candidate": str(self.output),
                  "plan": "", "logicalFile": "", "setup": None}
        request.write_text(json.dumps(config), encoding="utf-8")
        proc = subprocess.run([LEAN, "--run", str(ROOT / "LeanExtract.lean"), str(request)], text=True, capture_output=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.output.write_text(self.output.read_text().replace("Nat := 1", "Nat := 2"), encoding="utf-8")
        config.update(mode="verify", input=str(self.output), moduleName="Output", plan=str(plan), result=str(self.directory / "verified.json"))
        request.write_text(json.dumps(config), encoding="utf-8")
        proc = subprocess.run([LEAN, "--run", str(ROOT / "LeanExtract.lean"), str(request)], text=True, capture_output=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("statement dependency changed", proc.stderr)

    def test_lake_project_imports_and_options(self):
        (self.directory / "lakefile.toml").write_text('name = "fixture"\nversion = "0.1.0"\n[leanOptions]\nautoImplicit = false\n[[lean_lib]]\nname = "Fixture"\n', encoding="utf-8")
        (self.directory / "lean-toolchain").write_text("leanprover/lean4:v4.26.0\n", encoding="utf-8")
        (self.directory / "Fixture.lean").write_text("def externalValue : Nat := 11\n", encoding="utf-8")
        self.source.write_text("import Fixture\ndef unused : Nat := 2\ntheorem target : externalValue = 11 := rfl\n", encoding="utf-8")
        proc = subprocess.run([sys.executable, str(CLI), str(self.source), "--theorem", "target", "--output", str(self.output), "--lean", LEAN, "--project", str(self.directory)], text=True, capture_output=True, cwd=self.directory)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        output = self.output.read_text()
        self.assertIn("import Fixture", output)
        self.assertNotIn("def externalValue", output)
        self.assertNotIn("def unused", output)
        lake = str(Path(LEAN).with_name("lake"))
        proc = subprocess.run([lake, "env", LEAN, str(self.output)], text=True, capture_output=True, cwd=self.directory)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        proc = self.run_extract("import Fixture\ntheorem target (x : missingType) : x = x := rfl\n", extra=("--force",), success=False)
        self.assertIn("Unknown identifier", proc.stderr)
        self.assertEqual(self.output.read_text(), output)


if __name__ == "__main__":
    unittest.main()
