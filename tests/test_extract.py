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
        for part in (b"theorem value_eq", b"attribute [simp]"):
            self.assertIn(part, output)
        for part in (b"class HasValue", b"instance : HasValue", b"@[simp] theorem extra"):
            self.assertNotIn(part, output)
        self.assertNotIn(b"theorem unrelated", output)

    def test_used_instance_and_attribute_registration(self):
        output = self.run_extract("""class Value where
  value : Nat
def chosen : Value := \u27e87\u27e9
attribute [instance] chosen
@[simp] theorem irrelevant : 1 + 1 = 2 := rfl
theorem target : Value.value = 7 := rfl
""")
        for part in (b"class Value", b"def chosen", b"attribute [instance]"):
            self.assertIn(part, output)
        self.assertNotIn(b"theorem irrelevant", output)

    def test_resolved_names_do_not_pull_in_matching_suffixes(self):
        output = self.run_extract("""namespace A
def value : Nat := 1
end A
namespace B
def value : Nat := 2
theorem target : value = 2 := rfl
end B
""")
        self.assertNotIn(b"namespace A", output)
        self.assertNotIn(b"Nat := 1", output)
        self.assertIn(b"namespace B", output)
        self.assertIn(b"Nat := 2", output)

    def test_unused_syntax_macros_attributes_and_diagnostics(self):
        output = self.run_extract("""import Lean
def unused : Nat := 42
attribute [simp] unused
macro "unused_term" : term => `(unused)
syntax "finish_here" : tactic
macro_rules | `(tactic| finish_here) => `(tactic| trivial)
#check unused
theorem target : True := by finish_here
#check target
""")
        for part in (b"def unused", b"attribute [simp]", b'"unused_term"', b"#check"):
            self.assertNotIn(part, output)
        self.assertIn(b'syntax "finish_here"', output)
        self.assertIn(b"macro_rules", output)

    def test_only_dependency_scopes_and_their_context_are_kept(self):
        output = self.run_extract("""namespace Unused
variable (n : Nat)
@[simp] theorem irrelevant : n + 0 = n := rfl
end Unused
namespace A.B
section Used
variable (n : Nat)
theorem target : n = n := rfl
end Used
end B
end A
section Later
variable (m : Nat)
#check m
end Later
""")
        for part in (b"Unused", b"irrelevant", b"Later", b"(m : Nat)", b"#check"):
            self.assertNotIn(part, output)
        for part in (b"namespace A.B", b"section Used", b"end Used", b"end B", b"end A"):
            self.assertIn(part, output)

    def test_attribute_removal_can_affect_tactic_control_flow(self):
        output = self.run_extract("""axiom value : Nat
axiom value_eq : value = 3
attribute [simp] value_eq
attribute [-simp] value_eq
theorem target : value = 3 := by
  fail_if_success simp
  exact value_eq
""")
        self.assertIn(b"attribute [-simp] value_eq", output)

    def test_export_alias_is_kept_outside_its_namespace(self):
        output = self.run_extract("""namespace A
def value : Nat := 7
end A
namespace B
export A (value)
end B
theorem target : B.value = 7 := rfl
""")
        self.assertIn(b"export A (value)", output)
        self.assertIn(b"namespace B", output)

    def test_used_custom_elaborator_and_unused_elaborator(self):
        output = self.run_extract("""import Lean
elab "unusedTerm" : term => return Lean.mkNatLit 42
elab "chosenTerm" : term => return Lean.mkNatLit 7
theorem target : chosenTerm = 7 := rfl
""")
        self.assertNotIn(b'"unusedTerm"', output)
        self.assertIn(b'"chosenTerm"', output)

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
        self.assertNotIn(b"structure S", output)
        self.assertNotIn(b"deriving DecidableEq", output)
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

    def test_compact_blank_lines_preserves_proof_comments_and_line_endings(self):
        for newline in (b"\n", b"\r\n"):
            with self.subTest(newline=newline):
                comment = b"/- Outer\n/- Nested --/\n\n\n\nKeep spacing. -/"
                proof = b"theorem target : True := by\n\n\n\n  trivial"
                source = (b"\n\n\n\nimport Lean\n\n\n\n" + comment + b"\n\n\n\n"
                          + b"def unused := 1\n\n \n  \n\n" + proof + b"\n\n\n\n\n")
                output = self.run_extract(source.replace(b"\n", newline), extra=("--force",))
                expected = (b"\n\nimport Lean\n\n\n" + comment + b"\n\n\n" + proof + b"\n\n\n")
                self.assertEqual(output, expected.replace(b"\n", newline))

    def test_simp_execution_trace_with_private_unicode_names_and_crlf(self):
        source = """namespace N
private def \u00ab\u503c\u00bb : Nat := 3
private theorem helper : \u00ab\u503c\u00bb = 3 := rfl
attribute [simp] helper
@[simp] theorem unused : 0 + 0 = 0 := rfl
theorem target : \u00ab\u503c\u00bb = 3 := by simp
end N
""".replace("\n", "\r\n").encode("utf-8")
        output = self.run_extract(source, "N.target")
        self.assertIn(b"private theorem helper", output)
        self.assertIn(b"attribute [simp] helper", output)
        self.assertNotIn(b"theorem unused", output)
        self.assertIn("theorem target : \u00ab\u503c\u00bb = 3 := by simp\r\n".encode(), output)

    def test_used_standalone_deriving_instance(self):
        output = self.run_extract("""structure S where
  value : Nat
deriving instance DecidableEq for S
theorem target (s : S) : decide (s = s) = true := by simp
""")
        self.assertIn(b"structure S", output)
        self.assertIn(b"deriving instance DecidableEq for S", output)

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
        self.check_verifier_rejects_change(
            "def value : Nat := 1\ntheorem target : value = value := rfl\n",
            "Nat := 1", "Nat := 2", "statement dependency changed",
        )

    def test_verifier_rejects_even_equivalent_proof_rewriting(self):
        self.check_verifier_rejects_change(
            "theorem target : True := by trivial\n",
            "by trivial", "True.intro", "changed original source",
        )

    def check_verifier_rejects_change(self, source, old, new, error):
        self.source.write_text(source, encoding="utf-8")
        plan = self.directory / "plan.json"
        request = self.directory / "request.json"
        config = {"mode": "extract", "input": str(self.source), "moduleName": "Input",
                  "theoremName": "target", "result": str(plan), "candidate": str(self.output),
                  "plan": "", "logicalFile": "", "setup": None}
        request.write_text(json.dumps(config), encoding="utf-8")
        proc = subprocess.run([LEAN, "--run", str(ROOT / "LeanExtract.lean"), str(request)], text=True, capture_output=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.output.write_text(self.output.read_text().replace(old, new), encoding="utf-8")
        config.update(mode="verify", input=str(self.output), moduleName="Output", plan=str(plan), result=str(self.directory / "verified.json"))
        request.write_text(json.dumps(config), encoding="utf-8")
        proc = subprocess.run([LEAN, "--run", str(ROOT / "LeanExtract.lean"), str(request)], text=True, capture_output=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn(error, proc.stderr)

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
