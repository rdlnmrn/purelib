#!/usr/bin/env python3
"""Exercise the real axiom verifier across explicit and old-style modules."""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


from scripts.paths import ROOT
FIXTURES = ROOT / "scripts/test/fixtures/module_verification"
LAKE = ROOT / "scripts/run-lake.sh"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class AxiomModuleFixtureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="axiom-module-fixture-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.sources = self.root / "source/ModuleVerification"
        self.objects = self.root / "objects/ModuleVerification"
        self.sources.mkdir(parents=True)
        self.objects.mkdir(parents=True)
        self.base_path = subprocess.check_output(
            [str(LAKE), "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
        self.env = {**os.environ, "LEAN_PATH": f"{self.objects.parent}:{self.base_path}"}
        for name in ("Explicit", "Facade", "Legacy"):
            source = (FIXTURES / f"{name}.lean").read_text()
            source = source.replace("propext Iff.rfl", "rfl")
            (self.sources / f"{name}.lean").write_text(source)
            self.compile(name)

    def run_lean(self, *args, success=True):
        result = subprocess.run([str(LAKE), "env", "env", f"LEAN_PATH={self.env['LEAN_PATH']}",
                                 "lean", *map(str, args)], cwd=ROOT, text=True,
                                capture_output=True)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def compile(self, name):
        self.run_lean("-E", "warning", f"--root={self.sources.parent}", "-o",
                      self.objects / f"{name}.olean", self.sources / f"{name}.lean")

    def audit(self, success=True, *, legacy=True, transitive_only=False):
        result = self.root / "audit-results.tsv"
        modules = ["ModuleVerification.Explicit", "ModuleVerification.Facade"]
        if legacy: modules.append("ModuleVerification.Legacy")
        project = self.root / "project.txt"; assigned = self.root / "assigned.txt"
        project.write_text("\n".join(modules) + "\n")
        assigned.write_text("\n".join(modules) + "\n")
        imports = self.root / "imports.txt"
        imports.write_text("\n".join([modules[-1]] if transitive_only else modules) + "\n")
        # Audit assigned owners through their actual retained direct imports.
        report = subprocess.run([str(LAKE), "env", "env", f"LEAN_PATH={self.env['LEAN_PATH']}",
            "python3", ROOT / "scripts/project-module-data.py", "audit", "--project", project,
            "--assigned", assigned, "--imports", imports, "--canonical", "false", "--result", result],
            cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(report.returncode == 0, success, report.stdout + report.stderr)
        return report, result

    def test_rejects_direct_transitive_and_unused_private_propext(self):
        source = self.sources / "Explicit.lean"
        source.write_text(source.read_text().replace(
            "private theorem privateBridge : True = True := rfl",
            "private theorem privateBridge : True = True := propext Iff.rfl"))
        self.compile("Explicit")
        report, path = self.audit(success=False)
        self.assertIn("privateBridge", report.stdout)
        self.assertIn("publicBridge", report.stdout)
        self.assertIn("propext", report.stdout)
        self.assertFalse(path.exists())
        import json
        rows = [json.loads(line) for line in Path(str(path) + ".closures.jsonl").read_text().splitlines()]
        roots = {row["name"]: row for row in rows if row["kind"] == "root"}
        self.assertEqual(roots["ModuleVerification.publicBridge"]["axioms"], ["propext"])
        dirty = {row["name"]: row for row in rows if row["kind"] == "dirty"}
        private_name = next(name for name in dirty if name.endswith("privateBridge"))
        self.assertIn(private_name, dirty["ModuleVerification.publicBridge"]["dependencies"])
        self.assertEqual(dirty[private_name]["external"], ["propext"])

        source.write_text(source.read_text().replace("propext Iff.rfl", "rfl").replace(
            "private theorem unusedPrivate : True := by exact True.intro",
            "private theorem unusedPrivate : True = True := propext Iff.rfl"))
        self.compile("Explicit")
        report, _ = self.audit(success=False)
        self.assertIn("unusedPrivate", report.stdout)
        self.assertNotIn("publicBridge: [propext]", report.stdout)

    def test_rejects_generated_constructor_equality_and_other_axioms(self):
        source = self.sources / "Explicit.lean"
        original = source.read_text()
        source.write_text(original + "\nprivate structure LocalPair where\n  left : Nat\n  right : Nat\n")
        self.compile("Explicit")
        report, _ = self.audit(success=False)
        self.assertIn("LocalPair.mk.injEq", report.stdout)
        self.assertIn("propext", report.stdout)

        source.write_text(original.replace(
            "private theorem unusedPrivate : True := by exact True.intro",
            "private theorem unusedPrivate : True := Classical.choice ⟨True.intro⟩"))
        self.compile("Explicit")
        report, _ = self.audit(success=False)
        self.assertIn("unusedPrivate", report.stdout)
        self.assertIn("Classical.choice", report.stdout)

    def test_named_source_roots_under_internal_namespace(self):
        source = self.sources / "Explicit.lean"
        source.write_text(source.read_text() + """
private theorem _root_.ModuleVerification._SourceNamespace.unused : True = True :=
  propext Iff.rfl

public theorem _root_.ModuleVerification._SourceNamespace.clean : True := by
  have certificate : True = True := rfl
  exact Eq.mp certificate True.intro
""")
        self.compile("Explicit")
        report, path = self.audit(success=False)
        self.assertIn("_SourceNamespace.unused", report.stdout)
        import json
        rows = [json.loads(line) for line in
                Path(str(path) + ".closures.jsonl").read_text().splitlines()]
        roots = {row["name"]: row for row in rows if row["kind"] == "root"}
        self.assertEqual(roots["ModuleVerification._SourceNamespace.clean"]["axioms"], [])
        unused = next(row for name, row in roots.items()
                      if name.endswith("_SourceNamespace.unused"))
        self.assertEqual(unused["axioms"], ["propext"])
        self.assertEqual(len(roots), 10)

    def keys(self):
        manifest = self.root / "modules.txt"
        inventory = self.root / "inputs.json"
        manifest.write_text("ModuleVerification.Explicit\nModuleVerification.Facade\n"
                            "ModuleVerification.Legacy\n")
        subprocess.run([str(LAKE), 'env', 'env', f"LEAN_PATH={self.env['LEAN_PATH']}",
                        'python3', ROOT / 'scripts/project-module-data.py', 'inputs',
                        manifest, inventory], cwd=ROOT, check=True)
        result = subprocess.run(
            ["python3", "-m", "scripts.axioms.input_keys", "--lean-path",
             self.env["LEAN_PATH"], str(inventory)], cwd=ROOT, text=True,
            capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return dict(line.split("\t") for line in result.stdout.splitlines())

    def test_constructor_api_under_internal_namespace(self):
        source = self.sources / "Explicit.lean"
        source.write_text(source.read_text() + """
private structure _root_.ModuleVerification._SourceNamespace.Pair where
  left : Nat
  right : Nat
""")
        self.compile("Explicit")
        report, _ = self.audit(success=False)
        self.assertIn("_SourceNamespace.Pair.mk.injEq", report.stdout)
        self.assertIn("propext", report.stdout)

    def test_private_roots_missing_part_and_proof_receipt(self):
        explicit, explicit_path = self.audit(legacy=False)
        self.assertIn("audited 7 project declarations", explicit.stdout)
        self.assertEqual(explicit_path.read_text().splitlines(), [
            "project\tModuleVerification.Explicit\t6",
            "project\tModuleVerification.Facade\t1",
        ])
        report, path = self.audit()
        self.assertIn("audited 8 project declarations", report.stdout)
        self.assertEqual(path.read_text().splitlines(), [
            "project\tModuleVerification.Explicit\t6",
            "project\tModuleVerification.Facade\t1",
            "project\tModuleVerification.Legacy\t1",
        ])
        # Only the outer legacy facade is imported: private roots in its
        # explicit grandparent still belong to the complete audit inventory.
        transitive, _ = self.audit(transitive_only=True)
        self.assertIn("audited 8 project declarations", transitive.stdout)

        main = self.objects / "Explicit.olean"
        private = self.objects / "Explicit.olean.private"
        before_main, before_private = digest(main), digest(private)
        before_keys = self.keys()
        source = self.sources / "Explicit.lean"
        old = source.read_text()
        self.assertEqual(old.count("private theorem unusedPrivate : True := by exact True.intro"), 1)
        source.write_text(old.replace(
            "private theorem unusedPrivate : True := by exact True.intro",
            "private theorem unusedPrivate : True := by exact (id True.intro)"))
        self.compile("Explicit")
        self.assertEqual(digest(main), before_main)
        self.assertNotEqual(digest(private), before_private)
        after_keys = self.keys()
        for module in ("Explicit", "Facade", "Legacy"):
            self.assertNotEqual(before_keys[f"ModuleVerification.{module}"],
                                after_keys[f"ModuleVerification.{module}"])
        self.audit()

        # Deliberately invalid temporary fixture: an unused private proof must
        # still be rejected by both workers, despite no public client using it.
        source.write_text(old.replace(
            "private theorem unusedPrivate : True := by exact True.intro",
            "private theorem unusedPrivate : True := by exact "
            "Classical.choice (show Nonempty True from ⟨True.intro⟩)"))
        self.compile("Explicit")
        for legacy in (False, True):
            forbidden, _ = self.audit(success=False, legacy=legacy)
            self.assertIn("unusedPrivate", forbidden.stdout + forbidden.stderr)
            self.assertIn("Classical.choice", forbidden.stdout + forbidden.stderr)
        forbidden, _ = self.audit(success=False, transitive_only=True)
        self.assertIn("unusedPrivate", forbidden.stdout + forbidden.stderr)
        self.assertIn("Classical.choice", forbidden.stdout + forbidden.stderr)

        source.write_text(old)
        self.compile("Explicit")
        private.unlink()
        missing, _ = self.audit(success=False)
        self.assertIn("Explicit.olean.private", missing.stdout + missing.stderr)
        transitive_missing, _ = self.audit(success=False, transitive_only=True)
        self.assertIn("Explicit.olean.private",
                      transitive_missing.stdout + transitive_missing.stderr)
        inventory = self.root / "inputs.json"
        key_result = subprocess.run(
            ["python3", "-m", "scripts.axioms.input_keys", "--lean-path",
             self.env["LEAN_PATH"], str(inventory)], cwd=ROOT, text=True,
            capture_output=True)
        self.assertNotEqual(key_result.returncode, 0)
        self.assertIn("missing compiled input", key_result.stderr)


if __name__ == "__main__":
    unittest.main()
