#!/usr/bin/env python3
"""Check default source coverage and the configured linters on Core-only fixtures."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path
from types import SimpleNamespace

from scripts.paths import ROOT
from scripts.linting import lake_args as args, providers


class ProviderPreparationTests(unittest.TestCase):
    def test_dependency_order_and_global_settings(self):
        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        expected = config["dynlibs"] + config["plugins"]
        calls = []
        def run(command, **kwargs):
            calls.append((command, kwargs))
            return SimpleNamespace(returncode=0)
        self.assertEqual(providers.prepare("/selected/lake", ["--wfail", "build", "Purelib.Data.Vector.Basic"], run), 0)
        self.assertEqual(calls, [(["/selected/lake", "--wfail", "build", target], {"cwd": ROOT})
                                 for target in expected])

    def test_failure_stops_before_later_providers(self):
        calls = []
        def run(command, **kwargs):
            calls.append(command)
            return SimpleNamespace(returncode=73)
        self.assertEqual(providers.prepare("lake", ["lint", "Purelib.Data.Vector.Basic"], run), 73)
        self.assertEqual(len(calls), 1)

    def test_read_only_and_alternate_commands_do_not_prepare(self):
        for command in (["env", "lean"], ["check-lint"], ["--no-build", "build"],
                        ["--dir", "/tmp/other", "build"], ["--file=other.toml", "lint"],
                        ["lint", "--help"], ["build", "--help"], ["--version"], []):
            with self.subTest(command=command):
                result = providers.prepare("lake", command, lambda *a, **k: self.fail("unexpected provider build"))
                self.assertEqual(result, 0)


class DefaultScopeTests(unittest.TestCase):
    def test_default_lint_and_driver_boundary(self):
        discover = lambda: ["Purelib.A", "scripts.Harness"]
        self.assertEqual(args.expand(["--wfail", "lint"], discover),
                         ["--wfail", "lint", "Purelib.A", "scripts.Harness"])
        self.assertEqual(args.expand(["lint", "--", "driver argument"], discover),
                         ["lint", "Purelib.A", "scripts.Harness", "--", "driver argument"])

    def test_lint_options_and_explicit_scopes(self):
        discover = lambda: ["Purelib.A"]
        self.assertEqual(args.expand(["lint", "--linters", ".style.longLine"], discover),
                         ["lint", "--linters", ".style.longLine", "Purelib.A"])
        for original in (["lint", "Purelib.A"], ["lint", "--help"],
                         ["env", "echo", "lint"], ["--wfail", "build", "Test"],
                         ["--dir", "/tmp/another-workspace", "lint"],
                         ["--file=alternate.toml", "lint"], []):
            self.assertEqual(args.expand(original, lambda: self.fail("unexpected discovery")), original)

    def test_invalid_inventory_fails(self):
        for modules in ([], [""], ["-bad"], ["Purelib..A"], ["bad name"], ["Purelib.A", "Purelib.A"]):
            with self.subTest(modules=modules), self.assertRaises(ValueError):
                args.expand(["lint"], lambda: modules)

    def test_every_declared_target_is_default_and_every_active_source_owned(self):
        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        targets = [row for kind in ("lean_lib", "lean_exe") for row in config.get(kind, [])]
        names = [row["name"] for row in targets]
        self.assertEqual(set(config["defaultTargets"]), set(names))
        self.assertEqual(len(config["defaultTargets"]), len(names))
        globs = []
        for row in targets:
            roots = row.get("roots", []) + ([row["root"]] if "root" in row else [])
            globs.extend(row.get("globs", roots))
        def owns(glob, module):
            if glob.endswith(".+"):
                return module.startswith(glob[:-2] + ".")
            if glob.endswith(".*"):
                return module == glob[:-2] or module.startswith(glob[:-2] + ".")
            return module == glob
        modules = args.project_modules()
        self.assertGreater(len(modules), 1)
        self.assertTrue(any(module.startswith("scripts.") for module in modules))
        self.assertEqual([module for module in modules if not any(owns(g, module) for g in globs)], [])

    def test_native_provider_dependency_order(self):
        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        seen = set()
        for target in config["plugins"]:
            module = target.split("/+", 1)[1].removesuffix(":dynlib")
            source = ROOT / ".lake/packages/mathlib" / (module.replace(".", "/") + ".lean")
            for line in source.read_text().splitlines():
                match = re.match(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(Mathlib\.[\w.]+)", line)
                if match:
                    self.assertIn(match[1], seen, f"native dependency must precede {module}")
            seen.add(module)


class NativeLinterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        cls.options = {row["name"]: row["value"] for row in config["leanOptions"]}
        # Keep dependencies in exactly the Lake-configured order. No source imports
        # of Mathlib or Batteries are added to any of the fixtures.
        cls.plugins = []
        for target in config["plugins"]:
            package, module = target.split("/+", 1)
            module, facet = module.rsplit(":", 1)
            assert package == "mathlib" and facet == "dynlib"
            filename = "mathlib_" + module.replace(".", "_") + ".so"
            path = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean" / filename
            assert path.is_file(), f"build {target} first"
            cls.plugins.append({"path": str(path)})
        cls.dynlibs = [str(ROOT / ".lake/packages/batteries/.lake/build/lib/libbatteries_Batteries.so")]
        cls.temp = tempfile.TemporaryDirectory(prefix="ccl-native-lint-")
        cls.directory = Path(cls.temp.name)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def compile(self, body, name="Probe", *, plugins=True, warning_errors=False, imports="Init"):
        source = self.directory / (name + ".lean")
        source.write_text("module\nimport " + imports + "\npublic section\n" + body)
        setup = self.directory / (name + ".setup.json")
        setup.write_text(json.dumps({"name": name, "package": "purelib", "isModule": True,
                                    "options": self.options, "importArts": {},
                                    "plugins": self.plugins if plugins else [],
                                    "dynlibs": self.dynlibs if plugins else []}))
        olean = self.directory / (name + ".olean")
        command = [str(ROOT / "scripts/run-lake.sh"), "env", "lean", "--setup", str(setup),
                   "-o", str(olean)]
        if warning_errors:
            command += ["-E", "linter.style.longLine"]
        result = subprocess.run(command + [str(source)], cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return result, olean

    def test_clean_core_and_unchanged_import_boundary(self):
        result, olean = self.compile("/-- Compute a tiny exact natural value. -/\ndef clean : Nat := 1\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertNotIn("warning:", result.stdout)
        from scripts.lean_module_data.compact import ModuleParts
        parts = ModuleParts()
        region = parts.add(olean)
        _, imports = parts.projection(region)
        self.assertTrue(imports)
        self.assertTrue(all(not name or name[0] not in {"Mathlib", "Batteries"}
                            for name, _, _ in imports), imports)

    def test_line_length_boundary_and_warning_failure(self):
        for length in (120, 121):
            prefix, suffix = "def padded : Nat := 1 /- ", " -/"
            line = prefix + "x" * (length - len(prefix) - len(suffix)) + suffix
            self.assertEqual(len(line), length)
            result, _ = self.compile("/-- Compute one. -/\n" + line + "\n", "Length" + str(length),
                                     warning_errors=True)
            if length == 120:
                self.assertEqual(result.returncode, 0, result.stdout)
            else:
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("exceeds the 120 character limit", result.stdout)

    def test_selected_diagnostics_without_mathlib_imports(self):
        cases = [
            ("UnusedVariable", "/-- Return one regardless of the argument. -/\ndef unusedArg (argument : Nat) : Nat := 1\n", "linter.unusedVariables"),
            ("UnusedSection", "section\nvariable (argument : Nat)\ninclude argument\n/-- One equals itself. -/\ntheorem retainedArgument : (1 : Nat) = 1 := by rfl\nend\n", "linter.unusedSectionVars"),
            ("MissingDocs", "def undocumented : Nat := 1\n", "missing doc string"),
            ("Whitespace", "/-- Return the input. -/\ndef spacing(x:Nat) : Nat := x\n", "linter.style.whitespace"),
            ("DocString", "/--  Return one. -/\ndef documented : Nat := 1\n", "linter.style.docString"),
            ("EmptyDoc", "/-- -/\ndef emptyDoc : Nat := 1\n", "empty"),
            ("Name", "/-- Return one. -/\ndef bad__name : Nat := 1\n", "contains '__'"),
            ("Namespace", "namespace Repeat.Repeat\n/-- Return one. -/\ndef value : Nat := 1\nend Repeat.Repeat\n", "duplicated"),
            ("DebugOption", "set_option pp.universes true\n/-- Return one. -/\ndef debugOption : Nat := 1\n", "linter.style.setOption"),
            ("NativeDecide", "/-- One equals itself. -/\ntheorem nativeProof : (1 : Nat) = 1 := by native_decide\n", "linter.style.nativeDecide"),
            ("Heartbeat", "set_option maxHeartbeats 1000 in\n/-- Return one. -/\ndef heartbeat : Nat := 1\n", "linter.style.maxHeartbeats"),
            ("UnusedTactic", "/-- One equals itself. -/\ntheorem reflexive : (1 : Nat) = 1 := by\n  skip\n  rfl\n", "linter.unusedTactic"),
            ("Classical", "open Classical\n/-- Return one. -/\ndef classicalOpening : Nat := 1\n", "linter.style.openClassical"),
        ]
        for name, body, expected in cases:
            with self.subTest(name=name):
                result, _ = self.compile(body, name)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertIn(expected, result.stdout)

    def test_core_style_diagnostic_requires_plugin_not_an_import(self):
        body = "/-- Return one. -/\ndef " + "x" * 130 + " : Nat := 1\n"
        without, _ = self.compile(body, "NoPlugin", plugins=False)
        self.assertEqual(without.returncode, 0, without.stdout)
        self.assertNotIn("exceeds", without.stdout)
        with_plugin, _ = self.compile(body, "WithPlugin")
        self.assertIn("exceeds the 120 character limit", with_plugin.stdout)

    def test_constructive_incompatible_rules_disabled(self):
        for option in ("unusedDecidableInType", "unusedFintypeInType"):
            self.assertIs(self.options["weak.linter." + option], False)

    def test_native_checker_agrees_with_original_checker_on_pass_and_failures(self):
        from scripts.linting import runner
        raw = subprocess.check_output([str(ROOT / 'scripts/run-lake.sh'), 'env', 'python3', '-c',
                                       'import os,json; print(json.dumps(dict(os.environ)))'], cwd=ROOT)
        env = json.loads(raw)
        env['LEAN_PATH'] = str(self.directory) + os.pathsep + env['LEAN_PATH']
        env['LEAN_SRC_PATH'] = str(self.directory) + os.pathsep + env['LEAN_SRC_PATH']
        lean = shutil.which('lean', path=env['PATH'])
        lake = shutil.which('lake', path=env['PATH'])
        search = [Path(p).resolve() for p in env['LEAN_PATH'].split(os.pathsep) if p]
        cache = self.directory / 'native-cache'
        cache.mkdir()
        helper = cache / 'RunBuiltinLint.lean'
        helper.write_text(runner.HELPER)
        keys, inputs, _ = runner.bind_inputs([], search, cache)
        tool, tools = runner.tool_identity(lake, lean, env, search, helper, {})
        inputs.update(tools)
        binary = runner.build_native_worker(lean, env, helper, cache, keys[runner.SUPPORT], tool, inputs)
        cases = [
            ('NativeClean', '/-- Compute one. -/\ndef clean : Nat := 1\n', 'Init', 0, 'No environment linters'),
            ('NativeTextFailure', 'def missingDocumentation : Nat := 1\n', 'Init', 1, 'missing doc string'),
            ('NativeEnvFailure', '''
open Lean Lean.Linter.EnvLinter
/-- Enable the regression environment linter. -/
register_builtin_option linter.envLinter.nativeRegression : Bool := {
  defValue := true
  descr := "native lint regression"
}
/-- Report one retained declaration through interpreted meta code. -/
@[builtin_env_linter linter.envLinter.nativeRegression]
meta def regressionLinter : EnvLinter where
  test name := return if name == `badValue then some m!"native environment diagnostic" else none
  noErrorsFound := "clean"
  errorsFound := "regression failure"
/-- Compute the value selected by the regression linter. -/
def badValue : Nat := 1
-- Retain an enabled option snapshot for this declaration in the fixture artifact.
run_elab do
  Lean.modifyEnv fun env =>
    Lean.Linter.envLinterSnapshotExt.insert env ``badValue
      (({} : Lean.NameMap Bool).insert `linter.envLinter.nativeRegression true)
''', 'Init\npublic import Lean.Data.Options\npublic meta import Lean.Linter.EnvLinter.Basic\npublic meta import Lean.Linter.Init\nmeta import Lean.Elab.Term',
             1, 'native environment diagnostic'),
        ]
        for name, body, imports, expected, message in cases:
            with self.subTest(name=name):
                compiled, _ = self.compile(body, name, imports=imports)
                self.assertEqual(compiled.returncode, 0, compiled.stdout)
                original = subprocess.run([lean, '--run', str(helper), name], env=env, cwd=ROOT,
                                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                native = subprocess.run([str(binary), name], env=env, cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                self.assertEqual(original.returncode, expected, original.stdout)
                self.assertEqual(native.returncode, original.returncode, native.stdout)
                self.assertEqual(native.stdout, original.stdout)
                self.assertIn(message, native.stdout)


if __name__ == "__main__":
    unittest.main()
