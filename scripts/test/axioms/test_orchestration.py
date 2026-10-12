#!/usr/bin/env python3
"""Exercise audit orchestration with a fake Lake; no proof-checker substitutes.

The fixture emits only protocol records. Real Lean validation is a separate
invocation of check-axioms.sh against repository modules.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from scripts.paths import ROOT


RUNNER = r'''#!/usr/bin/env python3
import json, os, pathlib, re, sys
root = pathlib.Path(__file__).resolve().parents[1]
args = sys.argv[1:]
with (root / "calls.jsonl").open("a") as log:
    log.write(json.dumps(args) + "\n")
if "build" in args:
    if os.environ.get("FAIL_BUILD"):
        sys.exit(7)
    executable = root / ".lake/build/bin/fraction_regression"
    executable.parent.mkdir(parents=True, exist_ok=True)
    executable.write_text("#!/bin/sh\nprintf '%s\\n' 'regression passed'\n")
    executable.chmod(0o755)
elif args == ["env", "printenv", "LEAN_PATH"]:
    print(root / ".lake/build/lib/lean")
elif "project-module-data.py" in " ".join(args) and "inputs" in args:
    roots = pathlib.Path(args[-2]).read_text().splitlines()
    names = list(dict.fromkeys(roots + (["Purelib.Support"] if "Purelib.Target" in roots else [])))
    extra = root / "input-imports.json"
    custom_imports = json.loads(extra.read_text()) if extra.exists() else {}
    pending = list(names)
    while pending:
        for dependency in custom_imports.get(pending.pop(), []):
            if dependency not in names:
                names.append(dependency)
                pending.append(dependency)
    records = []
    for name in names:
        base = root / ".lake/build/lib/lean" / name.replace(".", "/")
        main = str(base) + ".olean"
        files = [main, main + ".server", main + ".private"] if name == "Purelib.Support" else [main]
        imports = custom_imports.get(name, ["Purelib.Support"] if name == "Purelib.Target" else [])
        records.append({"name": name, "imports": imports, "files": files})
    pathlib.Path(args[-1]).write_text(json.dumps({"schema": 1, "roots": roots, "modules": records}))
elif "audit-input-keys" in args:
    # Protocol-only fixture; real revision/private/IR checks use compiled fixtures.
    import hashlib
    rows=json.loads(pathlib.Path(args[-2]).read_text())["modules"]
    old=dict(line.split("\t") for line in pathlib.Path(args[-1]).read_text().splitlines())
    all_ir={row["name"]: pathlib.Path(row["files"][0]).with_suffix(".ir") for row in rows}
    def closure(name,seen):
        if name in seen:return b""
        seen.add(name);row=next(r for r in rows if r["name"]==name);p=all_ir[name]
        return name.encode()+ (p.read_bytes() if p.exists() else b"absent")+b"".join(closure(d,seen)for d in row["imports"])
    for row in rows:
        name=row["name"];print(name+"\t"+hashlib.sha256(old[name].encode()+closure(name,set())).hexdigest())
elif "--run" in args:
    print("regression passed")
else:
    if os.environ.get("FAIL_AUDIT"):
        sys.exit(8)
    # Track actual child-process concurrency in this orchestration fixture.
    import atexit, fcntl, time
    activity = root / "worker-activity.json"
    def change_activity(delta):
        with activity.open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            lock.seek(0)
            text = lock.read()
            state = json.loads(text) if text else {"active": 0, "maximum": 0}
            state["active"] += delta
            state["maximum"] = max(state["maximum"], state["active"])
            lock.seek(0); lock.truncate(); lock.write(json.dumps(state)); lock.flush()
    change_activity(1)
    atexit.register(change_activity, -1)
    time.sleep(0.06)
    options = {key: args[args.index(key)+1] for key in ('--project','--assigned','--canonical','--result')}
    modules = pathlib.Path(options['--assigned']).read_text().splitlines()
    boundary = pathlib.Path(options['--project']).read_text()
    source = ''
    declarations_file = root / "declarations.json"
    declarations = json.loads(declarations_file.read_text()) if declarations_file.exists() else {}
    extra = root / "input-imports.json"
    custom_imports = json.loads(extra.read_text()) if extra.exists() else {}
    imported = set(modules) | {"Purelib.Support"}
    pending = list(imported)
    while pending:
        for dependency in custom_imports.get(pending.pop(), []):
            if dependency not in imported:
                imported.add(dependency); pending.append(dependency)
    seen_declarations = {}
    for module in imported:
        for name in declarations.get(module, []):
            if name in seen_declarations:
                print(f"entrypoint collision: {name}", file=sys.stderr)
                sys.exit(9)
            seen_declarations[name] = module
    # Confirm scoped workers still receive the complete provenance boundary.
    assert "Purelib.Other" in boundary and "Purelib.Target" in boundary
    if os.environ.get("FAIL_DISCOVERED_AUDIT") and "Purelib.Logic.AuditFixture" in modules:
        sys.exit(8)
    result = options["--result"]
    records = [f"project\t{module}\t{0 if module == 'Purelib.Empty' else 3}\n" for module in modules]
    if options["--canonical"] == "true":
        records.append("canonical\t@canonical\t5\n")
    if os.environ.get("BAD_RESULTS"):
        records.append("project\tUnsolicited\t1\n")
    pathlib.Path(result).write_text("".join(records))
    pathlib.Path(result + ".closures.jsonl").write_text(
        "".join(json.dumps({"kind": "root", "owner": module, "scanned_module": module, "name": declarations.get(module, [module + ".fixture"])[0],
                            "axioms": [], "canonical": False}) + "\n" for module in modules))
    if "--report-ir-only" in args:
        pathlib.Path(result + ".ir-only.jsonl").write_text(
            "".join(json.dumps({"scanned_module": module, "name": module + ".irFixture",
                                "kernel_ConstantInfo": False}) + "\n" for module in modules))
'''


class AuditScriptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="audit-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "scripts").mkdir()
        for relative in ("check-axioms.sh", "project-modules.py", "paths.py", "__init__.py",
                         "axioms/__init__.py", "axioms/input_keys.py", "axioms/worker_plan.py",
                         "verification/__init__.py", "verification/environments.py",
                         "verification/modules.py"):
            target = self.root / "scripts" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / "scripts" / relative, target)
        runner = self.root / "scripts/run-lake.sh"
        runner.write_text(RUNNER)
        runner.chmod(0o755)
        (self.root / "scripts/project-module-data.py").write_text(
            "import sys\nif sys.argv[1:] == ['audit-support']: print('Purelib.Support')\n"
            "elif sys.argv[1:] == ['regression-root']: print('Test.Data.Rat.Fraction.RegressionMain')\n")
        (self.root / "scripts/lean_module_data").mkdir()
        (self.root / "scripts/lean_module_data/__init__.py").write_text("# Fixture parser identity.\n")
        (self.root / "scripts/lean_module_data/audit.py").write_text("# Original empty axiom policy fixture.\n")
        (self.root / "scripts/lean_module_data/audit_metadata.py").write_text("# Root metadata fixture.\n")
        (self.root / "lean-toolchain").write_text("fixture\n")
        (self.root / "lakefile.toml").write_text("")
        for module in ["Purelib.Target", "Purelib.Other", "Purelib.Empty", "Purelib.Support", "Test.Data.Rat.Fraction.RegressionMain"]:
            source = self.root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- Orchestration fixture, no declarations.\n")
            artifact = self.root / ".lake/build/lib/lean" / module.replace(".", "/")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.with_suffix(".olean.hash").write_text("0123456789abcdef\n")
            artifact.with_suffix(".trace").write_text("dependency revision 1\n")
            artifact.with_suffix(".olean").write_text(f"compiled {module}\n")
            if module == "Purelib.Support":
                Path(str(artifact) + ".olean.server").write_text("server data\n")
                Path(str(artifact) + ".olean.private").write_text("private proof A\n")
        regression = self.root / ".lake/build/bin/fraction_regression"
        regression.parent.mkdir(parents=True, exist_ok=True)
        regression.write_text("#!/bin/sh\necho regression passed\n")
        regression.chmod(0o755)
        (self.root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").mkdir(parents=True)
        self.env = {**os.environ, "AXIOM_AUDIT_JOBS": "1", "AXIOM_AUDIT_CACHE": "1",
                    "AXIOM_AUDIT_CACHE_DIR": str(self.root / "cache")}

    def run_audit(self, *args, success=True, **env):
        # The fixed regression executable is present in every production Lake config.
        config = self.root / 'lakefile.toml'
        if 'root="Test.Data.Rat.Fraction.RegressionMain"' not in config.read_text():
            config.write_text(config.read_text() + '\n[[lean_exe]]\nname="fraction_regression"\n'
                              'root="Test.Data.Rat.Fraction.RegressionMain"\n')
        result = subprocess.run(["bash", "scripts/check-axioms.sh", *args],
                                cwd=self.root, env={**self.env, **env},
                                text=True, capture_output=True)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0)
        return result

    def calls(self):
        log = self.root / "calls.jsonl"
        return [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []

    def test_scope_paths_dedup_and_no_build(self):
        self.run_audit("--no-build", "Purelib.Target", "./Purelib/Target.lean",
                       str(self.root / "Purelib/Target.lean"))
        builds = [c for c in self.calls() if "build" in c]
        self.assertEqual(builds, [["--quiet", "--wfail", "--no-build", "build", "Purelib.Target",
                                  "Test.Data.Rat.Fraction.RegressionMain", "Purelib.Support",
                                  "fraction_regression"]])

    def test_full_and_scoped_cache_preservation(self):
        self.run_audit("--full")
        self.run_audit("Purelib.Target")
        result = self.run_audit()
        self.assertIn("6 hits, 0 checked", result.stdout)
        self.assertIn("full scope, 5 project modules", result.stdout)

    def test_dependency_change_invalidates_only_affected_key(self):
        self.run_audit("--full")
        (self.root / ".lake/build/lib/lean/Purelib/Target.olean").write_text("target revision 2\n")
        result = self.run_audit("Purelib.Target")
        self.assertIn("2 hits, 1 checked", result.stdout)
        (self.root / ".lake/build/lib/lean/Purelib/Support.olean.private").write_text("private proof B\n")
        result = self.run_audit("Purelib.Target")
        self.assertIn("1 hits, 2 checked", result.stdout)

    def test_rejections_do_not_start_lake(self):
        for args in [("--full", "Purelib.Target"), ("Missing",), ("",),
                     ("Purelib.Target[x]",), ("Missing.lean",),
                     ("scripts/ProjectAxiomAudit.lean",), ("--bogus",),
                     ("--report-ir-only", "Purelib.Target")]:
            self.run_audit(*args, success=False)
        self.assertEqual(self.calls(), [])

    def test_failed_currentness_never_runs_worker(self):
        result = self.run_audit("--no-build", "Purelib.Target", success=False, FAIL_BUILD="1")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(len(self.calls()), 1)
        self.assertFalse((self.root / "cache/passes-v1.tsv").exists())

    def test_scoped_run_does_not_read_unrelated_artifacts(self):
        artifact = self.root / ".lake/build/lib/lean/Purelib/Other.olean"
        artifact.unlink()
        self.run_audit("Purelib.Target")
        result = self.run_audit("--full", success=False)
        self.assertIn("cannot resolve compiled module", result.stderr)

    def test_missing_private_artifact_fails_before_cache_hit(self):
        self.run_audit("Purelib.Target")
        (self.root / ".lake/build/lib/lean/Purelib/Support.olean.private").unlink()
        result = self.run_audit("Purelib.Target", success=False)
        self.assertIn("compiled input", result.stderr)

    def test_interpreter_change_invalidates_affected_pass(self):
        path=self.root / ".lake/build/lib/lean/Purelib/Target.ir"
        path.write_text("interpreter A")
        self.run_audit("Purelib.Target")
        self.assertIn("3 hits, 0 checked",self.run_audit("Purelib.Target").stdout)
        path.write_text("interpreter B")
        self.assertIn("2 hits, 1 checked",self.run_audit("Purelib.Target").stdout)
        path.unlink()
        self.assertIn("2 hits, 1 checked",self.run_audit("Purelib.Target").stdout)

    def test_worker_failure_and_bad_results_preserve_cache(self):
        self.run_audit("Purelib.Other")
        cache = self.root / "cache/passes-v1.tsv"
        before = cache.read_bytes()
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")
        self.assertEqual(cache.read_bytes(), before)
        self.run_audit("Purelib.Target", success=False, BAD_RESULTS="1")
        self.assertEqual(cache.read_bytes(), before)

    def test_configured_script_scope_is_explicit_and_rejects_unregistered_scripts(self):
        source = self.root / "scripts/Harness.lean"
        source.write_text("-- Configured mathematical script fixture.\n")
        (self.root / "lakefile.toml").write_text(
            '[[lean_exe]]\nname = "harness"\nroot = "scripts.Harness"\n')
        artifact = self.root / ".lake/build/lib/lean/scripts/Harness"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.with_suffix(".olean.hash").write_text("0123456789abcdef\n")
        artifact.with_suffix(".trace").write_text("script source revision 1\n")
        artifact.with_suffix(".olean").write_text("compiled script fixture\n")
        self.run_audit("scripts.Harness", success=False)
        result = self.run_audit("--configured-scripts", "scripts.Harness")
        self.assertIn("audited 6 project declarations", result.stdout)
        self.run_audit("--configured-scripts", "scripts.Unregistered", success=False)
        source.unlink()
        missing = self.run_audit("--configured-scripts", "--full", success=False)
        self.assertIn("missing configured script sources", missing.stderr)

    def add_fixture_module(self, module, declarations=()):
        source = self.root / (module.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("-- Orchestration declaration fixture.\n")
        artifact = self.root / ".lake/build/lib/lean" / module.replace(".", "/")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.with_suffix(".olean").write_text(f"compiled {module}\n")
        if declarations:
            path = self.root / "declarations.json"
            records = json.loads(path.read_text()) if path.exists() else {}
            records[module] = list(declarations)
            path.write_text(json.dumps(records))

    def test_standalone_same_name_roots_and_transitive_importer_are_separate(self):
        scripts = ["scripts.FirstHarness", "scripts.SecondHarness"]
        for module in scripts + ["Test.Data.Json"]:
            self.add_fixture_module(module, ["main"])
        importer = "Purelib.ImportingHarness"
        self.add_fixture_module(importer)
        (self.root / "input-imports.json").write_text(json.dumps({importer: [scripts[0]]}))
        (self.root / "lakefile.toml").write_text("".join(
            f'[[lean_exe]]\nname = "harness{index}"\nroot = "{module}"\n'
            for index, module in enumerate([*scripts, "Test.Data.Json"])))
        reports = self.root / "standalone-reports"
        result = self.run_audit("--configured-scripts", "--full",
                                AXIOM_AUDIT_JOBS="2", AXIOM_AUDIT_REPORT_DIR=str(reports))
        self.assertIn("9 project modules", result.stdout)
        run = next(reports.glob("run.*"))
        assigned = []
        for file in run.glob("assignments.*.tsv"):
            rows = [line.split("\t") for line in file.read_text().splitlines()]
            assigned.extend(tuple(row) for row in rows)
            projects = [row[1] for row in rows if row[0] == "project"]
            if set(projects) & (set(scripts) | {importer}):
                self.assertEqual(len(projects), 1)
                self.assertNotIn(["canonical", "@canonical"], rows)
        expected = {("project", module) for module in
                    ["Purelib.Target", "Purelib.Other", "Purelib.Empty", "Purelib.Support",
                     *scripts, "Test.Data.Json", importer, "Test.Data.Rat.Fraction.RegressionMain"]} | {("canonical", "@canonical")}
        self.assertEqual(set(assigned), expected)
        self.assertEqual(len(assigned), len(expected))
        roots = [json.loads(line) for file in run.glob("closures.*.jsonl")
                 for line in file.read_text().splitlines()]
        self.assertEqual({(row["owner"], row["name"]) for row in roots if row["name"] == "main"},
                         {(module, "main") for module in scripts + ["Test.Data.Json"]})
        activity = json.loads((self.root / "worker-activity.json").read_text())
        self.assertEqual(activity["active"], 0)
        self.assertGreaterEqual(activity["maximum"], 1)
        self.assertLessEqual(activity["maximum"], 2)
        self.assertTrue((run / "worker-plan.tsv").is_file())
        # Every pass remains cached under its exact scanned source identity.
        (self.root / "worker-activity.json").unlink()
        self.run_audit("--configured-scripts", "--full", AXIOM_AUDIT_JOBS="1")
        self.assertEqual(json.loads((self.root / "worker-activity.json").read_text())["maximum"], 1)
        cached = self.run_audit("--configured-scripts", "--full", AXIOM_AUDIT_JOBS="1")
        self.assertIn("10 hits, 0 checked", cached.stdout)

    def test_complete_reports_scan_cached_modules_and_retain_each_invocation(self):
        self.run_audit("Purelib.Target")
        reports = self.root / "reports"
        first = self.run_audit("Purelib.Target", AXIOM_AUDIT_REPORT_DIR=str(reports))
        self.assertIn("0 hits, 3 checked", first.stdout)
        self.run_audit("Purelib.Target", AXIOM_AUDIT_REPORT_DIR=str(reports))
        runs = list(reports.glob("run.*"))
        self.assertEqual(len(runs), 2)
        for run in runs:
            self.assertTrue((run / "inputs.tsv").exists())
            self.assertTrue((run / "checker.py.txt").exists())
            self.assertTrue((run / "worker.0.json").exists())
            self.assertTrue((run / "assignments.0.tsv").exists())
            row = json.loads((run / "closures.0.jsonl").read_text())
            self.assertEqual(row["owner"], "Purelib.Target")
            self.assertFalse(list(run.glob("ir-only.*.jsonl")))

    def test_ir_only_report_is_optional_and_preserves_cached_passes(self):
        self.run_audit("Purelib.Target")
        cache = self.root / "cache/passes-v1.tsv"
        before = cache.read_bytes()
        reports = self.root / "ir-reports"
        report = self.run_audit("--report-ir-only", "Purelib.Target",
                                AXIOM_AUDIT_REPORT_DIR=str(reports))
        self.assertIn("0 hits, 3 checked", report.stdout)
        self.assertEqual(cache.read_bytes(), before)
        run = next(reports.glob("run.*"))
        rows = [json.loads(line) for file in run.glob("ir-only.*.jsonl")
                for line in file.read_text().splitlines()]
        self.assertEqual(sorted(rows, key=lambda row: row['scanned_module']), [
            {"scanned_module": module, "name": module + ".irFixture", "kernel_ConstantInfo": False}
            for module in ("Purelib.Target", "Test.Data.Rat.Fraction.RegressionMain")])
        worker = json.loads((run / "worker.0.json").read_text())
        self.assertEqual(worker["report_ir_only"], "true")
        self.assertEqual(worker["all_helpers"], "false")
        self.assertIn("3 hits, 0 checked", self.run_audit("Purelib.Target").stdout)

    def test_ir_only_report_does_not_turn_a_failed_audit_into_a_pass(self):
        reports = self.root / "failed-ir-reports"
        self.run_audit("--report-ir-only", "Purelib.Target", success=False,
                       AXIOM_AUDIT_REPORT_DIR=str(reports), FAIL_AUDIT="1")
        self.assertFalse((self.root / "cache/passes-v1.tsv").exists())

    def test_normal_and_all_helpers_passes_are_not_interchangeable(self):
        self.run_audit("Purelib.Target")
        cache = self.root / "cache/passes-v1.tsv"
        normal = cache.read_bytes()
        self.run_audit("--all-helpers", "Purelib.Target", success=False, FAIL_AUDIT="1")
        self.assertEqual(cache.read_bytes(), normal)
        self.assertIn("3 hits, 0 checked", self.run_audit("Purelib.Target").stdout)
        strict = self.run_audit("--all-helpers", "Purelib.Target")
        self.assertIn("0 hits, 3 checked", strict.stdout)
        self.assertNotEqual(cache.read_bytes(), normal)
        self.assertIn("3 hits, 0 checked", self.run_audit("--all-helpers", "Purelib.Target").stdout)
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")
        worker_calls = [call for call in self.calls() if "audit" in call]
        self.assertTrue(any("--all-helpers" in call for call in worker_calls))
        self.assertTrue(any("--all-helpers" not in call for call in worker_calls))

    def test_all_helpers_and_ir_only_reporting_are_independent(self):
        reports = self.root / "strict-ir-reports"
        self.run_audit("--all-helpers", "--report-ir-only", "Purelib.Target",
                       AXIOM_AUDIT_REPORT_DIR=str(reports))
        run = next(reports.glob("run.*"))
        worker = json.loads((run / "worker.0.json").read_text())
        self.assertEqual(worker["all_helpers"], "true")
        self.assertEqual(worker["report_ir_only"], "true")
        self.assertTrue(list(run.glob("ir-only.*.jsonl")))

    def test_discovered_sources_are_active_and_cannot_evade_full_audit(self):
        module = "Purelib.Logic.AuditFixture"
        source = self.root / "Purelib/Logic/AuditFixture.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("module\n-- Ordinary source discovery fixture.\n")
        artifact = self.root / ".lake/build/lib/lean/Purelib/Logic/AuditFixture"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.with_suffix(".olean").write_text("compiled ordinary source fixture\n")
        artifact.with_suffix(".olean.hash").write_text("0123456789abcdef\n")
        artifact.with_suffix(".trace").write_text("Discovered source revision 1\n")
        reports = self.root / "discovery-reports"
        self.run_audit("--full", AXIOM_AUDIT_REPORT_DIR=str(reports))
        builds = [call for call in self.calls() if "build" in call]
        self.assertTrue(any(module in call for call in builds))
        records = [json.loads(line) for file in reports.glob("run.*/closures.*.jsonl")
                   for line in file.read_text().splitlines()]
        self.assertIn(module, {row["owner"] for row in records})
        self.run_audit(module, AXIOM_AUDIT_CACHE="0")
        failed = self.run_audit("--full", success=False, AXIOM_AUDIT_CACHE="0", FAIL_DISCOVERED_AUDIT="1")
        self.assertNotEqual(failed.returncode, 0)
        artifact.with_suffix(".olean").unlink()
        missing = self.run_audit("--no-build", "--full", success=False)
        self.assertIn("cannot resolve compiled module", missing.stderr)

    def test_policy_change_invalidates_old_passes(self):
        self.run_audit("Purelib.Target")
        checker = self.root / "scripts/lean_module_data/audit.py"
        checker.write_text(checker.read_text() + "-- empty axiom policy revision\n")
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")

    def test_planner_revision_invalidates_cached_passes(self):
        self.run_audit("Purelib.Target")
        planner = self.root / "scripts/axioms/worker_plan.py"
        planner.write_text(planner.read_text() + "\n# planner policy revision fixture\n")
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")

    def test_shared_environment_policy_invalidates_cached_passes(self):
        self.run_audit("Purelib.Target")
        helper = self.root / "scripts/verification/environments.py"
        helper.write_text(helper.read_text() + "\n# shared environment policy revision fixture\n")
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")

    def test_previous_policy_cache_cannot_satisfy_current_audit(self):
        checker = self.root / "scripts/check-axioms.sh"
        current = checker.read_text()
        previous = current.replace('ccl-project-axiom-audit-empty-canonical-and-runner-v9',
                                   'ccl-project-axiom-audit-empty-all-kernel-v7')
        self.assertNotEqual(previous, current)
        checker.write_text(previous)
        self.run_audit("Purelib.Target")
        before = (self.root / "cache/passes-v1.tsv").read_bytes()
        checker.write_text(current)
        self.run_audit("Purelib.Target", success=False, FAIL_AUDIT="1")
        self.assertEqual((self.root / "cache/passes-v1.tsv").read_bytes(), before)

    def test_zero_declarations_and_disabled_cache(self):
        self.run_audit("Purelib.Empty", AXIOM_AUDIT_CACHE="0")
        self.assertFalse((self.root / "cache").exists())


if __name__ == "__main__":
    unittest.main()
