#!/usr/bin/env python3
"""Exercise profiling dispatch, cold preservation and checked compiler replays."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts.profiling.build_costs import Probes, compiler_command, import_header, stop_owned, timings

from scripts.profiling import build as driver


class DispatchTests(unittest.TestCase):
    def test_wrapper_flags_preserve_scope_and_values(self):
        args = ["--profile", "--wfail", "-K", "--cold", "build", "Purelib.A", "--cold"]
        self.assertEqual(driver.flags(args), (["--wfail", "-K", "--cold", "build", "Purelib.A"], True, True))
        self.assertEqual(driver.flags(["build", "--", "--profile", "--cold"]),
                         (["build", "--", "--profile", "--cold"], False, False))
        self.assertEqual(driver.flags(["env", "lean", "--profile"]),
                         (["env", "lean", "--profile"], False, False))

    def test_unsupported_contexts_are_rejected_before_cold_mutation(self):
        for args in (["env", "lean"], ["--dir=/tmp/other", "build"], ["--file", "other", "build"],
                     ["--no-build", "build"], ["build", "--help"]):
            with self.subTest(args=args):
                self.assertFalse(driver.is_project_build(args))
                with self.assertRaises(ValueError):
                    driver.execute(args, True, True)

    def test_timings_do_not_invent_cached_results(self):
        log = "✔ [1/3] Built Purelib.A (750ms)\n✔ [2/3] Built Purelib.B (5.0s)\n"
        self.assertEqual(timings(log, ["Purelib.A", "Purelib.B", "Purelib.C"]),
                         {"Purelib.A": .75, "Purelib.B": 5})
        with self.assertRaises(ValueError):
            timings(log + log, ["Purelib.A"])
        with self.assertRaises(ValueError):
            timings(log, [])

    def test_header_preserves_phase_and_order(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "Source.lean"
            header = "module\n/- preamble -/\npublic import Init\nmeta import all Lean.Meta.FunInfo\n"
            p.write_text(header + "\nnamespace Owner\nend Owner\n")
            self.assertEqual(import_header(p), header)

    def test_concurrent_writer_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(driver, "ROOT", Path(directory)):
            before = Path.cwd()
            try:
                os.chdir(directory)
                lock = driver.writer_lock(["build"])
                try:
                    with self.assertRaisesRegex(ValueError, "another repository build"):
                        driver.writer_lock(["build"])
                finally:
                    lock.close()
            finally:
                os.chdir(before)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.module = "Purelib.A"
        source = self.root / "Purelib/A.lean"
        source.parent.mkdir()
        source.write_text("module\nimport Init\n")
        self.fake = self.root / "toolchain/bin/lean"
        self.fake.parent.mkdir(parents=True)
        self.fake.write_text("""#!/usr/bin/env python3
import json, pathlib, sys
args=sys.argv[1:]
root=pathlib.Path(__file__).resolve().parents[2]
with (root/'calls').open('a') as stream: stream.write(json.dumps(args)+'\\n')
if '-Dtrace.profiler=true' in args: print('[Kernel] [0.123] test kernel frame')
for option,suffix in [('-o','.olean'),('-i','.ilean'),('-c','.c')]:
 if option in args:
  p=pathlib.Path(args[args.index(option)+1]);p.write_text('emitted '+suffix)
  if suffix=='.olean':
   for extra in ['.olean.private','.olean.server','.ir']:p.with_suffix(extra).write_text('emitted '+extra)
""")
        self.fake.chmod(0o755)
        artifacts = self.root / "imports"
        artifacts.mkdir()
        for suffix in (".olean", ".olean.private", ".olean.server", ".ir"):
            (artifacts / ("Init" + suffix)).write_text("import bytes" + suffix)
        plugin = self.root / "plugin.so"
        plugin.write_text("plugin")
        self.setup = self.root / "setup.json"
        self.setup.write_text(json.dumps({"importArts": {"Init": [str(artifacts / "Init.olean")]},
                                          "plugins": [{"path": str(plugin)}], "dynlibs": []}))
        self.command = [str(self.fake), str(source), "-o", str(self.root / "Lake.olean"),
                        "-i", str(self.root / "Lake.ilean"), "-c", str(self.root / "Lake.c"),
                        "--setup", str(self.setup), "--json"]
        trace = self.root / ".lake/build/lib/lean/Purelib/A.trace"
        trace.parent.mkdir(parents=True)
        trace.write_text(json.dumps({"log": [{"message": ".> " + shlex.join(self.command)}]}))
        self.probes = Probes(self.root, self.root / "cache", 8)

    def tearDown(self):
        self.temporary.cleanup()

    def test_complete_replay_reuse_and_private_artifact_invalidation(self):
        result = self.probes.module(self.module)
        self.assertTrue(result["valid_quiet_runs"])
        self.assertEqual(result["runs"]["profile"]["frames"][0]["kind"], "Kernel")
        calls = (self.root / "calls").read_text().splitlines()
        self.assertEqual(len(calls), 4)
        self.assertIn(str(self.setup), json.loads(calls[0]))
        self.assertFalse((self.root / "Lake.olean").exists())
        again = self.probes.module(self.module)
        self.assertTrue(all(row["reused"] for row in again["runs"].values()))
        self.assertEqual(len((self.root / "calls").read_text().splitlines()), 4)
        (self.root / "imports/Init.olean.private").write_text("changed private bytes")
        changed = self.probes.module(self.module)
        self.assertFalse(changed["runs"]["full"]["reused"])
        self.assertEqual(len((self.root / "calls").read_text().splitlines()), 8)

    def test_standalone_replays_make_warnings_fatal(self):
        result = self.probes.run(self.module, "full")
        self.assertIn("-DwarningAsError=true", result["inputs"]["command"])
        command = json.loads((Path(result["receipt"]).parent / "command.json").read_text())
        self.assertIn("-DwarningAsError=true", command)

    def test_corrupt_checkpoint_is_rejected(self):
        result = self.probes.run(self.module, "full")
        (Path(result["receipt"]).parent / "Module.ir").write_text("corrupt")
        with self.assertRaisesRegex(ValueError, "corrupt diagnostic checkpoint"):
            self.probes.run(self.module, "full")

    def test_failed_profiler_is_kept_separate_from_quiet_success(self):
        self.fake.write_text(self.fake.read_text().replace(
            "if '-Dtrace.profiler=true' in args: print('[Kernel] [0.123] test kernel frame')",
            "if '-Dtrace.profiler=true' in args: sys.exit(9)"))
        result = self.probes.module(self.module)
        self.assertTrue(result["valid_quiet_runs"])
        self.assertEqual(result["runs"]["profile"]["exit_code"], 9)
        self.assertTrue(Path(result["runs"]["profile"]["receipt"]).name == "failure.json")

    def test_interrupted_run_reuses_completed_modes(self):
        self.probes.run(self.module, "full")
        with patch.object(self.probes, "run", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.probes.selected([self.module], 1)
        resumed = Probes(self.root, self.root / "cache", 8)
        result = resumed.module(self.module)
        self.assertTrue(result["runs"]["full"]["reused"])
        self.assertEqual(len((self.root / "calls").read_text().splitlines()), 4)


class ColdTests(unittest.TestCase):
    def test_scoped_cold_build_preserves_old_bytes_and_does_not_claim_full_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            (root / "scripts/run-lake.sh").write_text(
                "#!/bin/sh\nmkdir -p .lake/build\necho fresh > .lake/build/new\n"
                "echo '✔ [1/1] Built Purelib.A (1.0s)'\n")
            (root / "scripts/run-lake.sh").chmod(0o755)
            old = root / ".lake/build"
            old.mkdir(parents=True)
            (old / "old").write_bytes(b"preserved")
            before = Path.cwd()
            try:
                os.chdir(root)
                with patch.object(driver, "ROOT", root), patch.object(driver, "inventory", return_value=["Purelib.A", "Purelib.B"]), \
                     patch.object(driver, "source_hashes", return_value={"Purelib.A": "a", "Purelib.B": "b"}), \
                     patch.object(driver.subprocess, "check_output", return_value="revision\n"), \
                     contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(driver.execute(["build", "Purelib.A"], False, True), 0)
                report = next((root / ".lake/build-profiles").iterdir())
                self.assertEqual((report / "preserved-build/old").read_bytes(), b"preserved")
                self.assertTrue((root / ".lake/build/new").exists())
                summary = json.loads((report / "summary.json").read_text())
                self.assertEqual(summary["unmeasured_modules"], ["Purelib.B"])
            finally:
                os.chdir(before)

    def test_owned_process_group_can_be_stopped(self):
        process = subprocess.Popen(["sleep", "60"], start_new_session=True)
        try:
            stop_owned(process)
            self.assertIsNotNone(process.poll())
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()


if __name__ == "__main__":
    unittest.main()
