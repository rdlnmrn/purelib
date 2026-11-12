"""Run the projection shell gate without ripgrep or Lean, including replay failures."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from scripts.paths import ROOT

PROJECTIONS = ("endpoint", "terminalOwner", "stepCount", "parameterEdges",
               "preparedBoxes", "requests", "toClearPath")


class PreparedProjectionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="projection-shell-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(ROOT / "scripts/check-prepared-projections.sh",
                        scripts / "check-prepared-projections.sh")
        tools = self.root / "bin"
        tools.mkdir()
        for name in ("bash", "dirname", "mktemp", "rm", "awk", "grep", "python3"):
            (tools / name).symlink_to(shutil.which(name))
        self.env = dict(os.environ, PATH=str(tools))
        self.assertIsNone(shutil.which("rg", path=self.env["PATH"]))
        self.owner = self.root / ".lake/build/ir/Purelib/Riemann/Branches/PreparedSheetContinuation.c"
        self.owner.parent.mkdir(parents=True)
        self.owner.write_text("".join(
            f"LEAN_EXPORT int _Subdivision_{name}Stored___redArg(int x) {{\nreturn x;\n}}\n"
            for name in PROJECTIONS))
        self.model = self.root / ".lake/build/ir/Purelib/Riemann/Integration/PreparedDirectDyadicRefinementsCore.c"
        self.model.parent.mkdir(parents=True)
        self.model.write_text(
            "LEAN_EXPORT int _CenteredPathChain_dataOfCanonicalSubdivisionStored___redArg(int x) {\n"
            "return x;\n}\n")
        # Replace compilation only. The actual shell script and scanners run unchanged.
        runner = scripts / "run-lake.sh"
        runner.write_text("""#!/usr/bin/env python3
import os
from pathlib import Path
import sys
args = sys.argv[1:]
if args[:2] == ["env", "lean"]:
    output = Path(args[args.index("-c") + 1])
    if output.name == "Projection.c":
        names = ("endpoint", "terminalOwner", "stepCount", "parameterEdges",
                 "preparedBoxes", "requests", "toClearPath")
        text = "".join("_Subdivision_" + name + "Stored___redArg(x);\\n"
                       for name in names if name != os.environ.get("MISSING_PROJECTION"))
    else:
        text = "_CenteredPathChain_dataOfCanonicalSubdivisionStored___redArg(x);\\n"
        if os.environ.get("MISSING_MODEL"):
            text = ""
    if os.environ.get("REPLAY_IN") == output.name:
        text += "_PreparedSheetContinuation_" + os.environ["REPLAY_OPERATION"] + "___(x);\\n"
    output.write_text(text)
""")
        runner.chmod(0o755)

    def run_gate(self, **env):
        return subprocess.run(
            ["bash", "scripts/check-prepared-projections.sh", "--models"],
            cwd=self.root, env=dict(self.env, **env), text=True, capture_output=True)

    def test_models_pass_without_ripgrep(self):
        result = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("All seven public projections", result.stdout)
        self.assertIn("Canonical centered-data projection", result.stdout)

    def test_missing_public_projection_or_model_fails(self):
        for name in PROJECTIONS:
            with self.subTest(projection=name):
                result = self.run_gate(MISSING_PROJECTION=name)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("missing direct stored-data implementation for " + name, result.stderr)
        result = self.run_gate(MISSING_MODEL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("did not select its stored-data implementation", result.stderr)

    def test_consumer_replay_fails_for_each_operation(self):
        for consumer in ("Projection.c", "Model.c"):
            for operation in ("advance", "advanceCached", "prepared", "recentered"):
                with self.subTest(consumer=consumer, operation=operation):
                    result = self.run_gate(REPLAY_IN=consumer, REPLAY_OPERATION=operation)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("replays owner preparation", result.stderr)

    def test_stored_implementation_replay_still_fails(self):
        for owner in (self.owner, self.model):
            with self.subTest(owner=owner.name):
                original = owner.read_text()
                owner.write_text(original.replace("return x;", "_PreparedSheetContinuation_advance___(x);"))
                result = self.run_gate()
                owner.write_text(original)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("replays owner preparation", result.stderr)


if __name__ == "__main__":
    unittest.main()
