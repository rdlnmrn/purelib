#!/usr/bin/env python3
"""Check trace CLI transport/validation without a Lean compiler or initializer."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import unittest

from scripts.paths import ROOT


class TraceCliTests(unittest.TestCase):
    def test_host_transport_retains_modes_private_names_and_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); scripts = root / 'scripts'; scripts.mkdir()
            shutil.copyfile(ROOT / 'scripts/trace-axiom.sh', scripts / 'trace-axiom.sh')
            runner = scripts / 'run-lake.sh'
            runner.write_text('#!/bin/sh\nset -eu\n[ \"$1\" = env ]; shift\nexec \"$@\"\n')
            runner.chmod(0o755)
            capture = root / 'arguments.json'
            (scripts / 'project-module-data.py').write_text(
                'import json,os,sys\nfrom pathlib import Path\n'
                'Path(os.environ["TRACE_TEST_CAPTURE"]).write_text(json.dumps(sys.argv[1:]))\n')
            env = {**os.environ, 'TRACE_TEST_CAPTURE':str(capture)}
            cases = [(['Example','Example.f'],['trace','--mode','axiom','--target','Quot.sound','Example','Example.f']),
                     (['--use','Example.operation','Example','Example.f','Example.g'],['trace','--mode','use','--target','Example.operation','Example','Example.f','Example.g']),
                     (['--axiom','propext','Example','_private.Example.0.Example.f'],['trace','--mode','axiom','--target','propext','Example','_private.Example.0.Example.f'])]
            for args, expected in cases:
                subprocess.run(['bash',str(scripts/'trace-axiom.sh'),*args],env=env,check=True,capture_output=True)
                self.assertEqual(json.loads(capture.read_text()),expected)
            capture.unlink()
            for args in ([], ['--use'], ['Example'], ['Example','bad;command'], ['bad/module','Example.f']):
                result = subprocess.run(['bash',str(scripts/'trace-axiom.sh'),*args],env=env,capture_output=True)
                self.assertEqual(result.returncode,2)
                self.assertTrue(result.stderr)
                self.assertFalse(capture.exists())
            self.assertFalse(list(root.glob('ccl-axiom-trace.*')))


if __name__ == '__main__':
    unittest.main()
