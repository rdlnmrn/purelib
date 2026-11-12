"""Exercise the detached frontend installer and its actual compiler controls."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts.toolchain import prepare_frontend as installer


class InstallerTests(unittest.TestCase):
    def test_emission_rejects_empty_partial_and_corrupt_checkpoints(self):
        with tempfile.TemporaryDirectory() as directory:
            stem = Path(directory) / 'Module'
            rows = []
            for suffix in installer.PARTS:
                path = Path(str(stem) + suffix)
                path.write_bytes(suffix.encode())
                rows.append(installer.bind(path))
            self.assertFalse(installer.valid_emission([], stem))
            self.assertFalse(installer.valid_emission(rows[:-1], stem))
            self.assertTrue(installer.valid_emission(rows, stem))
            Path(rows[-1]['path']).write_bytes(b'corrupt')
            self.assertFalse(installer.valid_emission(rows, stem))

    def test_overlay_copies_replacements_without_mutating_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base, target = root / 'base', root / 'target'
            owner = base / 'lib/lean/Lean/Meta'
            owner.mkdir(parents=True)
            (owner / 'Changed.olean').write_bytes(b'parent')
            (owner / 'Other.olean').write_bytes(b'unchanged')
            replacement = root / 'replacement'
            replacement.write_bytes(b'candidate')
            installer.overlay(base, target, {
                Path('lib/lean/Lean/Meta/Changed.olean'): replacement,
                Path('lib/lean/Lean/Meta/New.c'): replacement,
            })
            selected = target / 'lib/lean/Lean/Meta/Changed.olean'
            self.assertFalse(selected.is_symlink())
            self.assertEqual(selected.read_bytes(), b'candidate')
            self.assertTrue((target / 'lib/lean/Lean/Meta/Other.olean').is_symlink())
            selected.write_bytes(b'edited')
            self.assertEqual((owner / 'Changed.olean').read_bytes(), b'parent')
            self.assertEqual((target / 'lib/lean/Lean/Meta/New.c').read_bytes(), b'candidate')

    def test_raw_failure_is_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            with self.assertRaisesRegex(RuntimeError, r'failed \(7\)'):
                installer.run([sys.executable, '-c', 'raise SystemExit(7)'], stage,
                              os.environ.copy(), 'rejected')
            self.assertEqual(json.loads((stage / 'rejected.exit.json').read_text()),
                             {'raw_exit_code': 7})

    def test_bootstrap_compiler_timeout_cannot_become_a_successful_emission(self):
        with tempfile.TemporaryDirectory() as directory:
            stage = Path(directory)
            child = ('import signal,sys,time; '
                     'signal.signal(signal.SIGTERM,lambda *_:sys.exit(0)); time.sleep(30)')
            with patch.object(installer, 'MODULE_TIMEOUT', .1), \
                    self.assertRaisesRegex(RuntimeError, r'failed \(124\)'):
                installer.run([sys.executable, '-c', child, 'Fixture.lean'], stage,
                              dict(os.environ), 'overrun')
            result = json.loads((stage / 'process-receipts/overrun.json').read_text())
            self.assertTrue(result['timed_out'])
            self.assertEqual(result['raw_exit_code'], 0)
            self.assertEqual(json.loads((stage / 'overrun.exit.json').read_text()), {'raw_exit_code': 0})


@unittest.skipUnless(os.environ.get('CCL_TEST_CORE_PREFIX'), 'set CCL_TEST_CORE_PREFIX for native integration')
class NativeTests(unittest.TestCase):
    def test_reuse_recovery_and_compiler_controls(self):
        base = Path(os.environ['CCL_TEST_CORE_PREFIX']).resolve()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / 'cache'
            prefix = installer.prepare(base, cache)
            with patch.object(installer, 'run', side_effect=AssertionError('warm rebuild')):
                self.assertEqual(installer.prepare(base, cache), prefix)
            receipt = next(p for p in cache.glob('*.json') if p.stem == prefix.name.split('.')[0])
            receipt.unlink()
            labels = []
            original = installer.run

            def recording(command, stage, env, label):
                labels.append(label)
                return original(command, stage, env, label)

            with patch.object(installer, 'run', side_effect=recording):
                prefix = installer.prepare(base, cache)
            self.assertNotIn('compile-0', labels)
            self.assertNotIn('compile-1', labels)
            env = {**os.environ, 'LEAN_PATH': str(prefix / 'lib/lean'), 'LEAN_NUM_THREADS': '8'}

            def compile_source(name, source):
                path = root / (name + '.lean')
                path.write_text(source)
                return subprocess.run([prefix / 'bin/lean', '-R', root, '-DwarningAsError=true',
                                       '-c', root / (name + '.c'), path],
                                      env=env, text=True, capture_output=True)

            positive = compile_source('SharedProof', '''module
import Lean
public section
namespace FrontendRegression
/-- Reflexivity at an arbitrary finite input. -/
theorem same (n : Nat) : n = n := rfl
/-- Retain the original proof application at a computed input. -/
@[expose] def retained (n : Nat) : { value : Nat // value = value } :=
  ⟨n + 1, same (n + 1)⟩
end FrontendRegression
open Lean in
run_meta do
  if (← getEnv).contains `FrontendRegression.retained._proof_1 then
    throwError "redundant theorem application was abstracted again"
  Meta.withLetDecl `computed (mkConst ``Nat) (mkNatLit 1) fun computed => do
    let proof := mkApp (mkConst ``FrontendRegression.same)
      (mkApp2 (mkConst ``Nat.add) computed (mkNatLit 1))
    unless (← Meta.AbstractNestedProofs.isNonTrivialProof proof) do
      throwError "dependent let scope lost its proof-abstraction boundary"
    let independent := mkApp (mkConst ``FrontendRegression.same)
      (mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 1))
    if ← Meta.AbstractNestedProofs.isNonTrivialProof independent then
      throwError "unrelated local let disabled theorem sharing"
  let first := Expr.forallE `first (mkConst ``Nat) (mkConst ``Nat) .default
  let second := Expr.forallE `second (mkConst ``Nat) (mkConst ``Nat) .implicit
  let converted ← Compiler.LCNF.toLCNFType (mkApp2 (mkConst ``Prod [0, 0]) first second)
  let args := converted.getAppArgs
  unless args.size == 2 do throwError "conversion lost product arguments"
  match args[0]!, args[1]! with
  | .forallE `first _ _ .default, .forallE `second _ _ .implicit => pure ()
  | _, _ => throwError "conversion cache lost binder metadata"
  let borrowed := Expr.forallE `value (markBorrowed (mkConst ``Nat)) (mkConst ``Nat) .default
  let ordinary := Expr.forallE `value (mkConst ``Nat) (mkConst ``Nat) .default
  let converted ← Compiler.LCNF.toLCNFType (mkApp2 (mkConst ``Prod [0, 0]) borrowed ordinary)
  let args := converted.getAppArgs
  unless isMarkedBorrowed args[0]!.bindingDomain! && !isMarkedBorrowed args[1]!.bindingDomain! do
    throwError "conversion cache changed argument ownership annotations"
  let bad : Declaration := .defnDecl {
    name := `FrontendRegression.invalid, levelParams := [], type := mkConst ``Nat,
    value := mkConst ``Bool.true, hints := .opaque, safety := .safe }
  let env ← getEnv
  match env.addDeclCore (Core.getMaxHeartbeats (← getOptions)).toUSize bad none true with
  | .ok _ => throwError "kernel accepted a malformed declaration"
  | .error _ => pure ()
end
''')
            self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
            negative = compile_source('HiddenType', '''module
public section
/-- An intentionally unexposed type body for the rejection control. -/
def Carrier : Type := Nat
/-- This runtime interface requires reduction unavailable in the public scope. -/
def identity (value : Carrier) : Carrier := value
end
''')
            self.assertNotEqual(negative.returncode, 0)
            self.assertIn('Compilation failed', negative.stdout + negative.stderr)


if __name__ == '__main__':
    unittest.main()
