#!/usr/bin/env python3
"""Real compiled source-root and all-helper coverage regressions.

Finite fixtures distinguish independent root selection from transitive closure
checks. All compilation uses separate outputs.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.paths import ROOT
LAKE=ROOT/'scripts/run-lake.sh'


class HostBackendTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='axiom-backend-fixture-')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.src=self.root/'source/ModuleVerification';self.obj=self.root/'objects/ModuleVerification'
        self.src.mkdir(parents=True);self.obj.mkdir(parents=True)
        base=subprocess.check_output([str(LAKE),'env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip()
        self.env={**os.environ,'LEAN_PATH':str(self.obj.parent)+':'+base}

    def compile(self,text):
        source=self.src/'RootMetadata.lean';source.write_text(text)
        r=subprocess.run([str(LAKE),'env','env','LEAN_PATH='+self.env['LEAN_PATH'],'lean','-E','warning',
             '--root='+str(self.src.parent),'-o',str(self.obj/'RootMetadata.olean'),str(source)],
             cwd=ROOT,text=True,capture_output=True)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)

    def audit(self,report_ir_only=False,success=False,all_helpers=False):
        module='ModuleVerification.RootMetadata';manifest=self.root/'modules.txt';manifest.write_text(module+'\n')
        self.audit_count=getattr(self,'audit_count',0)+1
        result=self.root/('audit-'+str(self.audit_count)+'.tsv')
        args=[str(LAKE),'env','env','LEAN_PATH='+self.env['LEAN_PATH'],'python3',
             str(ROOT/'scripts/project-module-data.py'),'audit','--project',str(manifest),
             '--assigned',str(manifest),'--canonical','false','--result',str(result)]
        if report_ir_only:args.append('--report-ir-only')
        if all_helpers:args.append('--all-helpers')
        r=subprocess.run(args,cwd=ROOT,text=True,capture_output=True)
        self.assertEqual(r.returncode==0,success,r.stdout+r.stderr)
        self.assertEqual(result.exists(),success)
        rows=[json.loads(line)for line in Path(str(result)+'.closures.jsonl').read_text().splitlines()]
        return r,rows,result

    def test_actual_meta_unsafe_registered_rewrite_and_partial_helpers(self):
        self.compile('''module
public import Init
public meta import Lean.Compiler.CSimpAttr
public section
namespace ModuleVerification
/-- Retained original finite operation. -/
def sourceValue : Nat := 1
/-- Definitionally equal replacement. -/
def targetValue : Nat := 1
/-- Deliberately dirty registered rewrite retained in the actual imported registry. -/
@[csimp] theorem replacementCertificate : sourceValue = targetValue :=
  Eq.mp (propext Iff.rfl) rfl
/-- An unreferenced meta declaration must still be audited. -/
meta def metaValue : Nat := 2
/-- An unreferenced unsafe declaration must still be audited. -/
unsafe def unsafeValue : Nat := 3
/-- Partial implementations must retain their separate unsafe recursors. -/
partial def recursiveValue (n : Nat) : Nat :=
  if n == 0 then 0 else recursiveValue (n-1)
end ModuleVerification
''')
        _,rows,result=self.audit();roots={r['name']:r for r in rows if r['kind']=='root'}
        self.assertEqual(roots['ModuleVerification.replacementCertificate']['axioms'],['propext'])
        self.assertNotIn('ModuleVerification.metaValue',roots)
        self.assertNotIn('ModuleVerification.unsafeValue',roots)
        self.assertFalse(any('_unsafe_rec' in n for n in roots))
        _,strict_rows,_=self.audit(all_helpers=True)
        strict={r['name']:r for r in strict_rows if r['kind']=='root'}
        self.assertIn('ModuleVerification.metaValue',strict)
        self.assertIn('ModuleVerification.unsafeValue',strict)
        self.assertTrue(any('_unsafe_rec' in n for n in strict))
        self.assertEqual(strict['ModuleVerification.replacementCertificate']['axioms'],['propext'])
        self.assertFalse(Path(str(result)+'.ir-only.jsonl').exists())
        for row in roots.values():self.assertEqual(row['scanned_module'],'ModuleVerification.RootMetadata')
        _,diagnostic_rows,diagnostic_result=self.audit(report_ir_only=True)
        self.assertEqual(rows,diagnostic_rows)
        inventory=Path(str(diagnostic_result)+'.ir-only.jsonl')
        self.assertTrue(inventory.is_file())
        for line in inventory.read_text().splitlines():
            self.assertIs(json.loads(line)['kernel_ConstantInfo'],False)

    def test_unreferenced_dirty_meta_helper_requires_all_helpers(self):
        self.compile('''module
public import Init
namespace ModuleVerification
/-- A clean client that does not use the dirty helper. -/
public def cleanValue : Nat := 1
/-- Deliberately dirty private meta proof outside the old source-root policy. -/
private meta def dirtyMeta : (0 : Nat) = 0 :=
  Eq.mp (propext Iff.rfl) rfl
end ModuleVerification
''')
        _,normal,_=self.audit(success=True)
        self.assertFalse(any(row['name'].endswith('.ModuleVerification.dirtyMeta')for row in normal))
        _,rows,_=self.audit(all_helpers=True)
        roots=[row for row in rows if row['kind']=='root']
        dirty=[row for row in roots if row['name'].endswith('.ModuleVerification.dirtyMeta')]
        self.assertEqual(len(dirty),1)
        self.assertEqual(dirty[0]['axioms'],['propext'])
        clean=next(row for row in roots if row['name']=='ModuleVerification.cleanValue')
        self.assertEqual(clean['axioms'],[])

    def test_generated_equation_is_excluded_only_as_an_independent_root(self):
        fixture = """module
public import Init
public section
namespace ModuleVerification
/-- An ordinary finite operation. -/
def operation : Nat := 0
/-- A deliberately dirty generated-style equation. -/
theorem generatedEquation.eq_def : operation = 0 := Eq.mp (propext Iff.rfl) rfl
"""
        self.compile(fixture + "end ModuleVerification\n")
        _,normal,_=self.audit(success=True)
        self.assertFalse(any(row['name']=='ModuleVerification.generatedEquation.eq_def'for row in normal))
        _,strict,_=self.audit(all_helpers=True)
        equation=next(row for row in strict if row.get('name')=='ModuleVerification.generatedEquation.eq_def')
        self.assertEqual(equation['axioms'],['propext'])
        self.compile(fixture + """/-- An ordinary client retains the exact equation proof. -/
theorem consumer : operation = 0 := generatedEquation.eq_def
end ModuleVerification
""")
        _,normal,_=self.audit()
        roots={row['name']:row for row in normal if row['kind']=='root'}
        self.assertNotIn('ModuleVerification.generatedEquation.eq_def',roots)
        self.assertEqual(roots['ModuleVerification.consumer']['axioms'],['propext'])
        dirty=next(row for row in normal if row['kind']=='dirty'and row['name']=='ModuleVerification.consumer')
        self.assertIn('ModuleVerification.generatedEquation.eq_def',dirty['dependencies'])

    def test_canonical_cohort_always_checks_excluded_meta_roots(self):
        self.compile("""module
public import Init
/-- A canonical-only dirty meta helper. -/
private meta def ModuleVerification.dirtyMeta : (0 : Nat) = 0 := Eq.mp (propext Iff.rfl) rfl
""")
        self.audit(success=True)
        import sys
        from unittest.mock import patch
        from scripts.lean_module_data.audit import audit
        search=[Path(p)for p in self.env['LEAN_PATH'].split(os.pathsep)]
        module='ModuleVerification.RootMetadata'
        result=self.root/'canonical.tsv'
        with patch('scripts.lean_module_data.audit.CANONICAL',(module,)):
            with self.assertRaisesRegex(ValueError,'unexpected project axiom closures'):
                audit([module],[module],True,result,search)
        roots=[json.loads(line)for line in Path(str(result)+'.closures.jsonl').read_text().splitlines()]
        dirty=next(row for row in roots if row['kind']=='root'and row['name'].endswith('.ModuleVerification.dirtyMeta'))
        self.assertTrue(dirty['canonical'])
        self.assertEqual(dirty['axioms'],['propext'])
        self.assertFalse(result.exists())

    def test_clean_default_audit_passes_without_ir_only_output(self):
        self.compile('module\npublic def ModuleVerification.value : Nat := 7\n')
        _,rows,result=self.audit(success=True)
        self.assertFalse(Path(str(result)+'.ir-only.jsonl').exists())
        _,diagnostic_rows,diagnostic_result=self.audit(report_ir_only=True,success=True)
        self.assertEqual(rows,diagnostic_rows)
        self.assertTrue(Path(str(diagnostic_result)+'.ir-only.jsonl').exists())

    def test_consumed_interpreter_identity_and_missing_part(self):
        self.compile('module\npublic def ModuleVerification.value : Nat := 7\n')
        import sys
        from scripts.lean_module_data.audit import input_keys
        from scripts.lean_module_data.compact import inventory
        from scripts.lean_module_data.paths import search_path
        saved=os.environ.get('LEAN_PATH');os.environ['LEAN_PATH']=self.env['LEAN_PATH']
        try:
            search=search_path();records,_=inventory(['ModuleVerification.RootMetadata'],search)
            path=self.root/'inputs.json';path.write_text(json.dumps(records))
            metadata=self.root/'metadata.tsv'
            result=subprocess.run(['python3','-m','scripts.axioms.input_keys',
                 '--lean-path',self.env['LEAN_PATH'],str(path)],text=True,capture_output=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr);metadata.write_text(result.stdout)
            original=input_keys(path,metadata,search)
            ir=self.obj/'RootMetadata.ir';raw=ir.read_bytes();ir.unlink()
            with self.assertRaisesRegex(ValueError,'missing compiled interpreter input'):
                input_keys(path,metadata,search)
            ir.write_bytes(raw);self.assertEqual(input_keys(path,metadata,search),original)
            changed=bytearray(raw);changed[40]^=1;ir.write_bytes(changed)
            with self.assertRaisesRegex(ValueError,'compiler revision mismatch'):
                input_keys(path,metadata,search)
        finally:
            if saved is None:os.environ.pop('LEAN_PATH',None)
            else:os.environ['LEAN_PATH']=saved

    def test_unsupported_compiler_revision_fails_before_any_pass(self):
        self.compile('module\npublic theorem ModuleVerification.clean : True := True.intro\n')
        main=self.obj/'RootMetadata.olean';raw=bytearray(main.read_bytes());raw[40]^=1;main.write_bytes(raw)
        manifest=self.root/'modules.txt';manifest.write_text('ModuleVerification.RootMetadata\n');result=self.root/'invalid.tsv'
        r=subprocess.run([str(LAKE),'env','env','LEAN_PATH='+self.env['LEAN_PATH'],'python3',
             str(ROOT/'scripts/project-module-data.py'),'audit','--project',str(manifest),
             '--assigned',str(manifest),'--canonical','false','--result',str(result)],
             cwd=ROOT,text=True,capture_output=True)
        self.assertNotEqual(r.returncode,0)
        self.assertIn('compiler revision mismatch',r.stdout)
        self.assertFalse(result.exists())


if __name__=='__main__':unittest.main()
