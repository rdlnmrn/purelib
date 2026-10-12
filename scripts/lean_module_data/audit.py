"""Authoritative project and strict canonical axiom audits on pinned compiled metadata.

This is the backend dispatched by check-axioms.sh, with the original empty axiom
policy, ordered roots, private inventory validation and complete dirty records.
IR-only code can be inventoried separately for diagnosis; it is not kernel-audited.
"""
from functools import cmp_to_key
from pathlib import Path
from .importer import Graph
from .observations import Observations,name_observer,query_observer,name_cmp,name_hash
from .paths import parse_name,render_name
from .contracts import dumps
from .audit_metadata import RootMetadata,audit_root
from .typed import InvalidArtifact

CANONICAL = (
 'Purelib.Data.Fin',
 'Purelib.Data.Nat.GCD.Coprime',
 'Purelib.Data.Nat.GCD.Extended',
 'Purelib.Data.Nat.GCD.Scalar',
 'Purelib.Data.Nat.LCM',
 'Purelib.Data.Rat.Fraction.Basic',
 'Purelib.Data.Rat.Fraction.Construction',
 'Purelib.Data.Rat.Fraction.Arithmetic',
 'Purelib.Data.Rat.Fraction.Order',
 'Purelib.Data.Rat.Fraction.Field',
 'Purelib.Data.Rat.Fraction',
 'Test.Data.Rat.Fraction.Regression',
 'Purelib.Data.Rat.Fraction.Compatibility',
 'Purelib.Data.Gaussian.Basic',
 'Test.Data.Gaussian.Regression',
 'Purelib.Polynomial.Dense.Gaussian.Basic',
 'Test.Polynomial.Dense.Gaussian.Regression',
 'Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator',
 'Test.Polynomial.Evaluation.Gaussian.NewtonResidual',
 'Purelib.Data.Gaussian.Constants',
 'Purelib.Data.Gaussian.Field',
 'Purelib.Data.Gaussian.Norm.Basic',
 'Purelib.Data.Gaussian.Resource',
 'Purelib.Data.Int.Order',
 'Purelib.Data.Int.ToNat',
 'Purelib.Data.Nat.Coprime.Basic',
 'Purelib.Data.Nat.GCD.Resource.Clauses',
 'Purelib.Data.Nat.GCD.Resource.Fuel',
 'Purelib.Data.Rat.Fraction.Cast',
 'Purelib.Data.Rat.Fraction.Cast.Order',
 'Purelib.Data.Rat.Fraction.Decide',
 'Purelib.Data.Rat.Fraction.Order.Arithmetic',
 'Purelib.Data.Rat.Fraction.Order.Basic',
 'Purelib.Data.Rat.Fraction.Order.Field',
 'Purelib.Data.Rat.Fraction.Order.Square',
 'Purelib.Data.Rat.Fraction.Resource.Clauses',
 'Purelib.Data.Rat.Fraction.Resource.Components',
 'Purelib.Data.Rat.Fraction.Resource.Fuel',
 'Purelib.Data.Rat.Fraction.Square',
 'Purelib.Data.Rat.Rounding.Floor',
 'Purelib.Data.Rat.SignedFraction.Arithmetic',
 'Purelib.Data.Rat.SignedFraction.Basic',
 'Purelib.Data.Rat.SignedFraction.Normalization',
 'Purelib.Data.Rat.SignedFraction.Order',
 'Purelib.Data.Rat.SignedFraction.Resource',
 'Purelib.NumberTheory.SquareClass.Rational.Nonsquare',
 'Purelib.Polynomial.Dense.Gaussian.Arithmetic',
 'Purelib.Polynomial.Dense.Gaussian.Derivative',
 'Purelib.Polynomial.Dense.Gaussian.Evaluation',
 'Purelib.Polynomial.Dense.Gaussian.Multiplication',
 'Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual',
)
# Original template import order determines imported first-owner provenance.
SUPPORT = ('Purelib.Data.Gaussian.Basic','Purelib.Data.Nat.GCD.Coprime',
 'Purelib.Data.Nat.GCD.Extended','Purelib.Data.Nat.GCD.Scalar',
 'Purelib.Data.Rat.Fraction.Basic','Purelib.Data.Rat.Fraction.Construction',
 'Purelib.Data.Rat.Fraction.Arithmetic','Purelib.Data.Rat.Fraction.Order',
 'Purelib.Data.Rat.Fraction.Field','Purelib.Data.Rat.Fraction',
 'Purelib.Polynomial.Dense.Gaussian.Basic',
 'Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator',
 'Lean.Util.CollectAxioms','Lean.Util.FoldConsts','Lean.Elab.Command','Lean.Compiler.MetaAttr',
 'Lean.Compiler.CSimpAttr','Lean.DeclarationRange','Purelib.Data.Fin',
 'Test.Data.Rat.Fraction.Regression','Purelib.Data.Rat.Fraction.Compatibility',
 'Purelib.Data.Nat.LCM','Test.Data.Gaussian.Regression','Test.Polynomial.Dense.Gaussian.Regression',
 'Test.Polynomial.Evaluation.Gaussian.NewtonResidual')
# Preserve the original first-owner import order and extend it from the single strict inventory.
SUPPORT = tuple(dict.fromkeys((*SUPPORT, *CANONICAL)))
REGRESSION_MODULE = 'Test.Data.Rat.Fraction.RegressionMain'



class AuditObservation(Observations):
    """One original worker import environment, including all transitive private parts."""
    def __init__(self, roots, search):
        self.graph=Graph(search)
        self.constants,self.order,self.state=self.graph.maps(roots,True)
        self.by_name={};self.names={};self.owners={};self.axiom_tables={}
        for key,ref in self.constants.items():
            name=name_observer(ref.d,ref.name);self.by_name[name]=ref;self.names[key]=name
        for key,owner in self.graph.owners.items():self.owners[self.graph.owner_names[key]]=owner
    @staticmethod
    def text(name):return render_name(name[1])
    @staticmethod
    def query_parts(parts):return name_hash(parts),parts
    def inventory(self,module):
        mod=self.state[module]['module']
        if mod is None:raise InvalidArtifact('axiom audit has no module data for: '+module)
        rows=mod.entries(True);names=[]
        for _,ref,idx in rows:
            name=name_observer(mod.d,idx)
            if name not in self.by_name:raise InvalidArtifact('axiom audit cannot load kernel declaration '+self.text(name)+' from '+module)
            names.append(name)
        extra=[]
        for p in mod.d.parts.array(mod.data(True)[3]):extra.append(name_observer(mod.d,mod.d.decode('Name',p)))
        return names+extra, [n for n in extra if n not in self.by_name]


def audit(project, assigned, canonical, result, search, report_ir_only=False, imports=None,
          all_helpers=False):
    """Audit source roots or all helpers, always with complete transitive closures."""
    project_set=set(project);assigned_set=set(assigned)
    outside=[m for m in assigned if m not in project_set]
    if outside:raise InvalidArtifact('project axiom audit received non-project modules: '+repr(outside))
    obs=AuditObservation([*(assigned if imports is None else imports),*SUPPORT],search)
    for m in CANONICAL:
        if m not in obs.state:raise InvalidArtifact('canonical audit did not import required owner: '+m)
    missing=[m for m in assigned if m not in obs.state]
    if missing:raise InvalidArtifact('project axiom audit did not import: '+repr(missing))
    metadata=RootMetadata(obs);modules=list(assigned)
    if canonical:modules.extend(m for m in CANONICAL if m not in assigned_set)
    records=[];resultlines=[];failures=[];traversal=[];checked=0;canonical_checked=0;ir=[]
    for module in modules:
        audit_project=module in assigned_set;audit_canonical=canonical and module in CANONICAL
        names,ir_only=obs.inventory(module)
        if report_ir_only:
            ir.extend({'scanned_module':module,'name':obs.text(n),'kernel_ConstantInfo':False}for n in ir_only)
        module_checked=0
        for name in names:
            ref=obs.by_name.get(name)
            if ref is None:continue
            root=all_helpers or audit_root(name,ref,metadata)
            if audit_canonical or audit_project and root:
                axioms=obs.axioms(name)
                if audit_project and root:checked+=1;module_checked+=1
                if audit_canonical:canonical_checked+=1
                row={'kind':'root','owner':obs.owners.get(name),'scanned_module':module,
                     'name':obs.text(name),'canonical':audit_canonical,'axioms':[obs.text(n)for n in axioms]}
                row['all_helpers']=all_helpers and audit_project
                records.append(row)
                if axioms:failures.append((module,name,axioms));traversal.append(name)
        if audit_project:resultlines.append('project\t'+module+'\t'+str(module_checked))
    visited=set();index=0
    while index<len(traversal):
        current=traversal[index];index+=1
        if current in visited:continue
        visited.add(current);ref=obs.by_name.get(current)
        if ref is None:continue
        dirty=[]
        for dependency in sorted(obs.used(ref),key=cmp_to_key(name_cmp)):
            if obs.axioms(dependency):
                dirty.append(dependency)
                if obs.owners.get(dependency)in project_set:traversal.append(dependency)
        records.append({'kind':'dirty','name':obs.text(current),'owner':obs.owners.get(current),
                        'dependencies':[obs.text(n)for n in dirty],
                        'external':[obs.text(n)for n in dirty if obs.owners.get(n)not in project_set]})
    Path(str(result)+'.closures.jsonl').write_text(''.join(dumps(r)+'\n'for r in records))
    if report_ir_only:Path(str(result)+'.ir-only.jsonl').write_text(''.join(dumps(r)+'\n'for r in ir))
    if failures:
        message='unexpected project axiom closures: '+str(len(failures))+' declarations'
        for module,name,axioms in sorted(failures,key=cmp_to_key(lambda a,b:name_cmp(a[1],b[1])))[:30]:
            message+='\n  '+module+': '+obs.text(name)+': ['+', '.join(obs.text(n)for n in axioms)+']'
        message+='\ncomplete roots and dirty dependency edges: '+str(result)+'.closures.jsonl'
        raise InvalidArtifact(message)
    if canonical:resultlines.append('canonical\t@canonical\t'+str(canonical_checked))
    Path(result).write_text('\n'.join(resultlines)+'\n')
    return 'audited '+str(checked)+' project declarations from '+str(len(assigned))+' assigned modules and '+str(canonical_checked)+' strict canonical declarations; allowed axioms: []'


def input_keys(inventory_path, metadata_keys_path, search):
    """Bind additional interpreter parts without replacing metadata Merkle evidence.

    Each root retains its original metadata key and adds the exact IR bytes of
    its compiled import closure. Missing optional legacy IR has an explicit
    identity; modern missing IR is rejected before any cache pass can be used.
    """
    import hashlib,json
    from .compact import Region,ModuleParts
    from .paths import find_olean
    inventory=json.loads(Path(inventory_path).read_text())
    if inventory.get('schema') != 1:raise InvalidArtifact('unknown audit input inventory schema')
    metadata={}
    for line in Path(metadata_keys_path).read_text().splitlines():
        module,digest=line.split('\t')
        if module in metadata or len(digest)!=64 or any(c not in '0123456789abcdef'for c in digest):
            raise InvalidArtifact('invalid or duplicate metadata key')
        metadata[module]=digest
    nodes={}
    for row in inventory['modules']:
        name=row['name']
        if name in nodes:raise InvalidArtifact('duplicate audit input module '+name)
        nodes[name]=row
    if set(inventory['roots'])!=set(metadata) or not set(metadata)<=set(nodes):raise InvalidArtifact('audit metadata/IR root inventories disagree')
    local={}
    for name,row in nodes.items():
        olean=find_olean(name,search)
        if str(olean)!=row['files'][0]:raise InvalidArtifact('audit input path changed for '+name)
        path=olean.with_suffix('.ir')
        if path.exists():
            local[name]=Region(path).sha256
        else:
            parts=ModuleParts();modern,_=parts.projection(parts.add(olean))
            if modern:raise InvalidArtifact('missing compiled interpreter input: '+str(path))
            local[name]='legacy-no-separate-IR'
    completed={};active=set()
    for root in nodes:
        tasks=[(root,False)]
        while tasks:
            name,finish=tasks.pop()
            if name in completed:continue
            if name not in nodes:raise InvalidArtifact('missing audit IR dependency '+name)
            if finish:
                payload=['ccl-audit-ir-closure-v1',name,local[name],[(d,completed[d])for d in nodes[name]['imports']]]
                completed[name]=hashlib.sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest();active.remove(name)
            else:
                if name in active:raise InvalidArtifact('cyclic audit IR import '+name)
                active.add(name);tasks.append((name,True))
                tasks.extend((d,False)for d in reversed(nodes[name]['imports'])if d not in completed)
    return '\n'.join(name+'\t'+hashlib.sha256(('ccl-audit-input-v1\0'+metadata[name]+'\0'+completed[name]).encode()).hexdigest()for name in inventory['roots'])+'\n'
