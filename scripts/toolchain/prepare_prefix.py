#!/usr/bin/env python3
"""Materialize a byte-checked Core epoch beside, never inside, the pinned installation.

The private Core compiler produces the explicit epoch ledger first. This script
retains its exact sources and six-part outputs, patched native CLI and archive in
one usable sysroot. It never treats successful emission as kernel acceptance.
"""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,shutil,subprocess,sys

def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def bind(p):return {'path':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_text())
def verify(z):
    p=Path(z['path'])
    if not p.is_file() or sha(p)!=z['sha256']:raise ValueError('missing or stale bytes: '+str(p))
    return p
def replace(src,dst):
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.is_symlink():dst.unlink()
    elif dst.exists():raise ValueError('refusing to overwrite existing prefix file: '+str(dst))
    with Path(src).open('rb') as a,dst.open('xb') as b:
        try:fcntl.ioctl(b.fileno(),0x40049409,a.fileno())
        except OSError:shutil.copyfileobj(a,b,4<<20)
    assert sha(src)==sha(dst)
def atomic(p,v):
    tmp=p.with_suffix(p.suffix+'.partial');tmp.write_text(json.dumps(v,sort_keys=True)+'\n');tmp.replace(p)

def check(config,prefix):
    cfg=read(config);m=read(prefix/'CORE-PREFIX.json')
    if cfg.get('production_review_pending',True):raise ValueError('Core compatibility review is pending; this prefix is a private checkpoint')
    if m['config']['sha256']!=sha(config):raise ValueError('Core source configuration changed')
    for z in m['selected_source_inputs']+m['selected_sources']+m['native_inputs']:verify(z)
    if m['required_roots_missing']:raise ValueError('Core boundary providers are missing')
    for r in m['rows']:
        # Proof bodies in PRIVATE matter independently of their PUBLIC bytes.
        for p in r['parts'].values():verify(p)
    print(m['epoch_key'])

def materialize(args):
    cfg=read(args.config);epoch=read(args.epoch);base=args.base.resolve();prefix=args.prefix.resolve()
    if prefix==base or base in prefix.parents:raise ValueError('prefix must be outside the original toolchain')
    if prefix.exists():raise ValueError('use a fresh detached prefix; no mutation of an accepted epoch')
    if sha(base/'bin/lean')!=cfg['upstream_compiler_sha256']:raise ValueError('original compiler differs from the pinned baseline')
    # Directory copies with per-file symlinks avoid writable directory links.
    prefix.mkdir(parents=True)
    for directory,dirs,files in os.walk(base,followlinks=False):
        rel=Path(directory).relative_to(base);out=prefix/rel;out.mkdir(exist_ok=True)
        for d in list(dirs):
            q=Path(directory)/d
            if q.is_symlink():
                dirs.remove(d);shutil.copytree(q.resolve(),out/d,symlinks=True)
        for f in files:(out/f).symlink_to(Path(directory)/f)
    inputs=[];selected=[]
    for r in cfg['sources']:
        rel=Path(*r['module'].split('.')).with_suffix('.lean');old=base/'src/lean'/rel
        if sha(old)!=r['original_source_sha256']:raise ValueError('original Core source mismatch: '+str(old))
        patch=args.config.parent/r['patch']
        if sha(patch)!=r['patch_sha256']:raise ValueError('patch mismatch')
        new=prefix/'src/lean'/rel;replace(old,new)
        subprocess.run(['patch','--batch','--fuzz=0','--no-backup-if-mismatch','-p1','-d',str(prefix/'src/lean'),'-i',str(patch.resolve())],check=True)
        if sha(new)!=r['candidate_source_sha256']:raise ValueError('patched source mismatch')
        inputs.append(bind(patch));selected.append(bind(new))
    compiled={r['module']:r for r in epoch.get('compiled_rows',[])};parts={}
    for r in epoch['rows']:
        if r['module'].split('.')[0] not in ('Init','Lean','Std','Lake'):continue
        parts.setdefault(r['module'],{})[r['part']]=r['immutable']
    rows=[]
    for module,ps in sorted(parts.items()):
        if set(ps)!=set(('.olean','.olean.server','.olean.private','.ir')):raise ValueError('incomplete four-part Core provider')
        retained={}
        for ext,z in ps.items():
            dst=prefix/'lib/lean'/Path(module.replace('.','/')+ext);replace(verify(z),dst);retained[ext]=bind(dst)
        if module in compiled:
            for ext in ('.c','.ilean'):
                z=compiled[module]['parts'][ext];dst=prefix/'lib/lean'/Path(module.replace('.','/')+ext);replace(verify(z),dst);retained[ext]=bind(dst)
        rows.append({'module':module,'parts':retained})
    host=read(args.native_tests);verify(host['host']);exe=prefix/'bin/lean';replace(host['host']['path'],exe);exe.chmod(0o755)
    # Native frontend calls use the changed archive member. Proof-only seeds retain
    # their original native operations by the separately reviewed whole C/IR evidence.
    archive=prefix/'lib/lean/libLean.a';replace(verify(args.archive_binding),archive)
    object_receipt=read(args.objects_json) if args.objects_json else {'objects':[args.object_binding]}
    object_inputs=object_receipt['objects']
    archives={'libLean.a':archive}
    for row in object_receipt.get('archives',[]):
        name=row['name']
        if name not in ('libLean.a','libInit.a','libStd.a'):raise ValueError('unsupported native archive')
        if name=='libLean.a':
            if row['binding']['sha256']!=args.archive_binding['sha256']:raise ValueError('main native archive differs')
            verify(row['binding']);continue
        if name in archives:raise ValueError('duplicate native archive')
        dst=prefix/'lib/lean'/name;replace(verify(row['binding']),dst);archives[name]=dst
    assignments=object_receipt.get('object_archives',[{'object':z,'archive':'libLean.a'} for z in object_inputs])
    if [r['object'] for r in assignments]!=object_inputs:raise ValueError('native object archive assignments differ')
    required={r.get('archive','libLean.a') for r in cfg['native_replacements']}
    if not required <= archives.keys():raise ValueError('native replacement archives are missing')
    objects=[]
    by_archive={name:[] for name in archives}
    for row in assignments:
        z=row['object'];name=row['archive']
        if name not in archives:raise ValueError('native object archive is missing')
        obj=prefix/'core-native'/Path(z['path']).name;replace(verify(z),obj);objects.append(obj)
        by_archive[name].append(obj)
    for name,selected_objects in by_archive.items():
        if selected_objects:subprocess.run([str(base/'bin/llvm-ar'),'rcs',str(archives[name]),*[str(p) for p in selected_objects]],check=True)
    # Lake prepends its own bin directory in lake env; keep a detached original
    # Lake executable co-located with the custom Lean, rather than a symlink.
    lake=prefix/'bin/lake';replace(base/'bin/lake',lake);lake.chmod(0o755)
    native=[bind(exe),bind(lake),*[bind(p) for p in archives.values()],*[bind(p) for p in objects]]
    driver=args.config.parent/cfg['native_driver_source']
    if sha(driver)!=cfg['native_driver_source_sha256']:raise ValueError('native CLI source mismatch')
    inputs.append(bind(driver))
    roots=set(cfg['project_boundary_roots']);missing=sorted(roots-parts.keys())
    contents={'config':bind(args.config),'epoch':bind(args.epoch),'native_test_receipt':bind(args.native_tests),'native_inputs':native,'selected_source_inputs':inputs,'selected_sources':selected,'rows':rows,'required_roots_missing':missing,'base_sysroot':str(base),'upstream_compiler':bind(base/'bin/lean'),'status':'PRIVATE_PREFIX_MATERIALIZED_REQUIRES_CORE_COMPATIBILITY_REVIEW','shared_frontend':'Original shared libraries retained; patched static host/archive and actual plugin regression are separately bound.'}
    contents['epoch_key']=hashlib.sha256(json.dumps(contents,sort_keys=True).encode()).hexdigest();atomic(prefix/'CORE-PREFIX.json',contents)
    for option,expected in [('--print-prefix',str(prefix)),('--print-libdir',str(prefix/'lib/lean'))]:
        got=subprocess.run([str(exe),option],check=True,capture_output=True,text=True).stdout.strip()
        if got!=expected:raise ValueError('native CLI selected wrong detached prefix')
    print(prefix/'CORE-PREFIX.json')

p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=['materialize','check']);p.add_argument('--config',type=Path,required=True);p.add_argument('--prefix',type=Path,required=True);p.add_argument('--epoch',type=Path);p.add_argument('--base',type=Path);p.add_argument('--native-tests',type=Path);p.add_argument('--archive',type=Path);p.add_argument('--archive-sha256');p.add_argument('--objects-json',type=Path);p.add_argument('--object',type=Path);p.add_argument('--object-sha256');a=p.parse_args()
try:
    if a.mode=='check':check(a.config,a.prefix)
    else:
        if not all((a.epoch,a.base,a.native_tests,a.archive,a.archive_sha256)) or not (a.objects_json or (a.object and a.object_sha256)):raise ValueError('materialize requires epoch/base/native tests/archive/object bindings')
        a.archive_binding={'path':str(a.archive),'sha256':a.archive_sha256};a.object_binding={'path':str(a.object),'sha256':a.object_sha256} if a.object else None;materialize(a)
except (ValueError,OSError,AssertionError,subprocess.CalledProcessError) as e:
    print('Core prefix error: '+str(e),file=sys.stderr);sys.exit(1)
