#!/usr/bin/env python3
"""Reconstruct the patched Core sysroot from tracked patches and a pinned release.

No prior epoch or prebuilt private native binary is an input. Completed emissions
are content checked before reuse; a different configuration gets a separate cache.
The authoritative project build, axiom audit and nanoda checks remain separate.
"""
from pathlib import Path
from scripts.paths import ROOT
import argparse, fcntl, hashlib, json, os, shutil, subprocess, sys, signal, time

EXT = ['.olean', '.olean.server', '.olean.private', '.ir']
def sha(p):
    with Path(p).open('rb') as f: return hashlib.file_digest(f, 'sha256').hexdigest()
def bind(p): return {'path': str(Path(p).resolve()), 'sha256': sha(p)}
def read(p): return json.loads(Path(p).read_text())
def put(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    q = Path(str(p) + '.partial')
    q.write_text(json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n')
    q.replace(p)
def copy(p, q):
    q.parent.mkdir(parents=True, exist_ok=True)
    if q.is_symlink(): q.unlink()
    if q.exists():
        if sha(p) != sha(q): raise ValueError('stale existing output: ' + str(q))
        return
    with Path(p).open('rb') as a, q.open('xb') as b:
        try: fcntl.ioctl(b.fileno(), 0x40049409, a.fileno())
        except OSError: shutil.copyfileobj(a, b, 4 << 20)
    if sha(p) != sha(q): raise ValueError('copy changed bytes')
ACTIVE=None
STOP_REQUESTED=False
def interrupt(signum, frame):
    # Never call Popen.wait() from its own signal-interrupted wait path.
    global STOP_REQUESTED
    STOP_REQUESTED=True
signal.signal(signal.SIGTERM,interrupt);signal.signal(signal.SIGINT,interrupt)
def run(cmd, log, env):
    global ACTIVE
    if STOP_REQUESTED:raise KeyboardInterrupt('private preparation interrupted; checkpoints retained')
    with log.open('wb') as f:
        ACTIVE=subprocess.Popen([str(x) for x in cmd],env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        stopped=False;stop_time=None
        try:
            while ACTIVE.poll() is None:
                if STOP_REQUESTED and not stopped:
                    if os.getpgid(ACTIVE.pid)!=ACTIVE.pid:raise RuntimeError('owned command process-group identity changed')
                    os.killpg(ACTIVE.pid,signal.SIGTERM);stopped=True;stop_time=time.monotonic()
                if stopped and time.monotonic()-stop_time>5:
                    # Process teardown only: no mathematical job timeout or limit change.
                    if os.getpgid(ACTIVE.pid)!=ACTIVE.pid:raise RuntimeError('owned command process-group identity changed')
                    os.killpg(ACTIVE.pid,signal.SIGKILL)
                time.sleep(.05)
            code=ACTIVE.wait()
            if STOP_REQUESTED:
                # A dead native driver may leave a compiler child in the same owned PGID.
                try:os.killpg(ACTIVE.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                raise KeyboardInterrupt('private preparation interrupted; checkpoints retained')
        finally:ACTIVE=None
    if code:raise RuntimeError(f'command failed ({code}): {log}')
def closure(graph, roots):
    seen = set(); todo = list(roots)
    while todo:
        m = todo.pop()
        if m in seen: continue
        seen.add(m); todo.extend(graph[m])
    return seen
def topo(graph, selected):
    pending = set(selected); order = []
    while pending:
        ready = sorted(m for m in pending if not pending.intersection(graph[m]))
        if not ready: raise ValueError('Core import cycle')
        order += ready; pending -= set(ready)
    return order

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--base', type=Path, required=True)
p.add_argument('--config', type=Path, required=True)
p.add_argument('--prefix', type=Path, required=True)
p.add_argument('--cache', type=Path, required=True)
p.add_argument('--repo', type=Path, default=ROOT)
p.add_argument('--jobs', type=int, default=4)
p.add_argument('--stop-after-native',action='store_true',help='bounded cold bootstrap/relink checkpoint without Core forward rebuilding')
a = p.parse_args(); base = a.base.resolve(); repo = a.repo.resolve(); cfg = read(a.config)
if not 1 <= a.jobs <= 4: raise ValueError('the measured compiler pool permits 1..4 workers')
if sha(base/'bin/lean') != cfg['upstream_compiler_sha256']: raise ValueError('wrong original compiler')
for rel, expected in cfg['upstream_native_tools'].items():
    if sha(base/rel) != expected: raise ValueError('wrong pinned native input: ' + rel)
# Review authorization is acceptance evidence, not a mathematical build input.
producer_paths=[Path(__file__).resolve(),Path(__file__).parent/'epoch_worker.py',Path(__file__).parent/'prepare_prefix.py']
producer_paths+=sorted((repo/'scripts/lean_module_data').glob('*.py'))
producer_inputs=[bind(z) for z in producer_paths]
system_tools={n:bind(shutil.which(n)) for n in ['ar','nm','patch']}
semantic_config={k:v for k,v in cfg.items() if k!='production_review_pending'}
build_key=hashlib.sha256(json.dumps({'config':semantic_config,'producers':producer_inputs,'system_tools':system_tools},sort_keys=True).encode()).hexdigest()
cache = a.cache.resolve()/build_key; cache.mkdir(parents=True, exist_ok=True)
if base == cache or base in cache.parents: raise ValueError('cache must be outside the installed toolchain')
lock = (cache/'PREPARE.lock').open('a+b'); fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
put(cache/'BUILD-KEY.json',{'key':build_key,'semantic_config':semantic_config,'full_config':bind(a.config),'producers':producer_inputs,'system_tools':system_tools,'excluded_acceptance_field':'production_review_pending'})
env = os.environ.copy(); env.update(LEAN_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
from scripts.lean_module_data.typed import TypedDecoder
from scripts.lean_module_data.render import Renderer

# One decoder per owner accumulates all four phases, including saved pointers.
def observe(module):
    decoder = TypedDecoder([]); renderer = Renderer(decoder)
    packages = []; headers = []; parts = {}
    for e in EXT:
        path = base/'lib/lean'/Path(module.replace('.', '/')+e)
        if not path.is_file(): raise ValueError('missing original complete part: ' + str(path))
        parts[e] = bind(path); region = decoder.parts.add(path)
        rr, off, fields = decoder.parts.ctor(region.root, 0, 5, 1)
        imports = []
        for ptr in decoder.parts.array(fields[0]):
            r, s, fs = decoder.parts.ctor(ptr, 0, 1, 3)
            imports.append({'name': renderer.name_string(decoder.decode('Name', fs[0])),
                            'flags': list(r.bytes(s, 3))})
        pkgs = []
        for ptr in decoder.parts.array(fields[4]):
            fs = decoder.parts.ctor(ptr, 0, 2, 0)[2]
            if renderer.name_string(decoder.decode('Name', fs[0])) == '_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt':
                values = decoder.parts.array(fs[1])
                if len(values) != 1: raise ValueError('ambiguous original module package')
                z = values[0]
                pkgs.append(None if z == 1 else decoder.parts.string(decoder.parts.ctor(z, 1, 1, 0)[2][0]))
        if len(pkgs) != 1: raise ValueError('original package observation missing')
        packages += pkgs
        headers.append({'phase': e, 'isModule': bool(rr.bytes(off, 1)[0]), 'ordered_imports': imports})
    if len({json.dumps(x) for x in packages}) != 1: raise ValueError('package disagreement by phase')
    if len({h['isModule'] for h in headers}) != 1: raise ValueError('module-mode disagreement')
    return {'module': module, 'package': packages[0], 'isModule': headers[0]['isModule'],
            'headers': headers, 'parts': parts}

sources = {}; patch_inputs = []
for row in cfg['sources']:
    m = row['module']; rel = Path(m.replace('.', '/')+'.lean'); old = base/'src/lean'/rel
    patch = a.config.parent/row['patch']
    if sha(old) != row['original_source_sha256'] or sha(patch) != row['patch_sha256']:
        raise ValueError('source or tracked patch differs: ' + m)
    dst = cache/'source'/rel
    if dst.exists() and sha(dst) not in (row['original_source_sha256'],row['candidate_source_sha256']):
        dst.rename(Path(str(dst)+'.interrupted.'+str(time.time_ns())))
    if not dst.exists():copy(old,dst)
    if sha(dst)==row['original_source_sha256']:
        run(['patch', '--batch', '--fuzz=0', '--no-backup-if-mismatch', '-p1',
             '-d', cache/'source', '-i', patch.resolve()], cache/(m+'.patch.log'), env)
    if sha(dst) != row['candidate_source_sha256']: raise ValueError('patched source mismatch: ' + m)
    sources[m] = bind(dst); patch_inputs += [bind(old), bind(patch), bind(dst)]

# Discover the required complete installed import closure, not an assumed prefix.
contexts = {}; graph = {}; queue = list(cfg['project_boundary_roots']) + list(sources)
queue += cfg.get('proof_import_roots', []) + cfg['native_driver_imports']
while queue:
    m = queue.pop()
    if m in contexts: continue
    c = observe(m); contexts[m] = c
    graph[m] = sorted({i['name'] for h in c['headers'] for i in h['ordered_imports']})
    queue.extend(graph[m])
for m, additional in cfg.get('additional_imports', {}).items():
    for dep in additional:
        if dep not in graph: raise ValueError('new import not in required original closure: ' + dep)
    graph[m] = sorted(set(graph[m]) | set(additional))
original_rows = [{'module':m, 'part':e, 'immutable':z} for m,c in contexts.items() for e,z in c['parts'].items()]
original_sources = []
for m in graph:
    old=base/'src/lean'/Path(m.replace('.', '/')+'.lean'); dst=cache/'source'/Path(m.replace('.', '/')+'.lean')
    if m not in sources:copy(old,dst)
    original_sources.append({'module':m, 'immutable':bind(old if m in sources else dst)})
put(cache/'CONTEXTS.json', {'rows':list(contexts.values()),
    'options_dynlibs_plugins':'Empty reconstructed checkpoint choices, not historical setup provenance.'})
put(cache/'GRAPH.json', graph)
put(cache/'ORIGINAL.json', {'rows':original_rows, 'original_sources':original_sources})

resolver = cache/'bootstrap/lib'; resolver.mkdir(parents=True, exist_ok=True)
for row in original_rows:
    q = resolver/Path(row['module'].replace('.', '/')+row['part']); q.parent.mkdir(parents=True, exist_ok=True)
    if not q.exists(): q.symlink_to(row['immutable']['path'])
ledger = {m:dict(c['parts']) for m,c in contexts.items()}
def bootstrap(module, source, ctx):
    deps = closure(graph, graph.get(module, [])); output = cache/'bootstrap'/Path(module.replace('.', '/'))
    output.parent.mkdir(parents=True, exist_ok=True)
    setup = {'name':module, 'package':ctx['package'], 'isModule':ctx['isModule'], 'imports':None,
        'importArts':{m:[ledger[m][e]['path'] for e in ['.olean','.ir','.olean.server','.olean.private']] for m in sorted(deps)},
        'options':{}, 'dynlibs':[], 'plugins':[]}
    sp = Path(str(output)+'.setup.json'); put(sp, setup)
    cmd = [base/'bin/lean', '-R', cache/'source', '--setup', sp, '-DwarningAsError=true', source,
           '-o', str(output)+'.olean', '-i', str(output)+'.ilean', '-c', str(output)+'.c']
    complete_inputs=[ledger[m][e] for m in sorted(deps) for e in EXT]
    for z in complete_inputs:
        if sha(z['path'])!=z['sha256']:raise ValueError('bootstrap import bytes changed')
    key = hashlib.sha256(json.dumps({'command':list(map(str,cmd)), 'source':bind(source),
          'setup':setup, 'complete_import_parts':complete_inputs,'tools':cfg['upstream_native_tools']},sort_keys=True).encode()).hexdigest()
    receipt = Path(str(output)+'.COMPILE.json')
    if receipt.exists() and read(receipt)['key'] == key:
        for z in read(receipt)['parts'].values():
            if sha(z['path']) != z['sha256']: raise ValueError('corrupt bootstrap checkpoint')
    else:
        run(cmd, Path(str(output)+'.log'), {**env,'LEAN_PATH':str(resolver)})
        put(receipt, {'key':key,'complete_import_parts':complete_inputs, 'parts':{e:bind(str(output)+e) for e in EXT+['.ilean','.c']}})
    for z in complete_inputs:
        if sha(z['path'])!=z['sha256']:raise ValueError('bootstrap import bytes changed after command')
    return read(receipt)['parts']

# Bootstrapping the proof API does not change runtime operations. It supplies the
# new quoted constant names needed when compiling the native WF proof producer.
for m in cfg['native_bootstrap_modules']:
    ps = bootstrap(m, Path(sources[m]['path']), contexts[m]); ledger[m] = {e:ps[e] for e in EXT}
    for e in EXT:
        dst = resolver/Path(m.replace('.', '/')+e); dst.unlink(); dst.symlink_to(ps[e]['path'])
native_parts={}
for m in topo(graph,{row['module'] for row in cfg['native_replacements']}):
    ps=bootstrap(m,Path(sources[m]['path']),contexts[m]);native_parts[m]=ps
    ledger[m]={e:ps[e] for e in EXT}
    for e in EXT:
        dst=resolver/Path(m.replace('.', '/')+e);dst.unlink();dst.symlink_to(ps[e]['path'])
native = cache/'native'; native.mkdir(exist_ok=True); objects = []
archive_key = native/'ARCHIVE.json'
archive_names = sorted({'libLean.a', *(r.get('archive', 'libLean.a') for r in cfg['native_replacements'])})
if not set(archive_names) <= {'libLean.a', 'libInit.a', 'libStd.a'}:
    raise ValueError('unsupported native replacement archive')
archives = {name: native/(name.removesuffix('.a')+'-patched.a') for name in archive_names}
archive = archives['libLean.a']
# Always revalidate the actual bootstrap imports before native checkpoint reuse.
for row in cfg['native_replacements']:
    m=row['module']; ps=native_parts[m]
    obj=native/(m+'.o'); receipt=native/(m+'.OBJECT.json')
    key={'c':ps['.c'],'leanc':bind(base/'bin/leanc'),'flags':['-DLEAN_EXPORTING','-O3']}
    if receipt.exists() and read(receipt)['key']==key:
        if sha(obj)!=read(receipt)['object']['sha256']:raise ValueError('corrupt native object checkpoint')
    else:
        run([base/'bin/leanc','-DLEAN_EXPORTING','-O3','-c',ps['.c']['path'],'-o',obj],native/(m+'.object.log'),env)
        put(receipt,{'key':key,'object':bind(obj)})
    objects.append(bind(obj))
object_archives = [{'object':obj, 'archive':row.get('archive','libLean.a')}
                   for row,obj in zip(cfg['native_replacements'],objects)]
recipe={'original_archives':{name:bind(base/'lib/lean'/name) for name in archive_names},
        'replacements':cfg['native_replacements'],'objects':objects,'object_archives':object_archives}
if archive_key.exists() and read(archive_key).get('recipe')==recipe:
    for row in read(archive_key)['archives']:
        if sha(row['binding']['path'])!=row['binding']['sha256']:raise ValueError('corrupt native archive checkpoint')
else:
    # A partial or outdated modified archive is never used as the next original.
    for name,path in archives.items():
        if path.exists():path.rename(native/(name+'-interrupted-'+str(time.time_ns())))
        copy(base/'lib/lean'/name,path)
    removals=[]
    for row in cfg['native_replacements']:
        m=row['module'];owner=row.get('archive','libLean.a');path=archives[owner]
        members=subprocess.check_output(['ar','t',str(path)],text=True).splitlines()
        if members.count(row['archive_member'])!=row['original_member_count']:raise ValueError('archive member count differs')
        extract=native/(m+'.original-member');extract.mkdir(exist_ok=True)
        subprocess.run(['ar','xN',str(row['instance']),str(path),row['archive_member']],cwd=extract,check=True)
        symbols=subprocess.check_output(['nm','--defined-only',str(extract/row['archive_member'])],text=True)
        if row['initializer_symbol'] not in {line.split()[-1] for line in symbols.splitlines() if line.split()}:raise ValueError('wrong archive member instance')
        removals.append((owner,row['archive_member'],row['instance']))
    if len(set(removals))!=len(removals):raise ValueError('duplicate native archive member selection')
    # Select against original members first, then remove duplicate-name occurrences
    # from highest to lowest so the remaining occurrence indices stay valid.
    for owner,member,instance in sorted(removals,reverse=True):
        subprocess.run(['ar','dN',str(instance),str(archives[owner]),member],check=True)
    put(archive_key,{'recipe':recipe,'archive':bind(archive),'archives':[{'name':name,'binding':bind(path)} for name,path in archives.items()],
                     'objects':objects,'object_archives':object_archives})
native_state=read(archive_key)
for z in [*[row['binding'] for row in native_state['archives']],*native_state['objects']]:
    if sha(z['path'])!=z['sha256']:raise ValueError('corrupt native checkpoint')
cli = a.config.parent/cfg['native_driver_source']
if sha(cli) != cfg['native_driver_source_sha256']: raise ValueError('CLI source differs')
cli_copy = cache/'source/PrivateLeanCLI.lean'; copy(cli, cli_copy)
graph['PrivateLeanCLI'] = cfg['native_driver_imports']
ps = bootstrap('PrivateLeanCLI', cli_copy, {'package':None,'isModule':True})
text = Path(ps['.c']['path']).read_text(); old = 'res = runtime_initialize_PrivateLeanCLI(1 /* builtin */);'
if text.count(old) != 1: raise ValueError('generated CLI entry shape changed')
entry = native/'PrivateLeanCLI-full-init.c'; entry.write_text(text.replace(old,'res = initialize_PrivateLeanCLI(1 /* builtin */);'))
host = cache/'native-sysroot/bin/lean'; host.parent.mkdir(parents=True,exist_ok=True)
lib=host.parent.parent/'lib/lean';lib.parent.mkdir(parents=True,exist_ok=True)
if not lib.exists():lib.symlink_to(base/'lib/lean',target_is_directory=True)
link = [base/'bin/leanc','-O3','-Wl,--export-dynamic','-o',host,entry,
        *[z['path'] for z in native_state['objects']],'-Wl,--whole-archive',archive,
        *[archives.get(n,base/'lib/lean'/n) for n in ['libInit.a','libStd.a','libleancpp.a','libleanrt.a']],'-Wl,--no-whole-archive']
host_receipt = native/'HOST.json'
host_key={'entry':bind(entry),'archive':native_state['archive'],'objects':native_state['objects'],'libraries':[bind(archives.get(n,base/'lib/lean'/n)) for n in ['libInit.a','libStd.a','libleancpp.a','libleanrt.a']],'leanc':bind(base/'bin/leanc'),'link':list(map(str,link))}
if not host_receipt.exists() or read(host_receipt).get('key')!=host_key:
    run(link,native/'link.log',env); put(host_receipt,{'key':host_key,'host':bind(host),'entry':bind(entry),'link':list(map(str,link))})
if sha(host) != read(host_receipt)['host']['sha256']: raise ValueError('corrupt native compiler checkpoint')

if a.stop_after_native:
    put(cache/'NATIVE-CHECKPOINT.json',{'build_key':bind(cache/'BUILD-KEY.json'),'status':'COLD_BOOTSTRAP_NATIVE_RELINK_COMPLETE_PENDING_REGRESSIONS','host':bind(host),'config':bind(a.config),'archive':native_state,'historical_setup_options':'Not claimed; reconstructed empty choices.'})
    print(cache/'NATIVE-CHECKPOINT.json');sys.exit(0)

affected = set(sources)
while True:
    enlarged = affected | {m for m,deps in graph.items() if affected.intersection(deps)}
    if enlarged == affected: break
    affected = enlarged
affected.discard('PrivateLeanCLI'); graph.pop('PrivateLeanCLI')
put(cache/'GRAPH.json',graph)
request = {'root_private_compilation_authorized':True,'source_in_place':True,
    'recovery':bind(cache/'ORIGINAL.json'),'contexts':bind(cache/'CONTEXTS.json'),
    'full_import_graph':bind(cache/'GRAPH.json'),'host':bind(host),
    'candidate_sources':sources,'topological_order':topo(graph,affected),
    'inputs':[bind(a.config),bind(cache/'BUILD-KEY.json'),*producer_inputs,*system_tools.values(),*patch_inputs]}
put(cache/'REQUEST.json',request)
run([sys.executable,'-m','scripts.toolchain.epoch_worker','--request',cache/'REQUEST.json',
     '--out',cache/'epoch','--jobs',str(a.jobs)],cache/'epoch.log',env)
put(cache/'NATIVE.json',{'host':bind(host),'source':bind(cli)})
if a.prefix.exists():
    previous=read(a.prefix/'CORE-PREFIX.json')
    if previous['config']['sha256']!=sha(a.config) or previous['epoch']['sha256']!=sha(cache/'epoch/EPOCH.json'):raise ValueError('existing prefix is another epoch')
    for row in previous['rows']:
        for z in row['parts'].values():
            if sha(z['path'])!=z['sha256']:raise ValueError('existing prefix part changed')
    print(a.prefix/'CORE-PREFIX.json');sys.exit(0)
run([sys.executable,'-m','scripts.toolchain.prepare_prefix','materialize','--config',a.config,
    '--prefix',a.prefix,'--epoch',cache/'epoch/EPOCH.json','--base',base,'--native-tests',cache/'NATIVE.json',
    '--archive',archive,'--archive-sha256',sha(archive),
    '--objects-json',archive_key],cache/'materialize.log',env)
print(a.prefix/'CORE-PREFIX.json')
