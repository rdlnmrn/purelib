"""Pinned official-kernel replay of complete old constants at new compiled types.

Metadata planning uses checked compact bytes. Availability, insertion, groups and
probe acceptance are decided by the original official native checked environment.
"""
from pathlib import Path
from functools import cmp_to_key
import hashlib,json,os,struct,subprocess,tempfile,threading,time,resource,sys
from .compact import InvalidArtifact
from .importer import Module,Graph
from .observations import Observations,name_observer,name_hash,quick_cmp,query_observer
from .paths import render_name
from .writer import Writer,probe_constant
from .alias import Aliases
from .kernel_replay import replay,text
from .typed import TypedDecoder

class KernelError(Exception):pass

def digest(path):
    with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

class Bindings:
    """Invocation-time exact paths/bytes, including absent selected artifact parts."""
    def __init__(self):self.rows={}
    def add(self,path,role):
        path=Path(path).absolute();key=str(path)
        before=path.stat() if path.exists() else None
        sha=digest(path) if before is not None else None
        after=path.stat() if path.exists() else None
        identity=lambda s:None if s is None else (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)
        if identity(before)!=identity(after):raise InvalidArtifact('changed while binding: '+key)
        row={'path':key,'sha256':sha,'bytes':None if after is None else after.st_size,'roles':[role]}
        old=self.rows.get(key)
        if old:
            if old['sha256']!=sha:raise InvalidArtifact('changed consumed input: '+key)
            old['roles']=sorted(set(old['roles']+[role]))
        else:self.rows[key]=row
    def module(self,module,role):
        for r in module.d.parts.regions:self.add(r.path,role)
        self.add(module.path.with_suffix('.ir'),role+'-ir')
    def verify(self):
        for row in self.rows.values():
            p=Path(row['path']);now=digest(p) if p.exists() else None
            if now!=row['sha256']:raise InvalidArtifact('changed invocation input: '+str(p))

def native_build(tc,cache,bindings):
    """Content-addressed original-C-API adapter; regular independently built output."""
    import fcntl,shlex
    tc=Path(tc).resolve();cache=Path(cache);source=Path(__file__).with_name('kernel_native.c')
    version=subprocess.run([str(tc/'bin/lean'),'--version'],capture_output=True,check=True).stdout.decode()
    if '4.32.2' not in version or 'f3b06c705e6c85f5314019d5d3baab0fec5b580c' not in version:raise InvalidArtifact('unsupported installed compiler/kernel ABI')
    flags=['-std=c11','-O2','-Wall','-Wextra','-Werror','-isystem',str(tc/'include'),'-isystem',str(tc/'include/clang')]
    cmd=[str(tc/'bin/clang'),*flags,str(source),'-L',str(tc/'lib/lean'),'-Wl,-rpath,'+str(tc/'lib/lean'),'-lleanshared']
    # Official preprocessor determines the exact selected public header closure.
    deps=subprocess.run([str(tc/'bin/clang'),*flags,'-M',str(source)],capture_output=True,check=True)
    paths=shlex.split(deps.stdout.decode().replace('\\\n',' ').split(':',1)[1])
    binding=Bindings()
    for path in [*paths,tc/'bin/clang',tc/'bin/lean',tc/'lib/lean/libleanshared.so']:
        binding.add(path,'native-build-input')
    identity={'protocol':1,'compiler_revision':'f3b06c705e6c85f5314019d5d3baab0fec5b580c','command':cmd,'inputs':list(binding.rows.values())}
    key=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest()
    directory=cache/key;directory.mkdir(parents=True,exist_ok=True)
    binary=directory/'kernel-replay';manifest=directory/'binding.json'
    with (directory/'build.lock').open('a+b') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        reuse=False
        if manifest.exists() and binary.exists() and not binary.is_symlink():
            old=json.loads(manifest.read_text());reuse=old.get('identity')==identity and old.get('binary_sha256')==digest(binary)
        if not reuse:
            temp=directory/'kernel-replay.partial'
            result=subprocess.run([*cmd,'-o',str(temp)],capture_output=True)
            (directory/'compile.stdout').write_bytes(result.stdout);(directory/'compile.stderr').write_bytes(result.stderr)
            if result.returncode or result.stderr:raise InvalidArtifact('native adapter compilation failed: '+result.stderr.decode('utf8','replace'))
            if not temp.is_file() or temp.is_symlink():raise InvalidArtifact('native adapter output is not a regular file')
            binding.verify();temp.replace(binary)
            record={'identity':identity,'binary_sha256':digest(binary),'compiler_exit':0,'stdout_sha256':hashlib.sha256(result.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(result.stderr).hexdigest()}
            pending=directory/'binding.json.partial';pending.write_text(json.dumps(record,indent=2)+'\n');pending.replace(manifest)
        binding.verify()
    for row in binding.rows.values():bindings.add(row['path'],'native-build-input')
    bindings.add(binary,'native-binary');bindings.add(manifest,'native-build-receipt')
    # Bind actual dynamic libraries selected by the independently built binary.
    linked=subprocess.run(['ldd',str(binary)],capture_output=True,check=True).stdout.decode()
    for line in linked.splitlines():
        words=line.split();paths=[word for word in words if word.startswith('/')]
        if paths:bindings.add(paths[0],'selected-dynamic-library')
    return binary

class Native:
    """Counted command/error frames to one retained official checked environment."""
    def __init__(self,binary,old,new,tc,environment=None):
        self.process=subprocess.Popen([str(binary),'service',str(old),str(new),str(tc)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=environment)
        self.peak=0;self.rss_stop=False;self.done=threading.Event()
        self.monitor=threading.Thread(target=self._monitor,daemon=True);self.monitor.start()
        try:self.receive()
        except BaseException:
            self.close();raise
    def _monitor(self):
        while not self.done.wait(.05):
            total=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
            for path in Path('/proc').glob('[0-9]*/stat'):
                try:
                    raw=path.read_text();fields=raw[raw.rfind(')')+2:].split()
                    if int(path.parent.name)==self.process.pid:total+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')
                except (OSError,ValueError,IndexError):pass
            self.peak=max(self.peak,total)
    def read(self,size):
        out=bytearray()
        while len(out)<size:
            data=self.process.stdout.read(size-len(out))
            if not data:
                raise InvalidArtifact('native kernel transport ended before complete response')
            out.extend(data)
        return bytes(out)
    def receive(self):
        header=self.read(9);tag=header[0];size=struct.unpack('<Q',header[1:])[0];body=self.read(size)
        if tag==1:raise KernelError(body.decode('utf8','strict'))
        if tag!=0:raise InvalidArtifact('unknown native kernel response tag')
        return body
    def call(self,op,payload=b''):
        self.process.stdin.write(bytes([op])+struct.pack('<Q',len(payload))+payload);self.process.stdin.flush();return self.receive()
    def packet(self,path):return struct.unpack('<Q',self.call(3,os.fsencode(path)))[0]
    def contains(self,packet,index):
        raw=self.call(4,struct.pack('<QQ',packet,index))
        if raw not in (b'\0',b'\1'):raise InvalidArtifact('invalid kernel membership result')
        return raw==b'\1'
    def add(self,slot,index,mode,name):self.call(5,struct.pack('<QQQ',slot,index,mode)+name.encode('utf8'))
    def compare(self,op,index,name):self.call(op,struct.pack('<Q',index)+name.encode('utf8'))
    def close(self):
        try:
            if self.process.poll() is None:
                try:self.call(0)
                except (BrokenPipeError,InvalidArtifact,KernelError):pass
            self.process.stdin.close();code=self.process.wait()
            stderr=self.process.stderr.read()
            if code not in (0,1) or stderr:raise InvalidArtifact('native kernel terminated unexpectedly: '+stderr.decode('utf8','replace'))
        finally:self.done.set();self.monitor.join();self.process.stdout.close();self.process.stderr.close()

class Packets:
    def __init__(self,session,header,directory):self.session=session;self.header=header;self.directory=directory;self.serial=0;self.original_names={}
    def remember(self,module):
        for (kind,ptr),idx in module.d.cache.items():
            if kind=="Name":self.original_names.setdefault(name_observer(module.d,idx),(module.d,ptr))
    def begin(self):
        w=Writer(self.header,0x700000000000+self.serial*0x100000000);self.serial+=1;return w
    def caches(self,w,changed):
        if not changed:return
        path=self.directory/('cache-'+str(self.serial)+'.compact')
        w.write(path,w.array([row['result'] for row in changed]))
        d=TypedDecoder([]);region=d.parts.add(path);d.decode('Array:Expr',region.root)
        count=struct.unpack('<Q',self.session.call(8,os.fsencode(path)))[0]
        if count!=len(changed):raise InvalidArtifact('incomplete original factory cache comparison')
    def publish(self,w,infos=(),names=(),groups=(),quotients=()):
        path=self.directory/('packet-'+str(self.serial)+'.compact');root=w.array([w.array(infos),w.array(names),w.array(groups),w.array(quotients)]);w.write(path,root)
        d=TypedDecoder([]);region=d.parts.add(path);arrays=d.parts.array(region.root)
        for ty,ptr in zip(('Array:ConstantInfo','Array:Name','Array:GroupInputs','Array:Declaration'),arrays):d.decode(ty,ptr)
        return self.session.packet(path)
    def query(self,key):
        w=self.begin();original=self.original_names.get(key)
        ptr=w.clone(original[0].parts,original[1]) if original is not None else name_node(w,key[1])
        slot=self.publish(w,names=[ptr]);return self.session.contains(slot,0)

def natural(w,n):
    if n<0:raise InvalidArtifact('negative serialized Nat')
    if n<(1<<63):return 2*n+1
    size=(n.bit_length()+63)//64;offset=len(w.data)
    raw=struct.pack('<IHBBiiQ',0,(24+size*8)&65535,0,250,size,size,w.base+offset+24)+n.to_bytes(size*8,'little')
    return w.add(raw)

def name_node(w,components):
    ptr=1;prefix=[]
    for tag,value in components:
        if tag==1:ptr=w.name_str(ptr,tuple(prefix),value)
        elif tag==2:ptr=w.ctor(2,[ptr,natural(w,value)],struct.pack('<Q',name_hash(tuple(prefix)+((2,value),))))
        else:raise InvalidArtifact('invalid Name component')
        prefix.append((tag,value))
    return ptr

def compare(oldpath,newpath,names,binary,tc,search,receipt=None,environment=None,initial_bindings=None):
    """Replay old data and kernel-check its complete original constants at new types."""
    if not names:raise KernelError('at least one name is required')
    binding=initial_bindings if initial_bindings is not None else Bindings();native=None;rows=[];outcome='failed';error=None
    for path in [binary,tc/'bin/lean',tc/'bin/clang',tc/'lib/lean/libleanshared.so']:
        binding.add(path,'native-toolchain')
    for path in Path(__file__).parent.glob('*.py'):binding.add(path,'host-reader-source')
    binding.add(Path(__file__).with_name('kernel_native.c'),'native-adapter-source')
    for path in (oldpath,newpath):
        for suffix in ('','.server','.private'):binding.add(Path(str(path)+suffix),'selected-artifact')
        binding.add(Path(path).with_suffix('.ir'),'selected-ir')
    try:
        with tempfile.TemporaryDirectory(prefix='lean-kernel-equivalence-') as directory:
            native=Native(binary,oldpath,newpath,tc,environment)
            eq={};payloads={};old=Module('Comparison.Old',oldpath,eq,payloads);new=Module('Comparison.New',newpath,eq,payloads)
            if any(len(m.d.parts.array(m.data(True)[1]))!=len(m.d.parts.array(m.data(True)[2])) for m in (old,new)):raise KernelError("inconsistent compiled declaration metadata")
            oldentries=old.entries(True);newentries=new.entries(True)
            binding.module(old,'old-input');binding.module(new,'new-input')
            selected=set()
            for raw in names:
                key=query_observer(raw)
                if key in selected:raise KernelError('duplicate selected name: '+render_name(key[1]))
                selected.add(key)
            native.call(2)
            # Binding import parts runs only AFTER the original actual importer.
            graph=Graph(search);imports=[render_name(c) for c,_,_ in old.imports(True)];order,state=graph.imports(imports,True)
            for module in graph.modules.values():binding.module(module,'import-private')
            for module in graph.ir.values():
                if module is not None:binding.module(module,'import-ir')
            oldmap={};newmap={}
            for _,r,_ in oldentries:
                k=name_observer(r.d,r.name)
                if k in oldmap:raise KernelError('duplicate old declaration: '+text(r))
                oldmap[k]=r
            header=old.d.parts.regions[0].data[:96];packets=Packets(native,header,Path(directory));packets.remember(old);packets.remember(new);w=packets.begin()
            actions,groups,quotients=replay(old,w);slot=packets.publish(w,groups=groups,quotients=quotients)
            for kind,index,name in actions:
                if kind=='O':native.add(0,index,0,name)
                elif kind=='G':native.add(slot+2,index,2,name)
                elif kind=='Q':native.add(slot+2,index,3,name)
                else:native.compare(6 if kind=='C' else 7,index,name)
            for _,r,_ in newentries:
                k=name_observer(r.d,r.name)
                if k in newmap:raise KernelError('duplicate new declaration: '+text(r))
                newmap[k]=r
            def constant_names(module):
                return {name_observer(module.d,module.d.decode('Name',p)) for p in module.d.parts.array(module.data(True)[1])}
            oldnames=constant_names(old);newnames=constant_names(new)
            aliases={};aliaskeys={};rewrite=packets.begin()
            for i,(_,r,_) in enumerate(newentries):
                if '._proof_' not in text(r):continue
                components=((1,'ProjectCompiledTypeEquivalence'),(1,'generated'),(2,i));key=(name_hash(components),components)
                if key in oldnames or key in newnames or packets.query(key):raise KernelError('generated helper fresh-name collision: '+render_name(components))
                original=name_observer(r.d,r.name);aliases[original]=name_node(rewrite,components);aliaskeys[original]=key
            aw=Aliases(rewrite,aliases);infos=[]
            for _,r,_ in newentries:
                infos.append(aw.info(r) if r.kind in (1,2,3) else rewrite.clone(r.d.parts,r.ptr))
            packets.caches(rewrite,aw.changed)
            newslot=packets.publish(rewrite,infos=infos)
            indices={name_observer(r.d,r.name):i for i,(_,r,_) in enumerate(newentries)}
            seen=set();obs=Observations.__new__(Observations)
            ordered=lambda keys:sorted(keys,key=cmp_to_key(quick_cmp))
            def remember_used(ref,keys):
                packets.remember(ref.module);return keys
            def find(mapping,key):
                if key not in mapping:raise KernelError('expected one declaration named '+render_name(key[1])+', found 0')
                return mapping[key]
            def install(key):
                tasks=[('enter',key)]
                while tasks:
                    op,k=tasks.pop();raw=render_name(k[1]);target=aliaskeys.get(k,k)
                    if op=='enter':
                        if packets.query(target):continue
                        if k not in aliases and k in oldnames:raise KernelError('old declaration not replayed: '+raw)
                        if k in seen:raise KernelError('cyclic new declaration dependency: '+raw)
                        r=find(newmap,k);seen.add(k);tasks.append(('finish',k))
                        tasks.extend(('enter',dep) for dep in reversed(ordered(remember_used(r,obs.used(r)))))
                    else:
                        r=find(newmap,k)
                        if r.kind==0:raise KernelError('type comparison cannot install an axiom: '+raw)
                        if r.kind not in (1,2,3):raise KernelError('unsupported declaration dependency: '+raw)
                        native.add(newslot+2,indices[k],4,raw)
            for raw in names:
                key=query_observer(raw);o=find(oldmap,key);n=find(newmap,key);label=render_name(key[1])
                if o.kind!=n.kind or o.d.eq_ids[o.levels()]!=n.d.eq_ids[n.levels()]:raise KernelError('kind or universe parameters changed: '+label)
                if not packets.query(key):raise KernelError('selected old declaration was not replayed: '+label)
                for dep in ordered(remember_used(n,obs.expression_names(n,n.type()))):install(dep)
                components=key[1]+((1,'compiledTypeEquivalenceProbe'),);pk=(name_hash(components),components)
                if packets.query(pk) or pk in oldnames or pk in newnames:raise KernelError('probe-name collision: '+render_name(components))
                pw=packets.begin();pa=Aliases(pw,{k:name_node(pw,v[1]) for k,v in aliaskeys.items()});pn=name_node(pw,components)
                ty=pa.expr(n.d,n.base[2]);val=pw.ctor(0,[pw.ctor(0,[pn,pw.clone(o.d.parts,o.base[1]),ty]),probe_constant(pw,o),1,pw.list([pn])],b'\1')
                packets.caches(pw,pa.changed)
                ps=packets.publish(pw,infos=[pw.ctor(1,[val])]);native.add(ps+2,0,1,label)
                line=('kernel-defeq\t'+label+'\n').encode('utf8');sys.stdout.buffer.write(line);sys.stdout.buffer.flush();rows.append(label)
            outcome='passed'
    except (KernelError,InvalidArtifact,OSError) as e:
        error=str(e);raise
    finally:
        if native is not None:native.close()
        binding.verify()
        if receipt is not None:
            record={'schema':1,'claim':'old constant at complete new type by official checked kernel insertion','status':outcome,'error':error,'selected':[str(n) for n in names],'successful_names':rows,'search_path':[str(p) for p in search],'inputs':list(binding.rows.values()),'native_peak_aggregate_rss_bytes':None if native is None else native.peak,'rss_stop':False if native is None else native.rss_stop,'runtime_contains':'actual original lean_environment_find','extension_loading':False,'artifact_scope':'serialized stable parts required; each consumed byte revalidated after invocation','memory_monitoring':'observational only; no production RSS/timeout/heartbeats cap'}
            Path(receipt).write_text(json.dumps(record,indent=2)+'\n')
