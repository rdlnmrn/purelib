"""Pinned finite import graph and constant-map merging from checked artifact bytes.

No Environment, initializer, unsafe mapping or reader callback executes.
"""
from pathlib import Path
from .typed import TypedDecoder, InvalidArtifact, INFO, RECORDS
from .render import Renderer
from .paths import find_olean, render_name

class Ref:
    def __init__(self, module, ptr):
        self.module = module; self.d = module.d; self.ptr = ptr
        region, offset, header = self.d.header(ptr)
        self.kind = header[3]
        if self.kind >= len(INFO): raise InvalidArtifact('invalid ConstantInfo tag')
        _, _, fields = self.d.parts.ctor(ptr, self.kind, 1, 0)
        self.val = fields[0]; types, size = RECORDS[INFO[self.kind]]
        vr, scalar, self.fields = self.d.parts.ctor(self.val, 0, len(types), size)
        self.scalar = vr.bytes(scalar, size)
        _, _, self.base = self.d.parts.ctor(self.fields[0], 0, 3, 0)
        self.name = self.d.decode('Name', self.base[0])
        self.key = self.d.eq_ids[self.name]
    def type(self): return self.d.decode('Expr', self.base[2])
    def levels(self): return self.d.decode('List:Name', self.base[1])
    def all(self):
        if self.kind not in (1, 2, 3): raise InvalidArtifact('no all field for this kind')
        return self.d.decode('List:Name', self.fields[2 if self.kind in (2,3) else 3])
    def info(self): return self.d.decode('ConstantInfo', self.ptr)
    def eq(self, idx): return self.d.eq_ids[idx]

class Module:
    def __init__(self, name, path, equal, payloads, data=True):
        self.name=name;self.path=path;self.d=TypedDecoder([])
        self.d.eq_identities=equal;self.d.name_payloads=payloads
        first=self.d.parts.add(path);r,s,f=self.d.parts.ctor(first.root,0,5,1)
        flag=r.bytes(s,1)[0]
        if flag not in (0,1): raise InvalidArtifact('invalid module Bool')
        self.modern=bool(flag);self.roots=[first]
        if data and self.modern:
            self.roots += [self.d.parts.add(str(path)+suffix) for suffix in ('.server','.private')]
        self.refs={};self.indices={};self.rows={}
    def data(self, private=False):
        region=self.roots[-1] if private else self.roots[0]
        r,s,f=self.d.parts.ctor(region.root,0,5,1)
        return f
    def imports(self, private=False):
        return self.d.parts.projection(self.roots[-1] if private else self.roots[0])[1]
    def entries(self, private=False):
        key=private and self.modern
        if key not in self.rows:
            f=self.data(key);names=self.d.parts.array(f[1]);infos=self.d.parts.array(f[2])
            if len(names)!=len(infos):raise InvalidArtifact('compiled contract inconsistent metadata: '+self.name)
            rows=[]
            for name, ptr in zip(names,infos):
                idx=self.d.decode('Name',name)
                if ptr not in self.refs:self.refs[ptr]=Ref(self,ptr)
                rows.append((self.d.eq_ids[idx],self.refs[ptr],idx))
            self.rows[key]=rows
        return self.rows[key]

class Graph:
    def __init__(self, search):
        self.search=search;self.equal={};self.payloads={};self.modules={};self.ir={}
    def load(self,name):
        if name not in self.modules:
            self.modules[name]=Module(name,find_olean(name,self.search),self.equal,self.payloads)
        return self.modules[name]
    def load_ir(self,name):
        if name not in self.ir:
            path=find_olean(name,self.search).with_suffix('.ir')
            self.ir[name]=Module(name,path,self.equal,self.payloads,False) if path.exists() else None
        return self.ir[name]
    def imports(self, roots, private):
        state={};order=[];active=set()
        # Explicit enter/resume/leave tasks preserve Core's depth-first postorder.
        tasks=[('edge',n,(False,True,False),(True,not private,True,False)) for n in reversed(roots)]
        while tasks:
            task=tasks.pop()
            if task[0]=='leave':
                _,name,record,isnew=task
                if isnew:state[name]=record;order.append(name);active.remove(name)
                continue
            _,name,edge,parent=task
            all_parent,export_parent,data_parent,ir_parent=parent
            all_edge,export_edge,meta_edge=edge
            data=data_parent and (export_edge or all_parent)
            all_=private or all_parent and all_edge
            export=export_parent and export_edge
            irtrans=ir_parent or data and meta_edge
            needsir=irtrans or all_ or private
            if not data and not needsir:continue
            irphase='all' if all_ else 'comptime' if irtrans else 'runtime'
            isnew=name not in state
            if name in active:raise InvalidArtifact('cyclic compiled import: '+name)
            old=state.get(name)
            if old is not None:
                data=data or old['data'];all_=all_ or old['all'];export=export or old['export'];irtrans=irtrans or old['irtrans']
                irphase=irphase if irphase==old['irphase'] else 'all'
            module=self.load(name) if data else None
            ir=self.load_ir(name) if irtrans or all_ or private else None
            rec={'data':data,'all':all_,'export':export,'irtrans':irtrans,'irphase':irphase,'module':module,'ir':ir}
            if old is not None and all(rec[k]==old[k] for k in ('data','all','export','irtrans','irphase')):continue
            if old is not None:state[name]=rec
            else:active.add(name)
            # Core bumps flags before descending, but uses the prior module's
            # already-loaded main data for goRec when upgrading an old node.
            selected=old if old is not None else rec
            main=selected['module'] if selected['data'] else selected['ir']
            tasks.append(('leave',name,rec,isnew))
            if main is not None:
                imports=main.imports(selected['all'] and selected['data'])
                for components,_,flags in reversed(imports):
                    tasks.append(('edge',render_name(components),flags,(all_,export,data,irtrans)))
        if not private:
            for name in roots:
                rec=state[name];main=rec['module'] if rec['data'] else rec['ir']
                if main is not None and not main.modern:raise InvalidArtifact('cannot import non-`module` '+name+' from `module`')
        return order,state

    def subsumes(self,new,old,constants):
        if new.key!=old.key or new.eq(new.type())!=old.eq(old.type()) or new.eq(new.levels())!=old.eq(old.levels()):return False
        if new.kind==2 and old.kind==2:return new.eq(new.all())==old.eq(old.all())
        if new.kind==2 and old.kind==0:
            entries=new.d.list_items(new.all())
            return len(entries)==1 and new.eq(entries[0])==old.key and not old.scalar[0]
        if new.kind!=0 or old.kind!=0:return False
        if new.scalar[0]!=old.scalar[0]:return False
        d=new.d;idx=new.type()
        while d.nodes[idx]['tag']==7:idx=d.nodes[idx]['children'][2]
        argc=0
        while d.nodes[idx]['tag']==5:
            argc+=1;idx=d.nodes[idx]['children'][0]
        node=d.nodes[idx]
        if node['tag']!=4:return False
        other=constants.get(d.eq_ids[node['children'][0]])
        if other is None:return False
        d=other.d;idx=other.type()
        for _ in range(argc):
            node=d.nodes[idx]
            if node['tag']!=7:return False
            idx=node['children'][2]
        node=d.nodes[idx]
        return node['tag']==3 and d.nodes[node['children'][0]]['tag']==0

    def maps(self,roots,private):
        order,state=self.imports(roots,private);constants={};public={};owners={}
        selected=[];owner_names={}
        for name in order:
            rec=state[name];main=rec['module'] if rec['data'] else rec['ir']
            if main is None:raise InvalidArtifact('missing data file for module '+name)
            selected.append((name,rec,main))
        for name,rec,main in selected:
            # finalizeImport resolves interpreter metadata even when the caller
            # only observes constant maps. Preserve its missing-IR failure.
            interp=main if (not private and rec['irphase']=='runtime') or not main.modern else rec['ir']
            if interp is None:raise InvalidArtifact('missing IR data file for module '+name)
        for name,rec,main in selected:
            for key,ref,_ in main.entries(rec['all'] and rec['data']):
                old=constants.get(key)
                if old is None:constants[key]=ref
                elif self.subsumes(ref,old,constants):constants[key]=ref
                elif not self.subsumes(old,ref,constants):
                    declared=Renderer(ref.d).name_string(ref.name)
                    raise InvalidArtifact("import "+name+" failed, environment already contains '"+declared+"' from "+owners[key])
                owners.setdefault(key,name)
                owner_names.setdefault(key, (int.from_bytes(ref.d.nodes[ref.name]['scalars'], 'little') if ref.d.nodes[ref.name]['tag'] else 1723, tuple(Renderer(ref.d).components(ref.name))))
            ir = rec['ir']
            if ir is not None:
                for ptr in ir.d.parts.array(ir.data(False)[3]):
                    idx = ir.d.decode('Name',ptr);key = ir.d.eq_ids[idx]
                    owners.setdefault(key,name)
                    owner_names.setdefault(key,(int.from_bytes(ir.d.nodes[idx]['scalars'],'little') if ir.d.nodes[idx]['tag'] else 1723, tuple(Renderer(ir.d).components(idx))))
        self.owners=owners;self.owner_names=owner_names
        if not private:
            for name in order:
                rec=state[name]
                if not rec['export']:continue
                module=rec['module'] if rec['data'] else rec['ir']
                if module is None:continue
                for key,ref,_ in module.entries(False):
                    old=public.get(key)
                    if old is None or self.subsumes(ref,old,public):public[key]=ref
        return constants if private else public,order,state
