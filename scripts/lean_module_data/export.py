"""Pinned lean4export 3.1.0 serialization of certified compiled artifacts.

This command reads retained private module data. It deliberately executes no
module initializer or callback. It is an untrusted serializer, not a checker.
"""
from collections import deque
from functools import cmp_to_key
from pathlib import Path
import sys
import time
from .format import decimal
from .compact import inventory, InvalidArtifact, VERSION, PIN
from .contracts import dumps
from .observations import name_observer, query_observer, quick_cmp
from .audit import AuditObservation
from .audit_metadata import RootMetadata, audit_root, unsafe
from .render import Renderer
from .writer import mix_hash


def log(message):
    print(message,file=sys.stderr,flush=True)


def milliseconds(start):return (time.monotonic_ns()-start)//1000000


def drive(call):
    """Execute nested finite serialization generators without Python recursion."""
    stack=[call]; value=None
    while stack:
        try:
            child=stack[-1].send(value); value=None; stack.append(child)
        except StopIteration as done:
            stack.pop(); value=done.value
    return value


class Environment:
    """Exact private constant map, first owners and persisted meta registrations."""
    def __init__(self, modules, search):
        self.observation=AuditObservation(modules,search)
        self.graph=self.observation.graph
        self.constants,self.order,self.state=self.observation.constants,self.observation.order,self.observation.state
        self.root_metadata=RootMetadata(self.observation)
        self.names={};self.by_name={};self.meta={};self.recs={};self.alpha_memo={};self.alpha_ids={}
        for key,r in self.constants.items():
            self.names[key]=name_observer(r.d,r.name);self.by_name[self.names[key]]=key
        for r in self.constants.values():
            if r.kind==7:
                d=r.d
                for idx in d.list_items(d.decode('List:Name',r.fields[1])):
                    self.recs.setdefault(d.eq_ids[idx],set()).add(r.key)
    def alpha(self,d,root):
        tasks=[(root,False)]
        while tasks:
            idx,post=tasks.pop(); cache=(id(d),idx)
            if cache in self.alpha_memo:continue
            n=d.nodes[idx];children=n['children'];tag=n['tag']
            if not post:
                tasks.append((idx,True));tasks.extend((i,False)for i in reversed(children)if d.nodes[i]['kind']=='Expr');continue
            observed=tuple(self.alpha_memo[(id(d),i)]if d.nodes[i]['kind']=='Expr'else ('raw',d.eq_ids[i])for i in children)
            if tag in (6,7,8):observed=observed[1:]
            scalar=n['scalars'][:4]+(n['scalars'][8:]if tag==8 else b'')
            key=(tag,observed,scalar);self.alpha_memo[cache]=self.alpha_ids.setdefault(key,len(self.alpha_ids))
        return self.alpha_memo[(id(d),root)]
    def text(self,key):
        r=self.constants[key];return Renderer(r.d).name_string(r.name)
    def sorted(self, keys):
        return sorted(keys,key=cmp_to_key(lambda a,b:quick_cmp(self.names[a],self.names[b])))
    def named(self,text): return self.by_name.get(query_observer(text))
    def roots(self, modules):
        """Select exactly the audit's source roots and registered compiler rewrites."""
        roots=[];aux=[];seen=set()
        for module in modules:
            names,_=self.observation.inventory(module)
            for name in names:
                r=self.observation.by_name.get(name)
                if r is None:continue
                identity=(module,r.key)
                if identity in seen:continue
                seen.add(identity)
                if audit_root(name,r,self.root_metadata):
                    roots.append((module,r.key))
                elif r.kind==1 and r.scalar[0]==2 and self.text(r.key).endswith('._unsafe_rec'):
                    aux.append((module,r.key))
        return roots,aux


class Serializer:
    """Original postorder IDs, recursive dependency order and atomic groups."""
    def __init__(self,env,handle):
        self.env=env;self.handle=handle;self.bytes=0;self.names={};self.levels={};self.exprs={};self.visited=set()
        self.normal={};self.normal_ids={};self.normal_nodes=[]
    def emit(self,obj):
        raw=(dumps(obj)+'\n').encode('utf8');self.handle.write(raw);self.bytes+=len(raw)
    def name(self,d,idx):
        n=d.nodes[idx]
        if not n['tag']:return 0
        key=d.eq_ids[idx]
        if key in self.names:return self.names[key]
        pre=yield self.name(d,n['children'][0]);value=d.nodes[n['children'][1]]['value']
        payload={'str':{'pre':pre,'str':value}} if n['tag']==1 else {'num':{'pre':pre,'i':value}}
        result=len(self.names)+1;payload['in']=result;self.emit(payload);self.names[key]=result;return result
    def level(self,d,idx):
        n=d.nodes[idx];tag=n['tag'];c=n['children']
        if tag==0:return 0
        key=('param',d.eq_ids[c[0]]) if tag==4 and int.from_bytes(n['scalars'][:4],'little')==(mix_hash(2239,name_observer(d,c[0])[0])&0xffffffff) else ('raw',d.eq_ids[idx])
        if key in self.levels:return self.levels[key]
        if tag==1:payload={'succ':(yield self.level(d,c[0]))}
        elif tag in (2,3):
            a=yield self.level(d,c[0]);b=yield self.level(d,c[1]);payload={('max' if tag==2 else 'imax'):[a,b]}
        elif tag==4:payload={'param':(yield self.name(d,c[0]))}
        else:raise InvalidArtifact('cannot export level metavariables')
        result=len(set(self.levels.values()))+1;payload['il']=result;self.emit(payload);self.levels[key]=result
        if tag==4:self.levels[('param',d.eq_ids[c[0]])]=result
        return result
    def param(self,d,idx):
        key=('param',d.eq_ids[idx])
        if key in self.levels:return self.levels[key]
        result=len({v for v in self.levels.values()})+1
        self.emit({'param':(yield self.name(d,idx)),'il':result});self.levels[key]=result;return result
    def names_list(self,d,idx):
        result=[]
        for item in d.list_items(idx):result.append((yield self.name(d,item)))
        return result
    def uparams(self,d,idx):
        result=yield self.names_list(d,idx)
        for item in d.list_items(idx):yield self.param(d,item)
        return result
    def normalize(self,d,idx):
        """Original removeMData with complete ancestor cache recalculation."""
        tasks=[(idx,False)];memo={}
        while tasks:
            i,post=tasks.pop()
            if i in memo:continue
            n=d.nodes[i];tag=n['tag'];c=n['children']
            ec=[j for j in c if d.nodes[j]['kind']=='Expr']
            if not post:
                tasks.append((i,True));tasks.extend((j,False)for j in reversed(ec)if j not in memo);continue
            if tag in (1,2):raise InvalidArtifact('cannot export free variables or metavariables')
            if tag==10:memo[i]=(memo[c[1]][0],True);continue
            children=tuple(('expr',memo[j][0])if d.nodes[j]['kind']=='Expr' else ('raw',d.eq_ids[j])for j in c)
            data=int.from_bytes(n['scalars'][:8],'little');childdata=[self.normal_nodes[memo[j][0]][3]for j in ec]
            changed=any(memo[j][1] for j in ec)or(tag==8 and bool(n['scalars'][8]))
            if changed:
                depth=lambda a:(a>>32)&255;rg=lambda a:a>>44
                flags=0
                for a in childdata:flags|=a&(15<<40)
                if tag==5:
                    a,b=childdata;data=(mix_hash(a,b)&0xffffffff)|(min(255,max(depth(a),depth(b))+1)<<32)|(max(rg(a),rg(b))<<44)|flags
                elif tag in (6,7,8):
                    dep=max(map(depth,childdata))+1
                    if tag in (6,7):a,b=childdata;h=mix_hash(dep,mix_hash(a&0xffffffff,b&0xffffffff));r=max(rg(a),max(0,rg(b)-1))
                    else:a,v,b=childdata;h=mix_hash(dep,mix_hash(a&0xffffffff,mix_hash(v&0xffffffff,b&0xffffffff)));r=max(rg(a),rg(v),max(0,rg(b)-1))
                    data=(h&0xffffffff)|(min(255,dep)<<32)|(r<<44)|flags
                elif tag==11:
                    a=childdata[0];dep=depth(a)+1;h=mix_hash(name_observer(d,c[0])[0],mix_hash(d.nodes[c[1]]['value']&((1<<64)-1),a&0xffffffff));data=(mix_hash(dep,h)&0xffffffff)|(min(255,dep)<<32)|(rg(a)<<44)|flags
                else:raise InvalidArtifact('unexpected changed expression kind')
            extra=b'\0' if tag==8 else n['scalars'][8:]
            key=(tag,children[1:] if tag in (6,7,8) else children,data&0xffffffff,extra if tag==8 else b'')
            canonical=self.normal_ids.get(key)
            if canonical is None:
                canonical=len(self.normal_nodes);self.normal_ids[key]=canonical;self.normal_nodes.append((d,i,children,data,changed))
            memo[i]=(canonical,changed)
        return memo[idx][0]
    def expr(self,d,idx):
        return (yield self.expr_aux(self.normalize(d,idx)))
    def expr_aux(self,canonical):
        if canonical in self.exprs:return self.exprs[canonical]
        d,i,children,_,_=self.normal_nodes[canonical];n=d.nodes[i];tag=n['tag'];c=n['children']
        def ex(position):return self.expr_aux(children[position][1])
        if tag==0:payload={'bvar':d.nodes[c[0]]['value']}
        elif tag==3:payload={'sort':(yield self.level(d,c[0]))}
        elif tag==4:
            name=yield self.name(d,c[0]);levels=[]
            for l in d.list_items(c[1]):levels.append((yield self.level(d,l)))
            payload={'const':{'name':name,'us':levels}}
        elif tag==5:
            fn=yield ex(0);arg=yield ex(1);payload={'app':{'fn':fn,'arg':arg}}
        elif tag in (6,7,8):
            name=yield self.name(d,c[0]);typ=yield ex(1)
            if tag==8:
                val=yield ex(2);body=yield ex(3);payload={'letE':{'name':name,'type':typ,'value':val,'body':body,'nondep':False}}
            else:
                body=yield ex(2);payload={('lam'if tag==6 else 'forallE'):{'name':name,'type':typ,'body':body,'binderInfo':['default','implicit','strictImplicit','instImplicit'][n['scalars'][8]]}}
        elif tag==9:
            lit=d.nodes[c[0]];val=d.nodes[lit['children'][0]]['value']
            for text in (['Nat']if lit['tag']==0 else ['Char.ofNat','String.ofList']):
                key=self.env.named(text)
                if key is not None and key not in self.visited:yield self.constant(key)
            payload={'natVal':decimal(val)}if lit['tag']==0 else {'strVal':val}
        elif tag==11:
            name=yield self.name(d,c[0]);body=yield ex(2);payload={'proj':{'typeName':name,'idx':d.nodes[c[1]]['value'],'struct':body}}
        else:raise InvalidArtifact('unsupported export expression')
        result=len(self.exprs);payload['ie']=result;self.emit(payload);self.exprs[canonical]=result;return result
    def deps(self,d,idx):
        seen=set();seen_names=set();todo=[idx]
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i);n=d.nodes[i];tag=n['tag'];c=n['children']
            if tag==4:
                key=d.eq_ids[c[0]]
                if key not in seen_names:
                    seen_names.add(key);yield self.constant(key)
            todo.extend(reversed([j for j in c if d.nodes[j]['kind']=='Expr']))
    def record(self,r):
        d=r.d;f=r.fields;kind=r.kind
        obj={'name':(yield self.name(d,r.name)),'levelParams':(yield self.uparams(d,r.levels())),'type':(yield self.expr(d,r.type()))}
        if kind in (1,2,3):
            obj['value']=yield self.expr(d,d.decode('Expr',f[1]))
            if kind==1:
                hints=d.nodes[d.decode('Hints',f[2])];obj['hints']=['opaque','abbrev'][hints['tag']]if hints['tag']<2 else {'regular':int.from_bytes(hints['scalars'],'little')};obj['safety']=['unsafe','safe','partial'][r.scalar[0]]
            obj['all']=yield self.names_list(d,r.all())
        if kind in (0,3,5,6,7):obj['isUnsafe']=unsafe(r)
        if kind==4:obj['kind']=['type','ctor','lift','ind'][r.scalar[0]]
        if kind==5:
            for field,pos in [('numParams',1),('numIndices',2),('numNested',5)]:obj[field]=d.nodes[d.decode('Nat',f[pos])]['value']
            obj['all']=yield self.names_list(d,d.decode('List:Name',f[3]));obj['ctors']=yield self.names_list(d,d.decode('List:Name',f[4]));obj['isRec']=bool(r.scalar[0]);obj['isReflexive']=bool(r.scalar[2])
        if kind==6:
            obj['induct']=yield self.name(d,d.decode('Name',f[1]))
            for field,pos in [('cidx',2),('numParams',3),('numFields',4)]:obj[field]=d.nodes[d.decode('Nat',f[pos])]['value']
        if kind==7:
            obj['all']=yield self.names_list(d,d.decode('List:Name',f[1]))
            for field,pos in [('numParams',2),('numIndices',3),('numMotives',4),('numMinors',5)]:obj[field]=d.nodes[d.decode('Nat',f[pos])]['value']
            rules=[]
            for rule in d.list_items(d.decode('List:RecursorRule',f[6])):
                cc=d.nodes[rule]['children'];ctor=yield self.name(d,cc[0]);rhs=yield self.expr(d,cc[2]);rules.append({'ctor':ctor,'nfields':d.nodes[cc[1]]['value'],'rhs':rhs})
            obj['rules']=rules;obj['k']=bool(r.scalar[0])
        return obj
    def constant(self,key):
        r=self.env.constants.get(key)
        if r is None:raise InvalidArtifact('Constant not found in environment: '+str(key))
        if unsafe(r)or key in self.visited:return
        self.visited.add(key);d=r.d;kind=r.kind
        if kind==6:yield self.constant(d.eq_ids[d.decode('Name',r.fields[1])]);return
        if kind==7:
            for idx in d.list_items(d.decode('List:Name',r.fields[1])):yield self.constant(d.eq_ids[idx])
            return
        if kind==4:
            yield self.constant(self.env.named('Eq'))
            for text in ['Quot','Quot.mk','Quot.lift','Quot.ind']:
                k=self.env.named(text);self.visited.add(k);self.emit({'quot':(yield self.record(self.env.constants[k]))})
            return
        if kind==5:
            inds=[];ctors=[];recs=[];rec_names=set()
            for idx in d.list_items(d.decode('List:Name',r.fields[3])):
                ind=self.env.constants[d.eq_ids[idx]];inds.append(ind);di=ind.d
                ctors.extend(self.env.constants[di.eq_ids[j]]for j in di.list_items(di.decode('List:Name',ind.fields[4])))
                self.visited.add(ind.key);yield self.deps(di,ind.type());rec_names.update(self.env.recs.get(key,()))
            for ctor in ctors:self.visited.add(ctor.key);yield self.deps(ctor.d,ctor.type())
            for k in self.env.sorted(rec_names):recs.append(self.env.constants[k])
            for rec in recs:self.visited.add(rec.key);yield self.deps(rec.d,rec.type())
            for rec in recs:
                for rule in rec.d.list_items(rec.d.decode('List:RecursorRule',rec.fields[6])):yield self.deps(rec.d,rec.d.nodes[rule]['children'][2])
            arrays=[]
            for values in [inds,ctors,recs]:
                array=[]
                for value in values:array.append((yield self.record(value)))
                arrays.append(array)
            self.emit({'inductive':dict(zip(['types','ctors','recs'],arrays))});return
        yield self.deps(d,r.type())
        if kind in (1,2,3):yield self.deps(d,d.decode('Expr',r.fields[1]))
        self.emit({['axiom','def','thm','opaque'][kind]:(yield self.record(r))})
    def metadata(self):
        self.emit({'meta':{'exporter':{'name':'lean4export','version':'3.1.0'},'format':{'version':'3.1.0'},'lean':{'version':VERSION.decode(),'githash':PIN.decode()}}})


def manifest(path):
    contents=Path(path).read_bytes().decode('utf8','strict')
    names=[line.strip(' \t\r\n\v\f')for line in contents.split('\n')if line.strip(' \t\r\n\v\f')]
    if not names:raise ValueError('nanoda module manifest is empty: '+str(path))
    from .paths import parse_name,render_name
    return [render_name(parse_name(n))for n in names]


def publish(path,data):
    path=Path(path);pending=Path(str(path)+'.partial');pending.write_bytes(data);pending.replace(path)


def pairs(env,values):return [{'owner':m,'name':env.text(k)}for m,k in values]


def graph_node(env,key):
    r=env.constants.get(key)
    if r is None:raise ValueError('nanoda graph: unresolved declaration '+str(key))
    if unsafe(r):raise ValueError('nanoda graph: unsafe dependency '+env.text(key))
    d=r.d;exprs=[r.base[2]];group=[];special=[];scan=True
    if r.kind in (1,2,3):exprs.append(r.fields[1])
    elif r.kind==5:
        group=[d.eq_ids[i]for i in d.list_items(d.decode('List:Name',r.fields[3]))]
        for k in list(group):
            ind=env.constants[k];group.extend(ind.d.eq_ids[i]for i in ind.d.list_items(ind.d.decode('List:Name',ind.fields[4])))
        group+=env.sorted(env.recs.get(key,()))
    elif r.kind==6:group=[d.eq_ids[d.decode('Name',r.fields[1])]]
    elif r.kind==7:
        group=[d.eq_ids[i]for i in d.list_items(d.decode('List:Name',r.fields[1]))]
        for rule_ptr in raw_list(d,r.fields[6]):
            _,_,f=d.parts.ctor(rule_ptr,0,3,0);exprs.append(f[2])
    elif r.kind==4:group=[env.named(n)for n in ['Quot','Quot.mk','Quot.lift','Quot.ind']];special=[env.named('Eq')];scan=False
    deps=set();count=0
    for root in exprs:
        seen=set();todo=[root]
        while todo:
            ptr=todo.pop()
            identity=env.alpha(d,d.decode('Expr',ptr))
            if identity in seen:continue
            seen.add(identity);count+=1;tag,req,_,_=d.descriptor('Expr',ptr)
            if tag==4 and scan:deps.add(d.eq_ids[d.decode('Name',req[0][1])])
            elif tag==9:
                lit=d.decode('Literal',req[0][1]);taglit=d.nodes[lit]['tag']
                for text in (['Nat']if taglit==0 else ['Char.ofNat','String.ofList']):
                    k=env.named(text)
                    if k is not None:deps.add(k)
            todo.extend(p for kind,p in reversed(req)if kind=='Expr')
    deps.update(group+special);ordered=env.sorted(deps)
    return {'name':env.text(key),'owner':env.graph.owners.get(key),'dependencies':[env.text(k)for k in ordered],'atomic':[env.text(k)for k in group],'expression_estimate':count},ordered


def raw_list(d,ptr):
    while ptr!=1:
        _,_,(head,ptr)=d.parts.ctor(ptr,1,2,0);yield head


def export_graph(modules,output,search):
    started=time.monotonic_ns();env=Environment(modules,search);log(f'nanoda graph: import_ms={milliseconds(started)}');started=time.monotonic_ns();roots,aux=env.roots(modules);log(f'nanoda graph: setup_ms={milliseconds(started)}');started=time.monotonic_ns()
    pending=Path(str(output)+'.partial');seen=set();queue=deque(k for _,k in roots)
    with pending.open('wb')as handle:
        handle.write((dumps({'schema':1,'roots':pairs(env,roots),'runtime_auxiliaries':pairs(env,aux)})+'\n').encode())
        while queue:
            key=queue.popleft()
            if key in seen:continue
            seen.add(key);node,deps=graph_node(env,key);handle.write((dumps(node)+'\n').encode());queue.extend(k for k in deps if k not in seen)
        handle.flush()
    pending.replace(output)
    log(f'nanoda graph: roots={len(roots)} declarations={len(seen)} discovery_ms={milliseconds(started)}')


def main(args, search):
    """Expose only raw graph/header diagnostics; production streams use native export."""
    if args == ['--metadata']:
        Serializer(None, sys.stdout.buffer).metadata()
    elif len(args) == 3 and args[0] == '--module-inputs':
        roots = manifest(args[1])
        result, _ = inventory(roots, search)
        publish(args[2], (dumps(result) + '\n').encode())
    elif len(args) == 3 and args[0] == '--graph':
        export_graph(manifest(args[1]), Path(args[2]), search)
    else:
        raise ValueError('raw reader provides metadata, compiled input inventories and declaration graphs only')
