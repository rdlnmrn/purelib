"""Exact constant-only alias replacement, retaining structural fields and caches."""
import struct
from .writer import mix_hash
from .observations import name_observer
from .compact import InvalidArtifact
class Aliases:
 def __init__(self,w,aliases):
  self.w=w;self.aliases=dict(aliases);self.context=tuple(sorted((k,v) for k,v in aliases.items()));self.memo={};self.changed=[]
 def data(self,p):
  off=p-self.w.base;count=self.w.data[off+6]
  return struct.unpack_from('<Q',self.w.data,off+8+8*count)[0]
 def expr(self,d,root):
  tasks=[(root,False)]
  while tasks:
   ptr,post=tasks.pop();key=(id(d.parts),ptr,self.context)
   if key in self.memo:continue
   tag,req,scalar,_=d.descriptor('Expr',ptr)
   if not post:
    tasks.append((ptr,True))
    for kind,c in reversed(req):
     if kind=='Expr' and (id(d.parts),c,self.context) not in self.memo:tasks.append((c,False))
    continue
   changed=False;fields=[]
   for kind,c in req:
    if kind=='Expr':new,flag=self.memo[(id(d.parts),c,self.context)];changed|=flag;fields.append(new)
    else:fields.append(self.w.clone(d.parts,c))
   if tag==4:
    key_name=name_observer(d,d.decode('Name',req[0][1]));fresh=self.aliases.get(key_name)
    if fresh is not None:fields[0]=fresh;changed=True
   if not changed:self.memo[key]=(self.w.clone(d.parts,ptr),False);continue
   child=[self.data(fields[i]) for i,(k,_) in enumerate(req) if k=='Expr']
   hash32=lambda x:x&0xffffffff
   depth=lambda x:(x>>32)&255
   range_=lambda x:x>>44
   flags=lambda xs:__import__('functools').reduce(int.__or__,xs,0)&(15<<40)
   if tag==4:
    name_data=self.w.data[fields[0]-self.w.base:];count=name_data[6];h=struct.unpack_from('<Q',name_data,8+8*count)[0]
    levels=req[1][1];lh=7;fl=0
    while levels!=1:
     _,_,(lp,levels)=d.parts.ctor(levels,1,2,0)
     if lp==1:ld=2221
     else:
      _,req_l,sc,_=d.descriptor('Level',lp);ld=int.from_bytes(sc,'little')
     lh=mix_hash(lh,ld&0xffffffff);fl|=((ld>>32)&3)<<42
    data=hash32(mix_hash(5,mix_hash(h,lh)))|fl
   elif tag==5:
    a,b=child;data=hash32(mix_hash(a,b))|(min(255,max(depth(a),depth(b))+1)<<32)|(max(range_(a),range_(b))<<44)|flags(child)
   elif tag in (6,7,8):
    dep=max(map(depth,child))+1
    if tag in (6,7):a,b=child;h=mix_hash(dep,mix_hash(hash32(a),hash32(b)));r=max(range_(a),max(0,range_(b)-1))
    else:a,v,b=child;h=mix_hash(dep,mix_hash(hash32(a),mix_hash(hash32(v),hash32(b))));r=max(range_(a),range_(v),max(0,range_(b)-1))
    data=hash32(h)|(min(255,dep)<<32)|(r<<44)|flags(child)
   elif tag in (10,11):
    e=child[0];dep=depth(e)+1;h=hash32(e)
    if tag==11:
     n=name_observer(d,d.decode('Name',req[0][1]))[0];idx=d.integer(req[1][1]);h=mix_hash(n,mix_hash(idx&((1<<64)-1),h))
    data=hash32(mix_hash(dep,h))|(min(255,dep)<<32)|(range_(e)<<44)|flags(child)
   else:raise InvalidArtifact('changed nonrecursive/nonconstant expression')
   new=self.w.ctor(tag,fields,struct.pack('<Q',data)+scalar[8:]);self.changed.append({'tag':tag,'source':ptr,'result':new,'cache':data});self.memo[key]=(new,True)
  return self.memo[(id(d.parts),root,self.context)][0]
 def name(self,d,ptr):return self.aliases.get(name_observer(d,d.decode('Name',ptr)),self.w.clone(d.parts,ptr))
 def names(self,d,ptr):
  values=[]
  while ptr!=1:
   _,_,(n,ptr)=d.parts.ctor(ptr,1,2,0);values.append(self.name(d,n))
  return self.w.list(values)
 def info(self,r):
  if r.kind not in (1,2,3):raise InvalidArtifact('original asDeclaration rejects unsupported kind')
  base=self.w.ctor(0,[self.name(r.d,r.base[0]),self.w.clone(r.d.parts,r.base[1]),self.expr(r.d,r.base[2])]);fields=[base,self.expr(r.d,r.fields[1])]
  if r.kind==1:fields.append(self.w.clone(r.d.parts,r.fields[2]))
  fields.append(self.names(r.d,r.fields[-1]));return self.w.ctor(r.kind,[self.w.ctor(0,fields,r.scalar)])
