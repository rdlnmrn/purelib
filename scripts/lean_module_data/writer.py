"""Bounded pinned compact writer: ordinary bytes only, no runtime pointers.

Supports the actual kernel-data constructor/array/string/GMP graph. Rejects
closures, thunks, tasks, refs and other runtime objects. Cached scalar bytes are
copied exactly for unchanged graphs; changing Expr/Level structure is unsupported.
"""
import struct
from pathlib import Path
from .compact import InvalidArtifact
from .observations import name_hash
class Writer:
 def __init__(self, header, base):
  if base%65536:raise InvalidArtifact('unaligned synthetic base')
  self.base=base;self.data=bytearray(header[:80]+struct.pack('<QQ',base,0));self.memo={};self.active=set()
 def add(self,raw):
  off=len(self.data);self.data.extend(raw);self.data.extend(b'\0'*(-len(self.data)%8));return self.base+off
 def ctor(self,tag,fields,scalar=b''):
  size=(8+len(fields)*8+len(scalar)+7)//8*8
  if tag>=244 or len(fields)>255 or size>65535:raise InvalidArtifact('unsupported constructor bounds')
  return self.add(struct.pack('<IHBB',0,size,len(fields),tag)+b''.join(struct.pack('<Q',f) for f in fields)+scalar)
 def array(self,fields):return self.add(b'\0\0\0\0\1\0\0\xf6'+struct.pack('<QQ',len(fields),len(fields))+b''.join(struct.pack('<Q',f) for f in fields))
 def list(self,items):
  result=1
  for item in reversed(items):result=self.ctor(1,[item,result])
  return result
 def string(self,text):
  raw=text.encode('utf8')+b'\0';return self.add(b'\0\0\0\0\1\0\0\xf9'+struct.pack('<QQQ',len(raw),len(raw),len(text))+raw)
 def name_str(self,prefix,components,text):
  return self.ctor(1,[prefix,self.string(text)],struct.pack('<Q',name_hash(tuple(components)+((1,text),))))
 def clone(self,parts,ptr):
  if ptr&1:return ptr
  root=(id(parts),ptr);tasks=[(ptr,None)]
  while tasks:
   current,desc=tasks.pop();key=(id(parts),current)
   if key in self.memo:continue
   if desc is None:
    if current&1:self.memo[key]=current;continue
    if key in self.active:raise InvalidArtifact('cyclic serialized object')
    r,o=parts.locate(current);rc,size,count,tag=struct.unpack('<IHBB',r.bytes(o,8))
    if rc:raise InvalidArtifact('noncompact RC')
    if tag<244:
     if size<8+count*8 or size%8:raise InvalidArtifact('invalid constructor size')
     children=[r.u64(o+8+i*8) for i in range(count)];raw=r.bytes(o,size);kind='ctor'
    elif tag==246:
     children=list(parts.array(current));raw=None;kind='array'
    elif tag==249:
     size,cap,length=[r.u64(o+i) for i in (8,16,24)]
     if size!=cap or size==0:raise InvalidArtifact('invalid compact string')
     raw=r.bytes(o,32+size);children=[];kind='raw'
    elif tag==250:
     alloc,signed,limb=struct.unpack('<iiQ',r.bytes(o+8,16));n=abs(signed)
     if alloc!=n or limb!=current+24 or size!=((24+8*n)&65535):raise InvalidArtifact('invalid GMP object')
     raw=r.bytes(o,24+8*n);children=[];kind='mpz'
    else:raise InvalidArtifact('unsupported serialized runtime tag '+str(tag))
    self.active.add(key);tasks.append((current,(kind,raw,children)))
    for child in reversed(children):
     if (id(parts),child) not in self.memo:tasks.append((child,None))
   else:
    kind,raw,children=desc;fields=[self.memo[(id(parts),c)] for c in children]
    if kind=='array':new=self.array(fields)
    elif kind=='ctor':
     rewritten=bytearray(raw)
     for i,field in enumerate(fields):struct.pack_into('<Q',rewritten,8+i*8,field)
     new=self.add(rewritten)
    elif kind=='mpz':
     rewritten=bytearray(raw);struct.pack_into('<Q',rewritten,16,self.base+len(self.data)+24);new=self.add(rewritten)
    else:new=self.add(raw)
    self.memo[key]=new;self.active.remove(key)
  return self.memo[root]
 def write(self,path,root):
  struct.pack_into('<Q',self.data,88,root);Path(path).parent.mkdir(parents=True,exist_ok=True);Path(path).write_bytes(self.data)

# Pinned expression/universe caches for newly constructed probe constants.
MASK=(1<<64)-1
M=0xc6a4a7935bd1e995
def mix_hash(h,k):
 k=k*M&MASK;k^=k>>47;k^=M
 return ((h^k)*M)&MASK

def probe_constant(w, original):
 """Exact .const oldName (old levelParams.map Level.param), with full caches."""
 from .observations import name_observer
 names=original.d.list_items(original.levels());level_nodes=[];level_hashes=[]
 # Locate retained raw Name pointers from the original universe-name list.
 raw_list=original.base[1]
 while raw_list!=1:
  _,_,fields=original.d.parts.ctor(raw_list,1,2,0)
  ptr,raw_list=fields;idx=original.d.decode('Name',ptr);hash_=name_observer(original.d,idx)[0]
  h=mix_hash(2239,hash_)&0xffffffff
  level_nodes.append(w.ctor(4,[w.clone(original.d.parts,ptr)],struct.pack('<Q',h|(1<<33))))
  level_hashes.append(h)
 levels=w.list(level_nodes);list_hash=7
 for h in level_hashes:list_hash=mix_hash(list_hash,h)
 name=w.clone(original.d.parts,original.base[0]);name_hash_=name_observer(original.d,original.name)[0]
 data=mix_hash(5,mix_hash(name_hash_,list_hash))&0xffffffff
 if names:data|=1<<43
 return w.ctor(4,[name,levels],struct.pack('<Q',data))
