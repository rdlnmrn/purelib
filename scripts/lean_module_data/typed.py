"""Private checked decoder for the pinned v4.32.2 compact kernel data.

No native pointer access, compiler reader, recursion-depth limit or guessed default.
The iterative typed graph retains cached bytes separately from structural identity.
"""
import struct
from pathlib import Path
from . import compact as stage_a
InvalidArtifact=stage_a.InvalidArtifact

# Pointer fields in runtime order, followed by scalar bytes. The pinned kernel
# accessor sources bind these layouts independently of declaration field order.
RECORDS={
 'ConstantVal':(('Name','List:Name','Expr'),0),
 'AxiomVal':(('ConstantVal',),1),
 'DefinitionVal':(('ConstantVal','Expr','Hints','List:Name'),1),
 'TheoremVal':(('ConstantVal','Expr','List:Name'),0),
 'OpaqueVal':(('ConstantVal','Expr','List:Name'),1),
 'InductiveVal':(('ConstantVal','Nat','Nat','List:Name','List:Name','Nat'),3),
 'ConstructorVal':(('ConstantVal','Name','Nat','Nat','Nat'),1),
 'RecursorRule':(('Name','Nat','Expr'),0),
 'RecursorVal':(('ConstantVal','List:Name','Nat','Nat','Nat','Nat','List:RecursorRule'),2),
 'QuotVal':(('ConstantVal',),1),
 'Substring':(('String','Nat','Nat'),0),
 'Constructor':(('Name','Expr'),0),
 'InductiveType':(('Name','Expr','List:Constructor'),0),
 'GroupTail':(('Nat','List:InductiveType'),0),
 'GroupInputs':(('List:Name','GroupTail'),0),
 'ReplayPackets':(('Array:GroupInputs','Array:Declaration'),0),
}
INFO=('AxiomVal','DefinitionVal','TheoremVal','OpaqueVal','QuotVal','InductiveVal','ConstructorVal','RecursorVal')
EXPRS=(('Nat',),('Name',),('Name',),('Level',),('Name','List:Level'),('Expr','Expr'),('Name','Expr','Expr'),('Name','Expr','Expr'),('Name','Expr','Expr','Expr'),('Literal',),('KVMap','Expr'),('Name','Nat','Expr'))

def raw_substring(string,start,stop):
 """Pinned lean_string_utf8_extract observer, including Raw invalid positions."""
 # Pinned runtime/object.cpp returns the original string for a non-scalar
 # position; ordinary Nat factories box every value beyond pointer scalar range.
 if start>(1<<63)-1 or stop>(1<<63)-1: return string
 data=string.encode('utf8'); size=len(data)
 if start>=stop or start>=size: return ''
 if data[start]&0xc0==0x80: return ''
 stop=min(stop,size)
 if stop<size and data[stop]&0xc0==0x80: stop=size
 return data[start:stop].decode('utf8','strict')

def substring_equal_observer(string,start,stop):
 """Original Substring.Raw.beq repairs each invalid endpoint to String end."""
 data=string.encode('utf8');size=len(data)
 def valid(pos):return pos<=size and (pos==size or data[pos]&0xc0!=0x80)
 begin=start if valid(start) else size
 end=stop if valid(stop) else size
 return data[begin:end].decode('utf8','strict')

class TypedDecoder:
 def __init__(self, paths):
  self.parts=stage_a.ModuleParts()
  for path in paths: self.parts.add(path)
  self.cache={}; self.active=set(); self.nodes=[]; self.identities={}; self.raw_objects={}; self.eq_ids=[]; self.eq_identities={}; self.name_payload_ids=[]; self.name_payloads={}

 def header(self, ptr):
  r,o=self.parts.locate(ptr)
  return r,o,struct.unpack('<IHBB',r.bytes(o,8))

 def ctor(self, ptr, tag, types, scalar_size):
  r,s,fields=self.parts.ctor(ptr,tag,len(types),scalar_size)
  return tuple(zip(types,fields)),r.bytes(s,scalar_size)

 def integer(self, ptr, signed_type=False):
  if ptr&1:
   value=ptr>>1
   if signed_type:
    # lean_scalar_to_int64 casts the unboxed payload to unsigned 32-bit,
    # then signed int; this differs from Nat's pointer-sized immediate.
    value&=0xffffffff
    return value-(1<<32) if value&(1<<31) else value
   return value
  r,o,(rc,size,count,tag)=self.header(ptr)
  if rc!=0 or count!=0 or tag!=250:
   raise InvalidArtifact('wrong compact GMP natural header')
  # GMP LP64 __mpz_struct: int alloc, int signed size, limb pointer. Lean's
  # compact-pinned.cpp copies this object and inlines its unsigned 64-bit limbs.
  alloc,signed,limbptr=struct.unpack('<iiQ',r.bytes(o+8,16))
  n=abs(signed)
  if signed<0 and not signed_type or alloc!=n or limbptr!=ptr+24:
   raise InvalidArtifact('invalid compact GMP natural fields')
  full_size=24+8*n
  if size!=(full_size & 65535):
   raise InvalidArtifact('invalid compact GMP natural size')
  data=r.bytes(o+24,8*n)
  if n and int.from_bytes(data[-8:],'little')==0:
   raise InvalidArtifact('noncanonical compact GMP natural')
  value=int.from_bytes(data,'little')
  return -value if signed<0 else value

 def string(self, ptr):
  r,o=self.parts.locate(ptr)
  if r.bytes(o,8)!=b'\0\0\0\0\x01\0\0\xf9':
   raise InvalidArtifact('wrong string header')
  size,capacity,length=(r.u64(o+i) for i in (8,16,24))
  if not size or capacity!=size: raise InvalidArtifact('invalid string capacity')
  raw=r.bytes(o+32,size)
  if raw[-1:]!=b'\0': raise InvalidArtifact('invalid string final terminator')
  value=raw[:-1].decode('utf8','strict')
  # Embedded NUL is valid in general kernel String data, unlike import names.
  if len(value)!=length: raise InvalidArtifact('invalid UTF8 character count')
  return value

 def descriptor(self, kind, ptr):
  """Return tag, typed child requests, exact scalar payload and atom value."""
  if kind=='Nat': return 0,(),b'',self.integer(ptr)
  if kind=='Int': return 0,(),b'',self.integer(ptr,True)
  if kind=='String': return 0,(),b'',self.string(ptr)
  if kind=='KVMap': return 0,(("List:Pair:Name:DataValue",ptr),),b'',None
  if kind=='Bool':
   if ptr not in (1,3): raise InvalidArtifact('invalid Bool scalar')
   return ptr>>1,(),b'',bool(ptr>>1)
  if kind.startswith('List:'):
   if ptr==1: return 0,(),b'',None
   types=(kind[5:],kind); children,scalar=self.ctor(ptr,1,types,0)
   return 1,children,scalar,None
  if kind.startswith('Array:'):
   return 0,tuple((kind[6:],p) for p in self.parts.array(ptr)),b'',None
  if kind=='Pair:Name:DataValue':
   children,scalar=self.ctor(ptr,0,('Name','DataValue'),0)
   return 0,children,scalar,None
  if kind=='Name' and ptr==1: return 0,(),b'',None
  if kind=='Level' and ptr==1: return 0,(),b'',None
  if kind=='Syntax' and ptr==1: return 0,(),b'',None
  if kind=='SourceInfo' and ptr==5: return 2,(),b'',None
  if kind=='Declaration' and ptr==9: return 4,(),b'',None
  if kind=='Hints' and ptr in (1,3): return ptr>>1,(),b'',None
  r,o,header=self.header(ptr); tag=header[3]
  if kind=='Name':
   if tag not in (1,2): raise InvalidArtifact('invalid Name constructor')
   types=('Name','String' if tag==1 else 'Nat'); size=8
  elif kind=='Level':
   choices={1:('Level',),2:('Level','Level'),3:('Level','Level'),4:('Name',),5:('Name',)}
   if tag not in choices: raise InvalidArtifact('invalid Level constructor')
   types=choices[tag]; size=8
  elif kind=='Expr':
   if tag>=len(EXPRS): raise InvalidArtifact('invalid Expr constructor')
   types=EXPRS[tag]; size=9 if tag in (6,7,8) else 8
  elif kind=='Int':
   if tag not in (0,1): raise InvalidArtifact('invalid Int constructor')
   types=('Nat',); size=0
  elif kind=='Literal':
   if tag not in (0,1): raise InvalidArtifact('invalid Literal constructor')
   types=('Nat' if tag==0 else 'String',); size=0
  elif kind=='ConstantInfo':
   if tag>=8: raise InvalidArtifact('invalid ConstantInfo constructor')
   types=(INFO[tag],); size=0
  elif kind=='Declaration':
   choices={0:(('AxiomVal',),0),1:(('DefinitionVal',),0),2:(('TheoremVal',),0),3:(('OpaqueVal',),0),5:(('List:DefinitionVal',),0),6:(('List:Name','Nat','List:InductiveType'),1)}
   if tag not in choices: raise InvalidArtifact('invalid Declaration constructor')
   types,size=choices[tag]
  elif kind=='Hints':
   if tag!=2: raise InvalidArtifact('invalid ReducibilityHints constructor')
   types=(); size=4
  elif kind=='DataValue':
   choices={0:('String',),1:(),2:('Name',),3:('Nat',),4:('Int',),5:('Syntax',)}
   if tag not in choices: raise InvalidArtifact('invalid DataValue constructor')
   types=choices[tag]; size=1 if tag==1 else 0
  elif kind=='Syntax':
   choices={1:('SourceInfo','Name','Array:Syntax'),2:('SourceInfo','String'),3:('SourceInfo','Substring','Name','List:Preresolved')}
   if tag not in choices: raise InvalidArtifact('invalid Syntax constructor')
   types=choices[tag]; size=0
  elif kind=='SourceInfo':
   choices={0:('Substring','Nat','Substring','Nat'),1:('Nat','Nat')}
   if tag not in choices: raise InvalidArtifact('invalid SourceInfo constructor')
   types=choices[tag]; size=1 if tag==1 else 0
  elif kind=='Preresolved':
   if tag not in (0,1): raise InvalidArtifact('invalid Preresolved constructor')
   types=('Name',) if tag==0 else ('Name','List:String'); size=0
  elif kind in RECORDS:
   if tag!=0: raise InvalidArtifact('invalid record constructor: '+kind)
   types,size=RECORDS[kind]
  else: raise InvalidArtifact('unrecognized typed schema: '+kind)
  children,scalar=self.ctor(ptr,tag,types,size)
  bool_positions={'AxiomVal':(0,), 'OpaqueVal':(0,), 'InductiveVal':(0,1,2), 'ConstructorVal':(0,), 'RecursorVal':(0,1), 'SourceInfo':(0,) if tag==1 else (), 'DataValue':(0,) if tag==1 else (), 'Expr':(8,) if tag==8 else ()}
  if any(scalar[i] not in (0,1) for i in bool_positions.get(kind,())):
   raise InvalidArtifact('invalid scalar Bool in '+kind)
  if kind=='Declaration' and tag==6 and scalar[0]>1: raise InvalidArtifact('invalid inductive Declaration Bool')
  if kind=='Expr' and tag in (6,7) and scalar[8]>3: raise InvalidArtifact('invalid BinderInfo')
  if kind=='DefinitionVal' and scalar[0]>2: raise InvalidArtifact('invalid DefinitionSafety')
  if kind=='QuotVal' and scalar[0]>3: raise InvalidArtifact('invalid QuotKind')
  return tag,children,scalar,None

 def decode(self, kind, ptr):
  root=(kind,ptr); tasks=[(root,None)]
  while tasks:
   key,desc=tasks.pop()
   if key in self.cache: continue
   if desc is None:
    if key in self.active: raise InvalidArtifact('cyclic typed compact object graph')
    desc=self.descriptor(*key); self.active.add(key)
    tasks.append((key,desc))
    for child in reversed(desc[1]):
     if child not in self.cache: tasks.append((child,None))
   else:
    tag,requests,scalar,atom=desc
    children=tuple(self.cache[c] for c in requests)
    self.raw_objects[key]={"tag":tag,"children":requests,"scalars":scalar,"value":atom}
    # Expr equality observes its hash, but does not compare the other computed
    # cache bits. Level equality likewise tests hash before logical structure.
    identity_scalar=scalar
    if key[0] in ('Expr','Level'): identity_scalar=scalar[:4]+scalar[8:]
    identity=(key[0],tag,children,identity_scalar,atom)
    idx=self.identities.get(identity)
    if idx is None:
     idx=len(self.nodes); self.identities[identity]=idx
     self.nodes.append({'kind':key[0],'tag':tag,'children':children,'scalars':scalar,'value':atom})
     eq_children=tuple(self.eq_ids[i] for i in children)
     eq_atom=atom
     name_payload=None
     if key[0]=='Name':
      # lean_name_eq guards the root hash, then compares prefix components
      # without consulting hashes of physically different inner prefixes.
      payload=(tag,(self.name_payload_ids[children[0]],self.eq_ids[children[1]])) if children else (tag,())
      name_payload=self.name_payloads.setdefault(payload,len(self.name_payloads))
      eq_children=()
      eq_atom=name_payload
     self.name_payload_ids.append(name_payload)
     if key[0]=='Syntax' and tag:
      eq_children=eq_children[1:]
     if key[0]=='Substring':
      string,start,stop=(self.nodes[i]['value'] for i in children)
      eq_atom=substring_equal_observer(string,start,stop)
      eq_children=()
     eq_key=(key[0],tag,eq_children,identity_scalar,eq_atom)
     eq_id=self.eq_identities.setdefault(eq_key,len(self.eq_identities))
     self.eq_ids.append(eq_id)
    self.cache[key]=idx; self.active.remove(key)
  return self.cache[root]

 def list_items(self, idx):
  values=[]
  while self.nodes[idx]['tag']==1:
   head,idx=self.nodes[idx]['children']; values.append(head)
  return values

 def module(self, region):
  r,s,f=self.parts.ctor(region.root,0,5,1)
  flag=r.bytes(s,1)[0]
  if flag not in (0,1): raise InvalidArtifact('invalid ModuleData.isModule')
  return {'is_module':bool(flag),'const_names':self.decode('Array:Name',f[1]),'constants':self.decode('Array:ConstantInfo',f[2]),'imports_ptr':f[0],'extra_names_ptr':f[3],'extension_ptr':f[4]}
