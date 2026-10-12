"""Private exact-schema2 candidate; reads only ordinary pinned artifact bytes."""
import argparse,json,time
from pathlib import Path
from .typed import TypedDecoder,InvalidArtifact
from .render import Renderer,derived
from .format import decimal,text,pretty

def json_quote(value):
 out=['"']
 for c in value:
  if c=='"': out.append('\\"')
  elif c=='\\': out.append('\\\\')
  elif c=='\n': out.append('\\n')
  elif c=='\r': out.append('\\r')
  elif ord(c)<32: out.append('\\u'+format(ord(c),'04x'))
  else: out.append(c)
 out.append('"'); return ''.join(out)

def dumps(value):
 """Core Json.compress object order and arbitrary natural decimal output."""
 out=[]; todo=[value]
 while todo:
  v=todo.pop()
  if isinstance(v,Raw): out.append(v.value)
  elif v is None: out.append('null')
  elif isinstance(v,bool): out.append('true' if v else 'false')
  elif isinstance(v,int): out.append(decimal(v))
  elif isinstance(v,str): out.append(json_quote(v))
  elif isinstance(v,list):
   todo.append(Raw(']'))
   for i in range(len(v)-1,-1,-1):
    todo.append(v[i])
    if i: todo.append(Raw(','))
   todo.append(Raw('['))
  elif isinstance(v,dict):
   keys=sorted(v); todo.append(Raw('}'))
   for i in range(len(keys)-1,-1,-1):
    k=keys[i]; todo.extend([v[k],Raw(':'),k])
    if i: todo.append(Raw(','))
   todo.append(Raw('{'))
  else: raise TypeError(type(v))
 return ''.join(out)
class Raw:
 def __init__(self,value): self.value=value

class Schema2:
 def __init__(self,d): self.d=d; self.r=Renderer(d); self.n=d.nodes
 def expr(self,idx):
  seen={}; output=[]; tasks=[(idx,False)]
  while tasks:
   e,finish=tasks.pop()
   if self.d.eq_ids[e] in seen: continue
   n=self.n[e]; tag,c,s=n['tag'],n['children'],n['scalars']
   expr_children=({5:c,6:c[1:],7:c[1:],8:c[1:],10:c[1:],11:c[2:]}.get(tag,()))
   if not finish:
    tasks.append((e,True))
    for child in reversed(expr_children):
     if self.d.eq_ids[child] not in seen: tasks.append((child,False))
    continue
   repr=self.r.repr
   if tag==0: node=['bvar',self.n[c[0]]['value']]
   elif tag==1: node=['fvar',repr(c[0])]
   elif tag==2: node=['mvar',repr(c[0])]
   elif tag==3: node=['sort',repr(c[0])]
   elif tag==4: node=['const',repr(c[0]),repr(c[1])]
   elif tag==5: node=['app',seen[self.d.eq_ids[c[0]]],seen[self.d.eq_ids[c[1]]]]
   elif tag in (6,7): node=['lam' if tag==6 else 'forallE',repr(c[0]),seen[self.d.eq_ids[c[1]]],seen[self.d.eq_ids[c[2]]],('Lean.BinderInfo.default','Lean.BinderInfo.implicit','Lean.BinderInfo.strictImplicit','Lean.BinderInfo.instImplicit')[s[8]]]
   elif tag==8: node=['letE',repr(c[0]),seen[self.d.eq_ids[c[1]]],seen[self.d.eq_ids[c[2]]],seen[self.d.eq_ids[c[3]]],bool(s[8])]
   elif tag==9: node=['lit',repr(c[0])]
   elif tag==10: node=['mdata',repr(c[0]),seen[self.d.eq_ids[c[1]]]]
   elif tag==11: node=['proj',repr(c[0]),self.n[c[1]]['value'],seen[self.d.eq_ids[c[2]]]]
   else: raise InvalidArtifact('unrecognized expression')
   seen[self.d.eq_ids[e]]=len(output); output.append(node)
  return {'root':seen[self.d.eq_ids[idx]],'nodes':output}
 def unpack(self,info):
  i=self.n[info]; kind=i['tag']; val=self.n[i['children'][0]]; base=self.n[val['children'][0]]
  return kind,val,base
 def name(self,info): return self.unpack(info)[2]['children'][0]
 def body(self,info):
  kind,val,base=self.unpack(info)
  return val['children'][1] if kind in (1,2,3) else None
 def extra(self,info):
  kind,v,b=self.unpack(info); c=v['children']; n=lambda i:decimal(self.n[i]['value'])
  if kind==1:
   return 'safety='+('Lean.DefinitionSafety.unsafe','Lean.DefinitionSafety.safe','Lean.DefinitionSafety.partial')[v['scalars'][0]]
  if kind==5: return 'ctors='+self.r.repr(c[4])+';numParams='+n(c[1])+';numIndices='+n(c[2])
  if kind==6: return 'induct='+self.r.name_string(c[1])+';cidx='+n(c[2])+';numParams='+n(c[3])+';numFields='+n(c[4])
  if kind==7: return 'all='+self.r.repr(c[1])+';params='+n(c[2])+';indices='+n(c[3])+';motives='+n(c[4])+';minors='+n(c[5])+';ruleCount='+decimal(len(self.d.list_items(c[6])))+';k='+('true' if v['scalars'][0] else 'false')
  return ''
 def records(self,module,private,public):
  names=self.n[private['const_names']]['children']; constants=self.n[private['constants']]['children']
  if len(names)!=len(constants): raise InvalidArtifact('compiled contract inconsistent metadata: '+module)
  by_name={}
  for info in constants: by_name.setdefault(self.name(info),info)
  exported=set(self.n[public['const_names']]['children']) if public is not None else None
  exposed={}
  if public is not None:
   for info in self.n[public['constants']]['children']: exposed.setdefault(self.name(info),self.body(info) is not None)
  yield {'module':module,'module_system':private['is_module'],'declaration_count':len(names)}
  for name in names:
   if name not in by_name: raise InvalidArtifact('missing declaration')
   info=by_name[name]; kind,val,base=self.unpack(info); c=base['children']; comp=self.r.components(name)
   # isPrivateName requires precisely the anonymous root `_private`, not an
   # arbitrary component of that spelling in a user namespace.
   from .observations import is_private_name
   isprivate=is_private_name(self.d,name)
   body=self.body(info)
   dec={'name':self.r.name_string(name),'kind':('axiom','def','theorem','opaque','quot','inductive','constructor','recursor')[kind],'private':isprivate,'internal':any(t==1 and v.startswith('_') for t,v in comp),'type':self.expr(c[2]),'body':self.expr(body) if body is not None else None,'levels':self.r.repr(c[1]),'extra':self.extra(info),'exported':name in exported if exported is not None else None,'exposed':exposed.get(name,False) if public is not None else None}
   yield {'module':module,'module_system':private['is_module'],'declaration':dec}

def capture(module,path):
 d=TypedDecoder([path]); public=d.module(d.parts.regions[0])
 if public['is_module']:
  d.parts.add(str(path)+'.server'); d.parts.add(str(path)+'.private'); private=d.module(d.parts.regions[-1])
 else: private=public; public=None
 return Schema2(d),private,public
