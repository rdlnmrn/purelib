"""Private original Repr observers on the complete pinned typed graph."""
from . import format as F
from .typed import InvalidArtifact, raw_substring

MAX_PREC=1024  # Init.Data.Nat.Basic max_prec := 1024, not a parser limit.

def letter_like(c):
 n=ord(c)
 return (0x3b1<=n<=0x3c9 and n!=0x3bb or 0x391<=n<=0x3a9 and n not in (0x3a0,0x3a3) or 0x3ca<=n<=0x3fb or 0x1f00<=n<=0x1ffe or 0x2100<=n<=0x214f or 0x1d49c<=n<=0x1d59f or 0xc0<=n<=0xff and n not in (0xd7,0xf7) or 0x100<=n<=0x17f)
def first(c): return 'a'<=c<='z' or 'A'<=c<='Z' or c=='_' or letter_like(c)
def rest(c):
 n=ord(c)
 return first(c) or '0'<=c<='9' or c in "'!?" or 0x2080<=n<=0x2089 or 0x2090<=n<=0x209c or 0x1d62<=n<=0x1d6a or n==0x2c7c

def derived(name,args,prec):
 body=F.text(name)
 for arg in args: body=F.append(F.append(body,F.LINE),arg)
 body=('group',('nest',1 if prec>=MAX_PREC else 2,body),False)
 return F.bracket('(',body,')') if prec>=MAX_PREC else body

class Renderer:
 def __init__(self,decoder):
  self.d=decoder; self.nodes=decoder.nodes; self.cache={}; self.name_cache={}
 def components(self,idx):
  out=[]
  while self.nodes[idx]['tag']:
   n=self.nodes[idx]; prefix,value=n['children']; out.append((n['tag'],self.nodes[value]['value'])); idx=prefix
  return list(reversed(out))
 def name_string(self,idx):
  if idx in self.name_cache: return self.name_cache[idx]
  comp=self.components(idx)
  if not comp: value='[anonymous]'
  else:
   strs=[v for t,v in comp if t==1]
   # Core only inspects the final string component after numerical suffixes.
   last_string=next((v for t,v in reversed(comp) if t==1),None)
   inaccessible=last_string is not None and ('✝' in last_string or last_string=='_inaccessible')
   macro=last_string=='_hyg'
   pseudo=comp==[(1,'_')] or comp[0][0]==1 and comp[0][1].startswith(('#','?'))
   escape=not (inaccessible or macro or pseudo)
   pieces=[]
   for tag,v in comp:
    if tag==2: pieces.append(F.decimal(v))
    elif not escape or v and first(v[0]) and all(rest(c) for c in v[1:]) or '»' in v: pieces.append(v)
    else: pieces.append('«'+v+'»')
   value='.'.join(pieces)
  self.name_cache[idx]=value; return value
 def deps(self,idx,prec):
  n=self.nodes[idx]; kind,tag,c=n['kind'],n['tag'],n['children']
  if kind in ('Nat','String','Bool','Int','Substring'): return []
  if kind=='Name':
   if tag and (tag==2 or any(t==2 for t,v in self.components(c[0]))):
    return [(c[0],MAX_PREC),(c[1],0)]
   return []
  if kind.startswith('List:'): return [(i,0) for i in self.d.list_items(idx)]
  if kind.startswith('Array:'): return [(i,0) for i in c]
  if kind=='Pair:Name:DataValue': return [(i,0) for i in c]
  if kind=='KVMap': return [(c[0],0)]
  if kind=='SourceInfo':
   if tag==0: return [(c[0],MAX_PREC),(c[2],MAX_PREC)]
   return []
  return [(i,MAX_PREC) for i in c]
 def build(self,idx,prec):
  n=self.nodes[idx]; kind,tag,c,scalar,v=n['kind'],n['tag'],n['children'],n['scalars'],n['value']
  get=lambda i,p=MAX_PREC:self.cache[i,p]
  if kind=='Nat': return F.text(F.decimal(v))
  if kind=='String': return F.text(F.quote(v))
  if kind=='Bool': return F.text('true' if v else 'false')
  if kind=='Int':
   result=F.text(F.decimal(v))
   return F.bracket('(',result,')') if v<0 and prec>=MAX_PREC else result
  if kind=='Name':
   if tag==0: return F.text('Lean.Name.anonymous')
   if tag==1 and not any(t==2 for t,v in self.components(c[0])): return F.text('`'+self.name_string(idx))
   body=F.append(F.append(F.append(F.text('Lean.Name.mkNum ' if tag==2 else 'Lean.Name.mkStr '),get(c[0])),F.text(' ')),get(c[1],0))
   return F.bracket('(',body,')') if prec>=MAX_PREC else body
  if kind.startswith('List:'):
   items=self.d.list_items(idx)
   if not items: return F.text('[]')
   atom=kind[5:] in ('Bool','Nat','Int','String')
   return F.bracket('[',F.join((get(i,0) for i in items),F.append(F.text(','),F.LINE)),']',atom)
  if kind.startswith('Array:'):
   if not c: return F.text('#[]')
   return F.bracket('#[',F.join((get(i,0) for i in c),F.append(F.text(','),F.LINE)),']',True)
  if kind=='Pair:Name:DataValue': return F.bracket('(',F.join((get(i,0) for i in c),F.append(F.text(','),F.LINE)),')')
  if kind=='KVMap':
   field=F.append(F.text('entries := '),('group',('nest',11,get(c[0],0)),False))
   return F.bracket('{ ',field,' }')
  if kind=='Substring':
   value=self.nodes[c[0]]['value']; start=self.nodes[c[1]]['value']; stop=self.nodes[c[2]]['value']; raw=value.encode('utf8')
   part=raw_substring(value,start,stop)
   return F.text(F.quote(part)+'.toRawSubstring')
  if kind=='Expr':
   args=[get(i) for i in c]
   if tag in (6,7):
    args.append(derived(('Lean.BinderInfo.default','Lean.BinderInfo.implicit',
                         'Lean.BinderInfo.strictImplicit','Lean.BinderInfo.instImplicit')[scalar[8]],[],MAX_PREC))
   elif tag==8: args.append(F.text('true' if scalar[8] else 'false'))
   return derived(('Lean.Expr.bvar','Lean.Expr.fvar','Lean.Expr.mvar','Lean.Expr.sort',
                   'Lean.Expr.const','Lean.Expr.app','Lean.Expr.lam','Lean.Expr.forallE',
                   'Lean.Expr.letE','Lean.Expr.lit','Lean.Expr.mdata','Lean.Expr.proj')[tag],args,prec)
  if kind=='Level':
   return derived(('Lean.Level.zero','Lean.Level.succ','Lean.Level.max','Lean.Level.imax','Lean.Level.param','Lean.Level.mvar')[tag],[get(i) for i in c],prec)
  if kind=='Literal': return derived(('Lean.Literal.natVal','Lean.Literal.strVal')[tag],[get(i) for i in c],prec)
  if kind=='DataValue':
   args=[F.text('true' if scalar[0] else 'false')] if tag==1 else [get(i) for i in c]
   return derived(('Lean.DataValue.ofString','Lean.DataValue.ofBool','Lean.DataValue.ofName','Lean.DataValue.ofNat','Lean.DataValue.ofInt','Lean.DataValue.ofSyntax')[tag],args,prec)
  if kind=='Syntax': return derived(('Lean.Syntax.missing','Lean.Syntax.node','Lean.Syntax.atom','Lean.Syntax.ident')[tag],[get(i) for i in c],prec)
  if kind=='Preresolved': return derived(('Lean.Syntax.Preresolved.namespace','Lean.Syntax.Preresolved.decl')[tag],[get(i) for i in c],prec)
  if kind=='SourceInfo':
   def pos(i): return F.text('{ byteIdx := '+F.decimal(self.nodes[i]['value'])+' }')
   if tag==0: args=[get(c[0]),pos(c[1]),get(c[2]),pos(c[3])]
   elif tag==1: args=[pos(c[0]),pos(c[1]),F.text('true' if scalar[0] else 'false')]
   else: args=[]
   return derived(('Lean.SourceInfo.original','Lean.SourceInfo.synthetic','Lean.SourceInfo.none')[tag],args,prec)
  raise InvalidArtifact('no original Repr contract for '+kind)
 def format(self,idx,prec=0):
  tasks=[(idx,prec,False)]
  while tasks:
   i,p,finish=tasks.pop()
   if (i,p) in self.cache: continue
   if finish: self.cache[i,p]=self.build(i,p)
   else:
    tasks.append((i,p,True))
    for j,q in reversed(self.deps(i,p)):
     if (j,q) not in self.cache: tasks.append((j,q,False))
  return self.cache[idx,prec]
 def repr(self,idx): return F.pretty(self.format(idx))
