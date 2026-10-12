"""Exact pinned imported metadata used by the original axiom-root predicate.

Only persisted declaration ranges, meta tags and global CSimp entries are read.
Target initializers, scope callbacks and elaborators never execute here.
"""
from functools import cmp_to_key
from .observations import name_observer, query_observer, quick_cmp
from .typed import InvalidArtifact

RANGE_TAG = 'Lean.declRangeExt'
META_TAG = '_private.Lean.Compiler.MetaAttr.0.Lean.metaExt'
CSIMP_TAG = 'Lean.Compiler.CSimp.ext'


def entries(module, tag, part=None):
    """Last exact extension record in the requested retained module part."""
    d = module.d
    data = module.data(True) if part is None else d.parts.ctor(module.roots[part].root,0,5,1)[2]
    found = ()
    for ptr in d.parts.array(data[4]):
        _, _, fields = d.parts.ctor(ptr, 0, 2, 0)
        idx = d.decode('Name', fields[0])
        if name_observer(d, idx) == query_observer(tag):
            found = d.parts.array(fields[1])
    return found


def lookup(table, name):
    """Original Name.quickLt binary search; missing and present empty differ."""
    lo, hi = 0, len(table)
    while lo < hi:
        mid = (lo+hi)//2; relation = quick_cmp(table[mid], name)
        if relation < 0: lo = mid+1
        elif relation > 0: hi = mid
        else: return True
    return False


class RootMetadata:
    """Imported first-owner range/meta tables and replayed global CSimp names."""
    def __init__(self, observation):
        self.observation = observation; self.ranges = {}; self.meta = {}; self.csimp = set()
        for owner in observation.order:
            mod = observation.state[owner]['module']
            if mod is None: continue
            d = mod.d
            for ptr in entries(mod, CSIMP_TAG):
                _, _, header = d.header(ptr)
                # Scoped entries persist but the audit worker activates no scopes.
                if header[3] == 0:
                    _, _, fields = d.parts.ctor(ptr, 0, 1, 0)
                    payload = fields[0]
                elif header[3] == 1:
                    d.parts.ctor(ptr, 1, 2, 0)
                    continue
                else:
                    raise InvalidArtifact('unsupported CSimp scoped-entry constructor')
                _, _, fields = d.parts.ctor(payload, 0, 3, 0)
                for field in fields: d.decode('Name', field)
                self.csimp.add(name_observer(d, d.decode('Name', fields[2])))

    def tables(self, owner):
        """Observe exact exported/private and server lookup tables for one owner."""
        if owner not in self.ranges:
            mod = self.observation.state[owner]['module']; ranges=[]; meta=[]
            if mod is not None:
                for part in (len(mod.roots)-1, 1 if mod.modern else 0):
                    table=[]
                    for ptr in entries(mod, RANGE_TAG, part):
                        _, _, fields = mod.d.parts.ctor(ptr, 0, 2, 0)
                        # The original predicate observes presence, not range coordinates.
                        table.append(name_observer(mod.d,mod.d.decode('Name',fields[0])))
                    ranges.append(table)
                meta=[name_observer(mod.d,mod.d.decode('Name',p)) for p in entries(mod,META_TAG)]
            self.ranges[owner]=ranges; self.meta[owner]=meta
        return self.ranges[owner],self.meta[owner]

    def has_range(self, name):
        owner=self.observation.owners.get(name)
        return owner is not None and any(lookup(t,name)for t in self.tables(owner)[0])

    def marked_meta(self, name):
        owner=self.observation.owners.get(name)
        return owner is not None and lookup(self.tables(owner)[1],name)


def user_components(name):
    """Original privateToUserName removes the retained private module/index prefix."""
    parts=name[1]
    if parts and parts[0]==(1,'_private'):
        for index,(tag,value) in enumerate(parts):
            if tag==2:
                return parts[index+1:] if value==0 else parts

    return parts


def unsafe(ref):
    """ConstantInfo.isUnsafe; a partial definition is not an unsafe definition."""
    if ref.kind==1:return ref.scalar[0]==0
    if ref.kind in (0,3,6):return bool(ref.scalar[0])
    if ref.kind==5:return bool(ref.scalar[1])
    if ref.kind==7:return bool(ref.scalar[1])
    return False


def audit_root(name, ref, metadata):
    """The original source/provenance predicate, without namespace inference."""
    parts=user_components(name); internal=any(t==1 and s.startswith('_')for t,s in parts)
    text=metadata.observation.text(name)
    constructor_api=False
    if text.endswith(('.inj','.injEq')):
        prefix_parts=name[1][:-1]
        prefix=metadata.observation.query_parts(prefix_parts)
        ctor=metadata.observation.by_name.get(prefix)
        if ctor is not None and ctor.kind==6:
            ind=name_observer(ctor.d,ctor.d.decode('Name',ctor.fields[1]))
            constructor_api=metadata.has_range(ind)
    excluded=((internal and not metadata.has_range(name)and not constructor_api)or
              text.endswith(('.congr_simp','.eq_def','.induct_unfolding'))or
              unsafe(ref)or metadata.marked_meta(name))
    return not excluded or name in metadata.csimp
