"""Compiled dependency and trace observations on the existing checked importer.

Namespace queries observe persisted registrations only. No module initializer,
callback, elaborator, kernel checker or native reader executes here.
"""
from collections import deque
from functools import cmp_to_key
from .importer import Graph
from .paths import parse_name, render_name
from .render import Renderer
from .typed import InvalidArtifact

MASK = (1 << 64) - 1
M = 0xc6a4a7935bd1e995


def string_hash(value):
    """Pinned runtime/hash.cpp MurmurHash64A over UTF8, with seed eleven."""
    data = value.encode('utf8'); h = (11 ^ (len(data) * M)) & MASK
    whole = len(data) // 8 * 8
    for i in range(0, whole, 8):
        k = int.from_bytes(data[i:i+8], 'little') * M & MASK
        k ^= k >> 47; k = k * M & MASK
        h = ((h ^ k) * M) & MASK
    if whole != len(data):
        h = ((h ^ int.from_bytes(data[whole:], 'little')) * M) & MASK
    h ^= h >> 47; h = h * M & MASK; h ^= h >> 47
    return h


def name_hash(components):
    """Original computed Name.hash, including its large-numeral branch."""
    h = 1723
    for tag, value in components:
        k = string_hash(value) if tag == 1 else value if value <= MASK else 17
        k = k * M & MASK; k ^= k >> 47; k ^= M
        h = ((h ^ k) * M) & MASK
    return h


def name_observer(d, idx):
    """Name equality retains the root cached hash and structural payload."""
    node = d.nodes[idx]
    return (int.from_bytes(node['scalars'], 'little') if node['tag'] else 1723,
            tuple(Renderer(d).components(idx)))


def query_observer(text):
    parts = parse_name(text)
    return name_hash(parts), parts



def is_private_name(d, idx):
    """Original privateHeader comparisons retain each prefix's cached hash."""
    private = query_observer('_private')
    while d.nodes[idx]['tag']:
        node = d.nodes[idx]
        if node['tag'] == 1 and name_observer(d, idx) == private: return True
        idx = node['children'][0]
    return False


def cmp(a, b):
    """Three-way comparison for the original scalar name-component orders."""
    return (a > b) - (a < b)


def name_cmp(a, b):
    """Pinned Name.cmp; constructor tags precede prefix comparison."""
    x, y = a[1], b[1]; i, j = len(x)-1, len(y)-1
    while i >= 0 and j >= 0:
        if x[i][0] != y[j][0]: return -1 if x[i][0] == 2 else 1
        i -= 1; j -= 1
    if i != j: return cmp(i, j)
    for u, v in zip(x, y):
        result = cmp(u[1], v[1])
        if result: return result
    return 0


def quick_cmp(a, b):
    """Name.quickCmp keeps cached hash order and reverse component ties."""
    result = cmp(a[0], b[0])
    if result: return result
    x, y = a[1], b[1]
    for u, v in zip(reversed(x), reversed(y)):
        if u[0] != v[0]: return -1 if u[0] == 2 else 1
        result = cmp(u[1], v[1])
        if result: return result
    return cmp(len(x), len(y))


def extension_entries(module, tag):
    """Last exactly tagged persisted record; absent registration is empty.

Unknown extensions are retained in the original bound artifact bytes and never
interpreted as namespace or axiom data.
    """
    d = module.d; found = ()
    for ptr in d.parts.array(module.data(True)[4]):
        _, _, fields = d.parts.ctor(ptr, 0, 2, 0)
        name = d.decode('Name', fields[0])
        if name_observer(d, name) == query_observer(tag):
            found = d.parts.array(fields[1])
    return found


NAMESPACE_TAG = '_private.Lean.Namespace.0.Lean.namespacesExt'
AXIOM_TAG = '_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt'


class Observations:
    """One selected compiled module with complete private/IR import identity."""
    def __init__(self, module, search, trace_environment=False):
        """Load original private imports and the trace template's Core owners."""
        self.module_text = module; self.module = render_name(parse_name(module))
        self.graph = Graph(search)
        roots = [self.module]
        if trace_environment:
            roots += ['Lean.Util.CollectAxioms', 'Lean.Util.FoldConsts', 'Lean.Elab.Command']
        self.constants, self.order, self.state = self.graph.maps(roots, True)
        self.by_name = {}; self.names = {}; self.owners = {}; self.axiom_tables = {}
        for key, ref in self.constants.items():
            name = name_observer(ref.d, ref.name)
            self.by_name[name] = ref; self.names[key] = name
        for key, owner in self.graph.owners.items():
            # An IR-only name is decoded by its module before entering owners.
            self.owners[self.graph.owner_names[key]] = owner

    def expression_names(self, ref, root, projections=False):
        """Finite expression traversal; projection owners are opt-in."""
        d = ref.d; result = []; seen = set(); names = set(); todo = [root]
        while todo:
            idx = todo.pop(); key = d.eq_ids[idx]
            if key in seen: continue
            seen.add(key); n = d.nodes[idx]; tag, c = n['tag'], n['children']
            if tag == 4 or tag == 11 and projections:
                name = name_observer(d, c[0])
                if name not in names: names.add(name); result.append(name)
            children = {5:c, 6:c[1:], 7:c[1:], 8:c[1:], 10:c[1:], 11:c[2:]}.get(tag, ())
            todo.extend(reversed(children))
        return result

    @staticmethod
    def body(ref):
        """Read a retained definition, theorem or opaque value when present."""
        return ref.d.decode('Expr', ref.fields[1]) if ref.kind in (1, 2, 3) else None

    def used(self, ref):
        """Original ConstantInfo type/body and no-body constructor dependencies."""
        names = set(self.expression_names(ref, ref.type()))
        body = self.body(ref)
        if body is not None: names.update(self.expression_names(ref, body))
        elif ref.kind in (5, 7):
            ptr = ref.fields[4] if ref.kind == 5 else ref.fields[1]
            idx = ref.d.decode('List:Name', ptr)
            names.update(name_observer(ref.d, n) for n in ref.d.list_items(idx))
        elif ref.kind == 6: names.add(name_observer(ref.d, ref.name))
        return names

    def persisted_axioms(self, name):
        """Imported precomputed entries selected by original first owner."""
        owner = self.owners.get(name)
        if owner is None: return None
        if owner not in self.axiom_tables:
            mod = self.state[owner]['module']; table = []
            if mod is not None:
                for ptr in extension_entries(mod, AXIOM_TAG):
                    _, _, fields = mod.d.parts.ctor(ptr, 0, 2, 0)
                    idx = mod.d.decode('Name', fields[0])
                    values = [name_observer(mod.d, mod.d.decode('Name', p))
                              for p in mod.d.parts.array(fields[1])]
                    table.append((name_observer(mod.d, idx), values))
            self.axiom_tables[owner] = table
        table = self.axiom_tables[owner]; lo, hi = 0, len(table)
        while lo < hi:
            mid = (lo+hi)//2; relation = quick_cmp(table[mid][0], name)
            if relation < 0: lo = mid+1
            elif relation > 0: hi = mid
            else: return table[mid][1]
        return None

    def axioms(self, root):
        """Pinned collectAxioms cache/sentinel traversal, fresh for each call."""
        seen = {}; tasks = [('visit', root)]; current = set()
        while tasks:
            task = tasks.pop(); name = task[1]
            if task[0] == 'finish':
                seen[name] = sorted(current, key=cmp_to_key(name_cmp))
                current = task[2] | current
                continue
            imported = self.persisted_axioms(name)
            if imported is not None:
                seen[name] = imported; current.update(imported); continue
            if name in seen: current.update(seen[name]); continue
            saved = current; current = set(); seen[name] = []
            tasks.append(('finish', name, saved)); ref = self.by_name.get(name)
            if ref is None: continue
            deps = []
            if ref.kind == 0: current.add(name)
            if ref.kind != 4: deps.extend(self.expression_names(ref, ref.type()))
            body = self.body(ref)
            if body is not None: deps.extend(self.expression_names(ref, body))
            if ref.kind == 5:
                idx = ref.d.decode('List:Name', ref.fields[4])
                deps.extend(name_observer(ref.d, n) for n in ref.d.list_items(idx))
            tasks.extend(('visit', n) for n in reversed(deps))
        return seen[root]

    def namespaces(self):
        """Union actual persisted registrations; no initialization executes."""
        names = set()
        for name in self.order:
            mod = self.state[name]['module']
            if mod is not None:
                names.update(name_observer(mod.d, mod.d.decode('Name', p))
                             for p in extension_entries(mod, NAMESPACE_TAG))
        return names

    def dependencies(self, queries):
        own = self.graph.load(self.module)
        public_rows = own.entries(False); exported = {k for k, _, _ in public_rows}
        public = {}
        for key, ref, _ in public_rows: public.setdefault(key, ref)
        declarations = []
        for key, _, idx in own.entries(True):
            ref = self.constants.get(key)
            if ref is None: raise InvalidArtifact('missing declaration: '+Renderer(own.d).name_string(idx))
            visible = key in exported; body = self.body(ref)
            exposed = key in public and self.body(public[key]) is not None
            parts = []
            for role, expr in [('public_signature' if visible else 'private_signature', ref.type()),
                               ('proof' if ref.kind == 2 else 'exposed_body' if exposed else 'private_body', body)]:
                if expr is None: continue
                names = sorted(self.expression_names(ref, expr, True), key=cmp_to_key(quick_cmp))
                parts.append({'role':role,'dependencies':[{'constant':render_name(n[1]),'owner':self.owners.get(n)} for n in names]})
            components = Renderer(own.d).components(idx)
            declarations.append({'name':Renderer(own.d).name_string(idx),'exported':visible,
                                 'private_name':is_private_name(own.d, idx),
                                 'internal':any(t == 1 and s.startswith('_') for t, s in components),'parts':parts})
        registered = self.namespaces() if queries else set()
        return {'module':self.module_text,'module_system':own.modern,'declarations':declarations,
                'namespace_queries':[{'namespace':q,'registered':query_observer(q) in registered} for q in queries]}

    def applications(self, ref, root, target):
        """Retain every shared occurrence, including partial applications."""
        d = ref.d; todo = [root]
        while todo:
            idx = todo.pop(); n = d.nodes[idx]; tag,c = n['tag'],n['children']
            if tag == 5:
                args = []; fn = idx
                while d.nodes[fn]['tag'] == 5:
                    f,a = d.nodes[fn]['children']; args.append(a); fn = f
                head = d.nodes[fn]
                if head['tag'] == 4 and name_observer(d, head['children'][0]) == target:
                    yield list(reversed(args))
            todo.extend(reversed({5:c,6:c[1:],7:c[1:],8:c[1:],10:c[1:],11:c[2:]}.get(tag, ())))

    def trace(self, mode, target_text, declaration_text):
        """Exact compiled tracing fields; types use serialized Expr Repr."""
        target = query_observer(target_text); declaration = query_observer(declaration_text)
        ref = self.by_name.get(declaration)
        if ref is None: raise InvalidArtifact('unknown declaration '+render_name(declaration[1]))
        name = render_name(declaration[1]); target_name = render_name(target[1])
        if mode == 'use':
            body = self.body(ref)
            if body is None: raise InvalidArtifact('declaration '+name+' has no inspectable value')
            renderer = Renderer(ref.d)
            for location, expr in [('type', ref.type()), ('proof', body)]:
                any_ = False
                for index, args in enumerate(self.applications(ref, expr, target), 1):
                    any_ = True
                    yield f'{name} {location} directly applies {target_name} at occurrence {index} with {len(args)} arguments'
                    for i, arg in enumerate(args, 1):
                        text = renderer.repr(arg)
                        yield f'  argument {i}: '+(text if len(text) <= 600 else text[:600]+'…')
                if not any_: yield f'{name} {location} contains no direct application of {target_name}'
            return
        if target not in self.by_name: raise InvalidArtifact('unknown target axiom or declaration '+target_name)
        yield name+' type (serialized Expr Repr): '+Renderer(ref.d).repr(ref.type())
        closure = self.axioms(declaration)
        names = lambda ns:'['+', '.join(render_name(n[1]) for n in ns)+']'
        yield name+' closure axioms: '+names(sorted(closure,key=cmp_to_key(name_cmp)))
        if target not in closure:
            yield 'does not depend on '+target_name; return
        immediate = sorted((n for n in self.used(ref) if n == target or target in self.axioms(n)),key=cmp_to_key(name_cmp))
        types = set(self.expression_names(ref, ref.type()))
        yield 'immediate dependencies carrying '+target_name+': '+names(immediate)
        yield 'type dependencies carrying '+target_name+': '+names([n for n in immediate if n in types])
        queue = deque([(declaration,[declaration])]); visited = {declaration}; found = None
        while queue:
            n,path = queue.popleft()
            if n == target: found = path; break
            r = self.by_name.get(n)
            if r is not None:
                for dep in sorted(self.used(r),key=cmp_to_key(name_cmp)):
                    if dep not in visited and (dep == target or target in self.axioms(dep)):
                        visited.add(dep); queue.append((dep,path+[dep]))
        yield 'shortest path: '+(' -> '.join(render_name(n[1]) for n in found) if found is not None else '<no path found despite closure result>')


def artifact_pins(module, search):
    """Bind every selected metadata/IR part before a cached owner report is used."""
    graph = Graph(search); order, state = graph.imports([render_name(parse_name(module))], True)
    pins = []; seen = set()
    for name in order:
        for selected in (state[name]['module'], state[name]['ir']):
            if selected is None: continue
            for region in selected.d.parts.regions:
                path = str(region.path)
                if path not in seen:
                    seen.add(path)
                    pins.append({'path':path,'sha256':region.sha256,'bytes':len(region.data)})
    return pins
