"""Original schema1 Repr records from pinned checked import graphs.

Each capture preserves original import order, theorem subsumption, public/private
map distinction and required interpreter metadata without running an initializer.
"""
from .contracts import Schema2
from .importer import Graph
from .paths import parse_name, render_name
from .render import Renderer
from .observations import is_private_name


def records(modules, search):
    """Merge CLI roots, then emit each original own-name list in retained order.

Production drivers still invoke one module per process, preserving independent
standalone declarations such as `main`. Direct multi-root capture retains the
original duplicate-theorem and incompatible-definition behavior.
"""
    modules = [render_name(parse_name(name)) for name in modules]
    graph = Graph(search)
    private, _, _ = graph.maps(modules, True)
    renderers, schemas = {}, {}
    for module in modules:
        own = graph.load(module)
        public = graph.maps([module], False)[0] if own.modern else None
        rows = own.entries(True)
        own_renderer = Renderer(own.d)
        yield {'module': module, 'module_system': own.modern, 'declaration_count': len(rows)}
        for key, _, own_name in rows:
            ref = private[key]
            decoder = ref.d
            if decoder not in renderers:
                renderers[decoder], schemas[decoder] = Renderer(decoder), Schema2(decoder)
            renderer, schema = renderers[decoder], schemas[decoder]
            info = ref.info()
            kind, _, constant = schema.unpack(info)
            body = schema.body(info)
            public_ref = public.get(key) if public is not None else None
            components = own_renderer.components(own_name)
            declaration = {
                'name': own_renderer.name_string(own_name),
                'kind': ('axiom', 'def', 'theorem', 'opaque', 'quot', 'inductive', 'constructor', 'recursor')[kind],
                'private': is_private_name(own.d, own_name),
                'internal': any(tag == 1 and part.startswith('_') for tag, part in components),
                'type': renderer.repr(constant['children'][2]),
                'body': renderer.repr(body) if body is not None else None,
                'levels': renderer.repr(constant['children'][1]),
                'extra': schema.extra(info),
                'exported': public_ref is not None if public is not None else None,
                'exposed': (public_ref.kind in (1, 2, 3) if public_ref is not None else
                            False if public is not None else None),
            }
            yield {'module': module, 'module_system': own.modern, 'declaration': declaration}


def diagnostic(error):
    """Retain the original reader's uncaught-exception diagnostic envelope.

The observed compact reader opens missing artifact files with the named-file
message below. Other checked format failures remain explicit failures; this
function does not manufacture module data or recover through another reader.
"""
    if isinstance(error, FileNotFoundError) and error.filename is not None:
        message = f"failed to open file '{error.filename}': {error.strerror}"
    else:
        message = str(error)
    return 'uncaught exception: ' + message
