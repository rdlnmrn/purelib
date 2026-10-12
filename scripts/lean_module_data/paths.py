"""Pinned Lean module-name parsing and package-root artifact selection."""
import os
import subprocess
from pathlib import Path
from .compact import InvalidArtifact, PIN
from .render import first, rest


def parse_name(value):
    """Mirror String.toName's finite name-literal parsing without a depth cap."""
    result = []
    pos = 0
    while pos < len(value):
        begin = pos
        if value[pos] == '«':
            end = value.find('»', pos + 1)
            if end < 0:
                return ()
            result.append((1, value[pos + 1:end])); pos = end + 1
        elif first(value[pos]):
            pos += 1
            while pos < len(value) and rest(value[pos]): pos += 1
            result.append((1, value[begin:pos]))
        elif '0' <= value[pos] <= '9':
            pos += 1
            while pos < len(value) and '0' <= value[pos] <= '9': pos += 1
            number = 0
            for char in value[begin:pos]: number = number * 10 + ord(char) - 48
            result.append((2, number))
        else:
            return ()
        if pos == len(value): break
        if value[pos] != '.': return ()
        pos += 1
        if pos == len(value): return ()
    return tuple(result)


def render_name(components):
    """Original Name.toString default escaping for a retained component list."""
    from .format import decimal
    if not components: return '[anonymous]'
    last = next((value for tag, value in reversed(components) if tag == 1), None)
    escape = not (last is not None and ('✝' in last or last in ('_inaccessible', '_hyg')) or
                  components == ((1, '_'),) or components[0][0] == 1 and
                  components[0][1].startswith(('#', '?')))
    return '.'.join(decimal(value) if tag == 2 else value if not escape or '»' in value or
                    value and first(value[0]) and all(rest(c) for c in value[1:])
                    else '«' + value + '»' for tag, value in components)


def find_olean(module, search):
    """Select a package root first, even if its requested descendant is missing."""
    components = parse_name(module) if isinstance(module, str) else module
    if not components: raise FileNotFoundError('unknown module prefix [anonymous]')
    if any(tag != 1 for tag, _ in components): raise InvalidArtifact('ill-formed import: numeric module component')
    values = [value for _, value in components]
    for root in search:
        root = Path(root); package = root / values[0]
        if package.is_dir() or Path(str(package) + '.olean').exists():
            return Path(str(root.joinpath(*values)) + '.olean')
    raise FileNotFoundError('unknown module prefix ' + repr(values[0]))


def search_path():
    """Original LEAN_PATH order followed by the pinned compiler's builtin root.

    The only compiler subprocess is its metadata-only --print-prefix query;
    neither a Lean source nor compiled module is executed or decoded by it.
    """
    sysroot = os.environ.get('LEAN_SYSROOT')
    if sysroot is None:
        result = subprocess.run(['lean', '--print-prefix'], check=True, text=True,
                                capture_output=True)
        sysroot = result.stdout.strip(' \t\r\n')
    environment = os.environ.get('LEAN_PATH')
    roots = [Path(p) for p in environment.split(os.pathsep)] if environment is not None else []
    return roots + [Path(sysroot) / 'lib/lean']
