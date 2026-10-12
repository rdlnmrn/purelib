"""Prepare and apply reviewed Lean import, reference and documentation edits.

This is a source editor, not a Lean elaborator. Exact source hashes and lexical
boundaries protect edits; compilation checks resolution and public contracts.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from dataclasses import asdict, dataclass

from scripts.paths import ROOT
SCHEMA = 1
MODES = {'import', 'public import', 'meta import', 'public meta import',
         'import all', 'public import all', 'meta import all', 'public meta import all', 'remove'}
DECL_KINDS = r'class\s+inductive|def|abbrev|opaque|theorem|lemma|structure|class|inductive|instance|axiom|syntax|macro|elab|example'
DECL = re.compile(r'(?P<attrs>(?:@\[[^\n]*?\]\s*)*)(?P<mods>(?:(?:public|private|protected|meta|unsafe|partial|nonrec|noncomputable|local|scoped)\s+)*)'
                  r'(?P<kind>' + DECL_KINDS + r')\b')
IMPORT = re.compile(r'(?P<mode>(?:public\s+)?(?:meta\s+)?import(?:\s+all)?)\s+(?P<module>[\w.]+)\s*$')
NAME = re.compile(r"(?:«[^»]+»|[^\W\d][\w'!?₀-₉]*)(?:\.(?:«[^»]+»|[^\W\d][\w'!?₀-₉]*))*", re.UNICODE)
RAW_STRING = re.compile(r'r(#+)?"')
OPEN_COMMAND = re.compile(
    r'open\s+(?:scoped\s+)?' + NAME.pattern +
    r'(?:(?:\s+' + NAME.pattern + r')*|\s*\(\s*' + NAME.pattern + r'(?:\s+' + NAME.pattern + r')*\s*\)|'
    r'\s+renaming\s+' + NAME.pattern + r'\s*(?:->|→)\s*' + NAME.pattern +
    r'(?:\s*,\s*' + NAME.pattern + r'\s*(?:->|→)\s*' + NAME.pattern + r')*)'
    r'(?:\s+in)?')


def digest(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()


def encoded(value) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def keys(obj, allowed, required, where):
    require(isinstance(obj, dict), f'{where}: expected an object')
    require(not (obj.keys() - set(allowed)), f'{where}: unknown keys {obj.keys() - set(allowed)}')
    require(set(required) <= obj.keys(), f'{where}: missing keys {set(required) - obj.keys()}')


def nonempty(value, where):
    require(isinstance(value, str) and bool(value.strip()), f'{where}: expected nonempty text')


def name(value, where):
    require(isinstance(value, str) and '\n' not in value and '\r' not in value and NAME.fullmatch(value) is not None, f'{where}: invalid Lean name {value!r}')


@dataclass(frozen=True)
class Token:
    kind: str
    start: int
    end: int
    text: str


def lex(text: str) -> list[Token]:
    """Tokenize names while retaining nested comments and strings as opaque spans."""
    result = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            kind = 'comment'
        elif text.startswith('/-', i):
            kind = 'doc' if text.startswith('/--', i) else 'comment'
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, f'unclosed comment at offset {start}')
        elif (raw := RAW_STRING.match(text, i)):
            marker = '"' + (raw[1] or '')
            end = text.find(marker, raw.end())
            require(end >= 0, f'unclosed raw string at offset {start}')
            i = end + len(marker)
            kind = 'string'
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            require(i < len(text), f'unclosed string at offset {start}')
            i += 1
            kind = 'string'
        elif text[i] == "'" and (char := re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\n])'", text[i:])):
            i += char.end()
            kind = 'string'
        elif (ident := NAME.match(text, i)):
            i = ident.end()
            kind = 'ident'
        else:
            i += 1
            continue
        result.append(Token(kind, start, i, text[start:i]))
    return result


def mask(text: str, tokens: list[Token]) -> str:
    chars = list(text)
    for token in tokens:
        if token.kind != 'ident':
            for i in range(token.start, token.end):
                if chars[i] not in '\r\n':
                    chars[i] = ' '
    return ''.join(chars)


def calc_rhs_identifiers(text: str, tokens: list[Token]) -> set[int]:
    """Recognize final names in ordinary indented calc equality/inequality steps.

    A step ends at its first assignment at the calc's delimiter depth. Nested
    records and named arguments have a different depth; proof assignments are
    outside the step. Unknown term/control forms remain protected. This narrow
    recognizer deliberately does not attempt to parse arbitrary relation syntax.
    """
    code = mask(text, tokens)
    identifiers = {token.start: token for token in tokens if token.kind == 'ident'}
    opening = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    delimiters, contexts, allowed = [], [], set()
    boundaries = {'where', 'with', 'by', 'do', 'then', 'else', 'in', 'from',
                  'def', 'abbrev', 'opaque', 'theorem', 'lemma', 'instance',
                  'structure', 'class', 'inductive', 'example', 'let', 'have',
                  'show', 'fun', 'match', 'if', 'exact', 'apply', 'rw', 'simp',
                  'change', 'intro', 'refine', 'constructor', 'namespace', 'end'}
    line_start, at_line_start, i = 0, True, 0
    while i < len(code):
        char = code[i]
        if char == '\n':
            line_start, at_line_start = i + 1, True
            i += 1
            continue
        if char.isspace():
            i += 1
            continue
        depth = len(delimiters)
        if at_line_start:
            indent = i - line_start
            while contexts and contexts[-1]['depth'] == depth:
                context = contexts[-1]
                if context['phase'] == 'pending' or indent > context['indent']:
                    break
                if indent == context['indent'] and context['phase'] == 'proof':
                    context.update(phase='step', relation=False)
                    break
                if indent < context['indent']:
                    contexts.pop()
                else:
                    break
            at_line_start = False
        context = contexts[-1] if contexts and contexts[-1]['depth'] == depth else None
        if context and context['phase'] == 'pending':
            context.update(phase='step', relation=False,
                           indent=len(code[line_start:i]) - len(code[line_start:i].lstrip()))
        if token := identifiers.get(i):
            quoted = code[max(0, i - 1):i] in {'`', '$'}
            if context and context['phase'] == 'step':
                if token.text in boundaries:
                    contexts.pop()
                    context = None
                elif (not quoted and context['relation'] and
                      re.match(r'\s*:=', code[token.end:])):
                    allowed.add(token.start)
            if token.text == 'calc' and not quoted:
                contexts.append({'depth': depth, 'phase': 'pending', 'indent': 0})
            i = token.end
            continue
        if char in opening:
            delimiters.append(opening[char])
        elif char in opening.values():
            if delimiters and delimiters[-1] == char:
                delimiters.pop()
                while contexts and contexts[-1]['depth'] > len(delimiters):
                    contexts.pop()
            else:
                contexts.clear()
        elif code.startswith(':=', i):
            if context and context['phase'] == 'step':
                context['phase'] = 'proof'
            i += 2
            continue
        elif code.startswith('=>', i) or char in ';|':
            if context and context['phase'] == 'step':
                contexts.pop()
        elif context and context['phase'] == 'step' and char in '=<>≤≥≠':
            context['relation'] = True
        i += 1
    return allowed


def by_type_rhs_identifiers(text: str, tokens: list[Token]) -> set[int]:
    """Recognize an exact-term endpoint before a theorem's outer proof assignment.

    Only a header equality ending in an indented ``by`` term is supported. Its
    direct ``exact`` command must end in ``name := by``, followed by a proof at
    lower indentation. Delimiter depth excludes record/named-argument labels;
    the first ordinary header assignment ends the search before any proof body.
    """
    code = mask(text, tokens)
    identifiers = {token.start: token for token in tokens if token.kind == 'ident'}
    opening = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    allowed = set()
    for declaration in inventory(text)['declarations']:
        if declaration['kind'] not in {'theorem', 'lemma'}:
            continue
        delimiters, annotated, signature_by, block_indent, exact = [], False, None, None, False
        i = declaration['name_end']
        while i < declaration['end']:
            char = code[i]
            if char.isspace():
                i += 1
                continue
            line_start = code.rfind('\n', 0, i) + 1
            first_on_line = not code[line_start:i].strip()
            indent = i - line_start
            if signature_by is not None and first_on_line and not delimiters:
                if block_indent is None:
                    block_indent = indent
                elif indent < block_indent:
                    break
                if indent == block_indent:
                    exact = False
            if token := identifiers.get(i):
                quoted = code[max(0, i - 1):i] in {'`', '$'}
                if not delimiters and not quoted:
                    if signature_by is None and annotated and token.text == 'by':
                        if code[declaration['name_end']:i].rstrip().endswith('='):
                            signature_by = token.end
                        else:
                            break
                    elif signature_by is not None:
                        if first_on_line and indent == block_indent and token.text == 'exact':
                            exact = True
                        if exact and (tail := re.match(r'\s*:=\s*by\b', code[token.end:declaration['end']])):
                            following = token.end + tail.end()
                            next_term = re.search(r'\S', code[following:declaration['end']])
                            if next_term:
                                next_offset = following + next_term.start()
                                next_line = code.rfind('\n', following, next_offset) + 1
                                if (next_line > following and block_indent is not None and
                                        next_offset - next_line < block_indent):
                                    allowed.add(token.start)
                            break
                i = token.end
                continue
            if char in opening:
                delimiters.append(opening[char])
            elif char in opening.values():
                if not delimiters or delimiters.pop() != char:
                    break
            elif not delimiters:
                if code.startswith(':=', i):
                    if signature_by is None:
                        break
                    i += 2
                    continue
                if char == ':' and code[i + 1:i + 2] != ':' and code[i - 1:i] != ':':
                    annotated = True
                if char == ';':
                    exact = False
            i += 1
    return allowed


def type_rhs_identifiers(text: str, tokens: list[Token]) -> set[int]:
    """Recognize relation endpoints in theorem types and typed local have claims.

    Declaration inventories bound header searches; explicit annotation colons
    bound local claims. Quantifier commas keep that type context. Header lets
    are skipped through their offside-delimited values, never exposing their
    binding labels. Nested assignments, syntax quotations and unsupported term
    forms remain protected. Equality-by headers use the separate narrow rule.
    """
    code = mask(text, tokens)
    identifiers = {token.start: token for token in tokens if token.kind == 'ident'}
    opening = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    allowed = by_type_rhs_identifiers(text, tokens)

    def annotated_endpoint(start, stop, *, header_lets):
        delimiters, annotated, relation, prefix, previous = [], False, False, True, None
        let_indent, let_assigned = None, False
        i = start
        while i < stop:
            char = code[i]
            if char.isspace():
                i += 1
                continue
            line_start = code.rfind('\n', 0, i) + 1
            first_on_line = not code[line_start:i].strip()
            if not delimiters and let_indent is not None and let_assigned and first_on_line:
                indent = i - line_start
                if indent < let_indent:
                    return None
                if indent == let_indent:
                    let_indent, let_assigned, prefix, previous = None, False, True, None
            if token := identifiers.get(i):
                if not delimiters and let_indent is None:
                    if not annotated and token.text in {'by', 'where', 'let', 'have', 'exact'}:
                        return None
                    if annotated:
                        if header_lets and prefix and token.text == 'let' and first_on_line:
                            let_indent = i - line_start
                        elif token.text in {'by', 'where', 'let', 'have', 'fun', 'match', 'if', 'do', 'exact'}:
                            return None
                        else:
                            prefix = False
                    previous = token
                i = token.end
                continue
            if char in opening:
                delimiters.append(opening[char])
            elif char in opening.values():
                if not delimiters or delimiters.pop() != char:
                    return None
            elif not delimiters:
                if code.startswith(':=', i):
                    if not annotated:
                        return None
                    if let_indent is not None:
                        let_assigned = True
                        i += 2
                        continue
                    if (relation and previous is not None and not code[previous.end:i].strip()
                            and code[max(0, previous.start - 1):previous.start] not in {'`', '$'}):
                        return previous.start
                    return None
                if let_indent is None:
                    if char == ':' and code[i + 1:i + 2] != ':' and code[i - 1:i] != ':':
                        annotated = True
                    elif annotated and char in '=<>≤≥≠' and not code.startswith('=>', i):
                        relation, prefix = True, False
                    elif char in ';|':
                        return None
            i += 1
        return None

    for declaration in inventory(text)['declarations']:
        if declaration['kind'] not in {'theorem', 'lemma'}:
            continue
        endpoint = annotated_endpoint(declaration['name_end'], declaration['end'], header_lets=True)
        if endpoint is not None:
            allowed.add(endpoint)
        # Only standalone local have commands are supported. In particular,
        # names inside quotation delimiters are syntax data, not local claims.
        delimiters = []
        i = declaration['name_end']
        while i < declaration['end']:
            if token := identifiers.get(i):
                line_start = code.rfind('\n', 0, i) + 1
                if (token.text == 'have' and not any(quoted for _, quoted in delimiters)
                        and code[line_start:i].strip() in {'', '·'}):
                    endpoint = annotated_endpoint(token.end, declaration['end'], header_lets=False)
                    if endpoint is not None:
                        allowed.add(endpoint)
                i = token.end
                continue
            char = code[i]
            if char in opening:
                delimiters.append((opening[char], code[max(0, i - 1):i] == '`'))
            elif char in opening.values():
                if delimiters and delimiters[-1][0] == char:
                    delimiters.pop()
                else:
                    break
            i += 1
    return allowed


def assignment_labels(text: str, tokens: list[Token], *, rewrite_calc_rhs: bool = False,
                      rewrite_type_rhs: bool = False) -> set[int]:
    """Protect assignment heads, allowing names in explicit type annotations.

    A name before ``:=`` is ambiguous without its preceding syntax: it can be
    a field/named-argument label or the last name of a return/default type.
    Track a bare annotation colon separately within each delimiter pair.
    Assignments and term/command boundaries end the annotation; entering a
    nested pair starts fresh, so an outer return type cannot unprotect a
    named argument or record label inside it. Unclassified heads stay protected.
    Comments, strings and escaped names never supply punctuation to this scan.
    """
    code = mask(text, tokens)
    identifiers = {token.start: token for token in tokens if token.kind == 'ident'}
    opening = {'(': ')', '[': ']', '{': '}', '⦃': '⦄', '⟨': '⟩'}
    stack = [[None, False]]
    boundaries = {'where', 'with', 'by', 'do', 'then', 'else', 'in', 'from',
                  'def', 'abbrev', 'opaque', 'theorem', 'lemma', 'instance',
                  'structure', 'class', 'inductive', 'example', 'let', 'have'}
    protected = set()
    i = 0
    while i < len(code):
        if token := identifiers.get(i):
            if re.match(r'\s*:=', code[token.end:]) and not stack[-1][1]:
                protected.add(token.start)
            if token.text in boundaries:
                stack[-1][1] = False
            i = token.end
            continue
        char = code[i]
        if char in opening:
            stack.append([opening[char], False])
        elif char in opening.values():
            if len(stack) > 1 and stack[-1][0] == char:
                stack.pop()
            else:
                stack[-1][1] = False
        elif code.startswith((':=', '=>'), i):
            stack[-1][1] = False
            i += 2
            continue
        elif char in ',;|':
            stack[-1][1] = False
        elif char == ':' and (i == 0 or code[i - 1] != ':') and code[i + 1:i + 2] not in {':', '>'}:
            stack[-1][1] = True
        i += 1
    if rewrite_calc_rhs:
        protected.difference_update(calc_rhs_identifiers(text, tokens))
    if rewrite_type_rhs:
        protected.difference_update(type_rhs_identifiers(text, tokens))
    return protected



def child_inventory(text: str, code: str, tokens: list[Token], declarations: list[dict]) -> tuple[list, list]:
    """Find source fields and constructors without changing declaration scopes.

    Indentation separates member heads from multiline types and default bodies.
    Unsupported heads are returned as diagnostics, rather than guessed names.
    """
    children, unsupported = [], []
    modifier = re.compile(r'(?:(?:@\[[^\]]*\]|private|protected|public|meta|unsafe)\s+)*')

    def warning(parent, offset, reason):
        unsupported.append({'parent': parent['key'], 'line': text.count('\n', 0, offset) + 1, 'reason': reason})

    for parent in declarations:
        if parent['kind'] not in {'structure', 'class', 'inductive', 'class inductive'}:
            continue
        inductive = 'inductive' in parent['kind']
        body = None
        depth = 0
        i = parent['name_end']
        while i < parent['end']:
            char = code[i]
            if depth == 0:
                word = NAME.match(code, i)
                if word:
                    if word[0] == 'where':
                        body = word.end()
                        break
                    i = word.end()
                    continue
                if code.startswith(':=', i):
                    body = i + 2
                    break
                if inductive and char == '|':
                    body = i
                    break
            depth += (char in '([{') - (char in ')]}')
            i += 1
        if body is None:
            continue  # A structure may have no explicitly declared fields.
        offset = body
        field_column = None
        last_child = None
        while offset < parent['end']:
            line_end = code.find('\n', offset, parent['end'])
            if line_end < 0:
                line_end = parent['end']
            line_start = code.rfind('\n', 0, offset) + 1
            fragment = code[offset:line_end]
            head_start = offset + len(fragment) - len(fragment.lstrip())
            head = code[head_start:line_end]
            next_member = None
            if inductive and head.startswith('|'):
                # A constructor separator is meaningful only outside its
                # argument binders. Comments, strings and quotations are
                # already masked; pipes inside a binder's type are not heads.
                depth = 0
                for pos in range(head_start + 1, line_end):
                    char = code[pos]
                    if depth == 0 and char == '|' and code[pos - 1].isspace():
                        suffix = code[pos + 1:line_end].lstrip()
                        if suffix and (NAME.match(suffix) or suffix.startswith('@[')):
                            next_member = pos
                            line_end = pos
                            head = code[head_start:line_end]
                            break
                    depth += (char in '([{') - (char in ')]}')
            original_column = len(text[line_start:line_end]) - len(text[line_start:line_end].lstrip())
            offset = next_member if next_member is not None else line_end + 1
            if not head:
                continue
            inline_header = line_start < body and bool(code[line_start:body].strip())
            column = head_start - line_start if inline_header else original_column
            if head.startswith('deriving ') or (not inline_header and column <= parent['column'] and not head.startswith('|')):
                break
            if inductive:
                if not head.startswith('|'):
                    if last_child is None:
                        warning(parent, head_start, 'expected a leading | constructor')
                    continue
                prefix = head_start
                cursor = head_start + 1
            else:
                if field_column is None:
                    field_column = column
                elif not inline_header and column > field_column:
                    continue
                elif column < field_column:
                    # An inline first field cannot establish the indentation
                    # of the following physical lines.
                    if last_child and last_child.get('inline_header'):
                        field_column = column
                    else:
                        warning(parent, head_start, 'inconsistent field indentation')
                        continue
                prefix = head_start
                cursor = head_start
            while cursor < line_end and code[cursor].isspace():
                cursor += 1
            mods = modifier.match(code, cursor, line_end)
            cursor = mods.end()
            match = NAME.match(code, cursor, line_end)
            if not match:
                warning(parent, head_start, 'unsupported member head (grouped binders, attributes or computed fields)')
                continue
            leaf = match[0]
            rest = code[match.end():line_end].lstrip()
            kind = 'constructor' if inductive or rest.startswith('::') else 'field'
            if not inductive and kind == 'field' and rest and not rest.startswith((':', '(', '{', '[')):
                warning(parent, head_start, 'unsupported field head; expected a single field name and signature')
                continue
            # A doc may precede the pipe, or occur after it as a modifier.
            doc = next((t for t in reversed(tokens) if t.kind == 'doc' and t.end <= match.start()
                        and (code[t.end:prefix].strip() == '' if t.end <= prefix
                             else code[t.end:match.start()].strip() == '')), None)
            full = leaf.removeprefix('_root_.') if leaf.startswith('_root_.') else parent['name'] + '.' + leaf
            child = {'name': full, 'key': full, 'parent': parent['key'], 'kind': kind,
                     'line': text.count('\n', 0, match.start()) + 1,
                     'name_start': match.start(), 'name_end': match.end(),
                     'anchor': doc.start if doc else prefix, 'attribute_start': prefix,
                     'doc': asdict(doc) if doc else None, 'inline_header': inline_header}
            children.append(child)
            last_child = child
    counts = {}
    for child in children:
        counts[child['name']] = counts.get(child['name'], 0) + 1
    for child in children:
        if counts[child['name']] > 1:
            child['key'] = f"{child['name']}@{child['line']}"
    return children, unsupported


def inventory(text: str) -> dict:
    tokens = lex(text)
    code = mask(text, tokens)
    # Syntax quotations can contain commands that introduce new names. They
    # require elaborator-backed editing, so hide them from this lexical editor.
    quotation_spans = []
    search = 0
    while (quote := code.find('`(', search)) >= 0:
        j, depth = quote + 2, 1
        while j < len(code) and depth:
            depth += (code[j] == '(') - (code[j] == ')')
            j += 1
        require(depth == 0, f'unclosed syntax quotation at offset {quote}')
        quotation_spans.append((quote, j))
        search = j
    if quotation_spans:
        tokens = [t for t in tokens if not any(a <= t.start < b for a, b in quotation_spans)]
        tokens += [Token('quotation', a, b, text[a:b]) for a, b in quotation_spans]
        tokens.sort(key=lambda t: t.start)
        code = mask(text, tokens)
    imports, declarations, commands, boundaries, syntax_headers = [], [], [], [], []
    scopes = []
    namespace = ''

    def scope_components(header):
        # Dotted namespace/section headers introduce one Lean scope per component.
        return re.findall(r'«[^»]+»|[^.]+', header) if header else ['']

    def push_scope(header, is_namespace):
        nonlocal namespace
        for part in scope_components(header):
            scopes.append((part, namespace))
            if is_namespace:
                # Ordinary namespace commands append _root_ literally. Only
                # declaration names and with_weak_namespace strip its prefix.
                namespace = '.'.join(filter(None, [namespace, part]))
    position = 0
    for line_number, line in enumerate(code.splitlines(True), 1):
        stripped = line.strip()
        require(not re.match(r'with_weak_namespace\b', stripped),
                f'with_weak_namespace requires elaborator-backed command scope at line {line_number}')
        start = position + len(line) - len(line.lstrip())
        require(not re.search(r'\bin\s+(?:public\s+|private\s+)?(?:' + DECL_KINDS + r')\b', stripped),
                f'inline declaration wrapper at line {line_number}; put the declaration on its own line before review')
        is_command = re.match(r'(?:namespace|end|section|mutual|open|export|variable|universe|attribute|set_option|local|scoped|notation|infix[lr]?|prefix|postfix|macro_rules|elab_rules|initialize|builtin_initialize)\b|#', stripped)
        syntax_command = re.match(
            r'(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|meta|unsafe|local|scoped)\s+)*'
            r'(syntax|macro_rules|elab_rules|macro|elab|notation|infix[lr]?|prefix|postfix|declare_syntax_cat)\b',
            stripped)
        if syntax_command:
            syntax_headers.append((position, start - position, line_number, syntax_command[1]))
            boundaries.append((position, start - position))
        if is_command:
            boundaries.append((position, start - position))
        if re.match(r'(?:(?:public|meta)\s+)*import\b', stripped) and not IMPORT.fullmatch(stripped):
            raise ValueError(f'unsupported import layout at line {line_number}; use one complete import per line')
        if match := IMPORT.fullmatch(stripped):
            imports.append({'module': match['module'], 'mode': ' '.join(match['mode'].split()),
                            'start': start, 'end': position + len(line.rstrip()), 'line': line_number})
            commands.append((position, position + len(line)))
        elif stripped.startswith('namespace '):
            ns = stripped.split()[1]
            push_scope(ns, True)
            commands.append((position, position + len(line)))
        elif re.fullmatch(r'(?:@\[[^\]]*\]\s*)*(?:(?:public|private|meta)\s+)?section(?:\s+\S+)?', stripped):
            header = re.search(r'\bsection(?:\s+(\S+))?$', stripped)[1] or ''
            push_scope(header, False)
        elif stripped == 'mutual':
            scopes.append(('', namespace))
        elif re.fullmatch(r'end(?:\s+\S+)?', stripped):
            header = stripped[3:].strip()
            parts = scope_components(header) if header else ['']
            require(len(parts) <= len(scopes) and [part for part, _ in scopes[-len(parts):]] == parts,
                    f'end scope header mismatch at line {line_number}: {header or '<anonymous>'}')
            for _ in parts:
                _, namespace = scopes.pop()
            commands.append((position, position + len(line)))
        elif stripped.startswith(('open ', 'export ')):
            commands.append((position, position + len(line)))
        if match := DECL.match(line.lstrip()):
            after = start + match.end()
            tail = code[after:position + len(line)]
            kind = match['kind']
            anonymous = kind in {'instance', 'syntax', 'macro', 'elab', 'example'}
            # Ordinary declaration names may follow their keyword on the next
            # line. Keep original offsets, including masked intervening comments.
            name_tail = tail if anonymous else code[after:]
            token_match = NAME.match(code, after + len(name_tail) - len(name_tail.lstrip()))
            named = re.search(r'\(\s*name\s*:=\s*(' + NAME.pattern + r')\s*\)', tail) if anonymous and kind != 'example' else None
            if named:
                leaf = named[1]
                name_start = after + named.start(1)
                name_end = after + named.end(1)
            elif token_match and kind not in {'syntax', 'macro', 'elab', 'example'} and not (anonymous and (tail.lstrip().startswith(('(', '[', '"')) or token_match[0] in {'where'})):
                leaf = token_match[0]
                name_start, name_end = token_match.span()
            else:
                require(anonymous, f'cannot locate declaration name at line {line_number}')
                leaf = f'{kind}@{line_number}'
                name_start = name_end = after
            full = leaf.removeprefix('_root_.') if leaf.startswith('_root_.') else '.'.join(filter(None, [namespace, leaf]))
            # Include preceding standalone attributes in the insertion anchor.
            anchor = position
            while True:
                end = len(code[:anchor].rstrip())
                previous_line_start = code.rfind('\n', 0, end) + 1
                if code[previous_line_start:end].strip() in {'public', 'private', 'protected', 'meta', 'unsafe', 'noncomputable', 'partial', 'nonrec', 'local', 'scoped'}:
                    anchor = previous_line_start
                    continue
                if not end or code[end - 1] != ']':
                    break
                j, depth = end - 2, 1
                while j >= 0 and depth:
                    depth += (code[j] == ']') - (code[j] == '[')
                    j -= 1
                if depth or j < 0 or code[j] != '@':
                    break
                line_start = code.rfind('\n', 0, j) + 1
                if code[line_start:j].strip():
                    break
                anchor = line_start
            previous = next((t for t in reversed(tokens) if t.kind == 'doc' and t.end <= anchor and code[t.end:anchor].strip() == ''), None)
            doc = previous if previous is not None and previous.kind == 'doc' else None
            declarations.append({'name': full, 'kind': kind, 'line': line_number, 'start': start,
                                 'column': start - position,
                                 'anchor': doc.start if doc else anchor, 'attribute_start': anchor,
                                 'name_start': name_start, 'name_end': name_end,
                                 'doc': asdict(doc) if doc else None})
        position += len(line)
    counts = {}
    for d in declarations:
        counts[d['name']] = counts.get(d['name'], 0) + 1
    for i, d in enumerate(declarations):
        d['key'] = d['name'] if counts[d['name']] == 1 else f"{d['name']}@{d['line']}"
        d['end'] = declarations[i + 1]['anchor'] if i + 1 < len(declarations) else len(text)
        d['end'] = min([d['end']] + [a for a, column in boundaries if d['start'] < a < d['end'] and column <= d['column']])
    # A notation expansion or elaborator body is compiler input, even outside
    # quotations. Changing its identifier spelling can change generated code.
    # Extend protection over indented continuation lines and rule clauses until
    # a recognized command at the same or a lesser indentation begins. Unknown
    # command forms remain protected rather than guessing where a template ends.
    command_starts = boundaries + [(d['anchor'], d['column']) for d in declarations]
    command_starts += [(r['start'], 0) for r in imports]
    syntax_commands = [
        {'start': a, 'end': min([len(text)] + [b for b, indent in command_starts
                                            if a < b and indent <= column]),
         'line': line, 'kind': kind}
        for a, column, line, kind in syntax_headers]
    children, unsupported = child_inventory(text, code, tokens, declarations)
    return {'imports': imports, 'declarations': declarations, 'children': children,
            'unsupported_children': unsupported, 'commands': commands,
            'syntax_commands': syntax_commands, 'tokens': tokens}


def source_path(plan, root=ROOT):
    value = plan['path']
    require(isinstance(value, str), 'path: expected a relative Lean source path')
    path = Path(value)
    require(not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean', 'path must be a relative .lean file without ..')
    resolved = (root / path).resolve()
    require(resolved.is_relative_to(root.resolve()), 'source path escapes repository')
    return resolved


def validate_plan(plan):
    keys(plan, {'schema', 'path', 'source_sha256', 'imports', 'opens', 'open_edits', 'rewrites', 'docstrings', 'review', 'prepared', 'declaration_renames', 'trim_trailing_whitespace', 'rewrite_calc_rhs', 'rewrite_type_rhs'},
         {'schema', 'path', 'source_sha256', 'imports', 'opens', 'rewrites', 'docstrings', 'review'}, 'plan')
    require(plan['schema'] == SCHEMA, 'unsupported schema')
    require(type(plan.get('trim_trailing_whitespace', False)) is bool,
            'trim_trailing_whitespace: expected a boolean')
    require(type(plan.get('rewrite_calc_rhs', False)) is bool,
            'rewrite_calc_rhs: expected a boolean')
    require(type(plan.get('rewrite_type_rhs', False)) is bool,
            'rewrite_type_rhs: expected a boolean')
    require(isinstance(plan['source_sha256'], str) and re.fullmatch('[0-9a-f]{64}', plan['source_sha256']), 'invalid source_sha256')
    nonempty(plan['review'], 'review')
    renames = plan.get('declaration_renames', [])
    require(isinstance(renames, list), 'declaration_renames: expected a list')
    for row in renames:
        keys(row, {'from', 'to', 'reason'}, {'from', 'to', 'reason'}, 'declaration rename')
        for key in ('from', 'to'):
            require(isinstance(row[key], str) and NAME.fullmatch(row[key]) is not None
                    and not row[key].startswith('_root_.'),
                    f'declaration rename {key}: expected an absolute declaration name without _root_')
        require(row['from'] != row['to'], 'declaration rename must change the name')
        nonempty(row['reason'], 'declaration rename reason')
    for key in ('from', 'to'):
        require(len({row[key] for row in renames}) == len(renames),
                f'duplicate declaration rename {key}')
    require(isinstance(plan.get('open_edits', []), list), 'open_edits: expected a list')
    for row in plan.get('open_edits', []):
        keys(row, {'from', 'to', 'count', 'reason'}, {'from', 'to', 'count', 'reason'}, 'open edit')
        for key in ('from', 'to'):
            value = row[key]
            require(isinstance(value, str) and '\n' not in value and '\r' not in value, f'open edit {key}: expected one command line')
            require((key == 'to' and not value) or value.startswith('open '), 'open edits only change open commands')
            require('/-' not in value and '--' not in value, 'open edits cannot contain comments')
            require((key == 'to' and not value) or OPEN_COMMAND.fullmatch(value), 'unsupported open command syntax')
        require(type(row['count']) is int and row['count'] > 0, 'open edit count must be positive')
        nonempty(row['reason'], 'open edit reason')
    for field in ('imports', 'opens', 'rewrites'):
        require(isinstance(plan[field], list), f'{field}: expected a list')
    seen = set()
    for row in plan['imports']:
        keys(row, {'module', 'mode', 'also', 'reason'}, {'module', 'mode', 'reason'}, 'import')
        name(row['module'], 'import.module')
        require(row['mode'] in MODES, f"invalid import mode {row['mode']!r}")
        also = row.get('also', [])
        require(isinstance(also, list) and all(isinstance(mode, str) and mode in MODES - {'remove'} for mode in also), 'import.also: expected import modes')
        require(not also or row['mode'] != 'remove', 'removed imports cannot have additional modes')
        require(len(set([row['mode'], *also])) == len(also) + 1, 'duplicate import mode')
        nonempty(row['reason'], 'import.reason')
        require(row['module'] not in seen, f"duplicate import decision: {row['module']}")
        seen.add(row['module'])
    aliases = set()
    for row in plan['opens']:
        keys(row, {'namespace', 'names', 'renaming', 'scope', 'reason'}, {'namespace', 'scope', 'reason'}, 'open')
        name(row['namespace'], 'open.namespace')
        nonempty(row['scope'], 'open.scope')
        nonempty(row['reason'], 'open.reason')
        require(not ('names' in row and 'renaming' in row), 'choose names or renaming for an open')
        if 'names' in row:
            require(isinstance(row['names'], list) and row['names'], 'open.names: expected nonempty list')
            for value in row['names']:
                name(value, 'open.names')
            require(len(set(row['names'])) == len(row['names']), 'duplicate selected open name')
        if 'renaming' in row:
            require(isinstance(row['renaming'], dict) and row['renaming'], 'open.renaming: expected nonempty map')
            for key, value in row['renaming'].items():
                name(key, 'renamed declaration'); name(value, 'alias')
                require((row['scope'], value) not in aliases, f'duplicate alias: {value}')
                aliases.add((row['scope'], value))
    for row in plan['rewrites']:
        keys(row, {'from', 'to', 'scope', 'count', 'reason', 'match'}, {'from', 'to', 'scope', 'count', 'reason'}, 'rewrite')
        require(row.get('match', 'prefix') in {'exact', 'prefix'}, 'rewrite.match must be exact or prefix')
        name(row['from'], 'rewrite.from')
        require('.' in row['from'], 'rewrite.from must be qualified')
        name(row['to'], 'rewrite.to')
        require(row['from'] != row['to'], 'rewrite must change its name')
        require(type(row['count']) is int and row['count'] > 0, 'rewrite.count must be a positive integer')
        nonempty(row['scope'], 'rewrite.scope'); nonempty(row['reason'], 'rewrite.reason')
    require(isinstance(plan['docstrings'], dict), 'docstrings: expected declaration-to-text map')
    for key, value in plan['docstrings'].items():
        nonempty(key, 'docstring key'); nonempty(value, f'docstring for {key}')
        require('/-' not in value and '-/' not in value, 'docstrings must contain content without comment delimiters')


def instructions_hash(plan):
    return digest(encoded({k: v for k, v in plan.items() if k != 'prepared'}))


def compile_edits(plan, text):
    validate_plan(plan)
    require(digest(text) == plan['source_sha256'], 'source changed since review; inspect and review the new source')
    data = inventory(text)
    decls = {d['key']: d for d in data['declarations']}
    doc_targets = {d['key']: d for d in [*data['declarations'], *data['children']]}
    masked = mask(text, data['tokens'])
    edits = []
    def edit(start, end, after):
        if text[start:end] != after:
            edits.append({'start': start, 'end': end, 'before': text[start:end], 'after': after})
    for row in plan.get('declaration_renames', []):
        require(row['from'] in decls, f"unknown declaration rename source: {row['from']}")
        require(row['to'] not in decls, f"declaration rename target already exists: {row['to']}")
        declaration = decls[row['from']]
        require(declaration['name_start'] < declaration['name_end'],
                'cannot rename an anonymous declaration')
        edit(declaration['name_start'], declaration['name_end'], '_root_.' + row['to'])
    def bounds(scope):
        if scope == 'file':
            return 0, len(text)
        if scope.startswith('proof:'):
            key = scope.removeprefix('proof:')
            require(key in decls, f'unknown proof scope: {key}')
            d = decls[key]
            depth = 0
            for i in range(d['name_end'], d['end']):
                depth += (masked[i] in '([{') - (masked[i] in ')]}')
                if depth == 0 and (i == 0 or not (masked[i - 1].isalnum() or masked[i - 1] in "_'.")):
                    word = NAME.match(masked, i)
                    if word and word[0] in {'let', 'have'}:
                        raise ValueError(f'proof scope has an unsupported unparenthesized signature expression ({word[0]}): {key}; use a file or declaration opening')
                if depth == 0 and masked[i] == '|' and not masked[masked.rfind('\n', 0, i) + 1:i].strip():
                    raise ValueError(f'proof scope has equation clauses rather than a := body: {key}')
                if depth == 0 and masked.startswith('where', i) and (i == 0 or masked[i - 1].isspace()) and (i + 5 == len(masked) or masked[i + 5].isspace()):
                    raise ValueError(f'proof scope has a where body rather than a := body: {key}')
                if depth == 0 and masked.startswith(':=', i):
                    j = i + 2
                    while j < d['end'] and masked[j].isspace():
                        j += 1
                    return j, d['end']
            raise ValueError(f'proof scope has no top-level := body: {key}')
        require(scope in decls, f'unknown or ambiguous declaration scope: {scope}')
        return decls[scope]['start'], decls[scope]['end']
    decisions = {row['module']: row for row in plan['imports']}
    actual = {row['module']: row for row in data['imports']}
    require(actual.keys() <= decisions.keys(), f'missing import decisions: {actual.keys() - decisions.keys()}')
    retained = set()
    def render_import(row):
        return '\n'.join(mode + ' ' + row['module'] for mode in [row['mode'], *row.get('also', [])])
    for row in data['imports']:
        module = row['module']
        mode = decisions[module]['mode']
        original_modes = {r['mode'] for r in data['imports'] if r['module'] == module}
        require(len(original_modes) <= 1 or 'also' in decisions[module],
                f'mixed import modes for {module}; explicitly supply also, even if empty')
        edit(row['start'], row['end'], '' if mode == 'remove' or module in retained else render_import(decisions[module]))
        retained.add(module)
    header_end = max((text.find('\n', row['end']) + 1 or len(text) for row in data['imports']), default=0)
    if not header_end:
        module_header = re.search(r'^module\s*$', mask(text, data['tokens']), re.M)
        require(module_header is not None, 'source needs an explicit module header')
        header_end = text.find('\n', module_header.start()) + 1
        require(header_end > 0, 'module header needs a following newline')
    additions = [render_import(r) + '\n' for r in plan['imports'] if r['module'] not in actual and r['mode'] != 'remove']
    require(not any(r['mode'] == 'remove' and r['module'] not in actual for r in plan['imports']), 'cannot remove an absent import')
    insertions = {}
    if additions:
        insertions[header_end] = ''.join(additions)
    replaced_opens = set()
    for row in plan.get('open_edits', []):
        matched = [(a, b) for a, b in data['commands'] if masked[a:b].strip() == row['from']]
        require(len(matched) == row['count'], f"open edit {row['from']}: expected {row['count']} occurrences, found {len(matched)}")
        for a, b in matched:
            start = a + len(masked[a:b]) - len(masked[a:b].lstrip())
            end = a + len(masked[a:b].rstrip())
            edit(start, end, row['to'])
            replaced_opens.add((a, b))
    open_seen = set()
    for row in plan['opens']:
        scope = row['scope']; bounds(scope)
        rendered = 'open ' + row['namespace']
        if 'names' in row:
            rendered += ' (' + ' '.join(row['names']) + ')'
        if 'renaming' in row:
            rendered += ' renaming ' + ', '.join(f'{a} -> {b}' for a, b in sorted(row['renaming'].items()))
        require((scope, rendered) not in open_seen, 'duplicate open instruction')
        open_seen.add((scope, rendered))
        require(not any(masked[a:b].strip() == rendered for a, b in data['commands'] if (a, b) not in replaced_opens), f'open already exists: {rendered}')
        if scope == 'file':
            offset = header_end
            fragment = '\n' + rendered + '\n'
        elif scope.startswith('proof:'):
            offset, _ = bounds(scope)
            fragment = rendered + ' in '
        else:
            offset = decls[scope]['anchor']
            fragment = rendered + ' in\n'
        insertions[offset] = insertions.get(offset, '') + fragment
    protected = data['commands'] + [(d['name_start'], d['name_end']) for d in [*data['declarations'], *data['children']]]
    labels = assignment_labels(text, data['tokens'], rewrite_calc_rhs=plan.get('rewrite_calc_rhs', False),
                               rewrite_type_rhs=plan.get('rewrite_type_rhs', False))
    counts = [0] * len(plan['rewrites'])
    syntax_counts = [0] * len(plan['rewrites'])
    ranges = [bounds(row['scope']) for row in plan['rewrites']]
    for token in data['tokens']:
        if token.kind != 'ident' or any(a <= token.start < b for a, b in protected):
            continue
        # Field labels, named arguments, syntax names and quoted names retain their identities.
        if token.start in labels or text[max(0, token.start - 1):token.start] in {'`', '$'}:
            continue
        candidates = []
        for i, (row, (a, b)) in enumerate(zip(plan['rewrites'], ranges)):
            if a <= token.start < b and (token.text == row['from'] or (row.get('match', 'prefix') == 'prefix' and token.text.startswith(row['from'] + '.'))):
                candidates.append((len(row['from']), i, row))
        if candidates:
            candidates.sort(reverse=True, key=lambda x: x[0])
            require(len(candidates) == 1 or candidates[0][0] != candidates[1][0], f'overlapping rewrite instructions at offset {token.start}')
            _, i, row = candidates[0]
            if any(command['start'] <= token.start < command['end'] for command in data['syntax_commands']):
                syntax_counts[i] += 1
                continue
            edit(token.start, token.end, row['to'] + token.text[len(row['from']):])
            counts[i] += 1
    for row, count, hidden in zip(plan['rewrites'], counts, syntax_counts):
        suffix = f'; {hidden} references are in protected syntax commands (notation, macro or elaborator)' if hidden else ''
        require(count == row['count'], f"rewrite {row['from']}: expected {row['count']} references, found {count}{suffix}")
    for key, doc in plan['docstrings'].items():
        require(key in doc_targets, f'unknown or ambiguous docstring declaration: {key}')
        d = doc_targets[key]
        rendered = '/-- ' + doc.strip() + ' -/'
        if d['doc']:
            edit(d['doc']['start'], d['doc']['end'], rendered)
        else:
            offset = d['attribute_start']
            separator = ' ' if 'parent' in d else '\n'
            insertions[offset] = insertions.get(offset, '') + rendered + separator
    for offset, value in insertions.items():
        edit(offset, offset, value)
    if plan.get('trim_trailing_whitespace', False):
        for match in re.finditer(r'[ \t]+(?=\n|\Z)', text):
            start, end = match.span()
            # Preserve literal/comment contents and spans already replaced.
            if any(t.start < end and start < t.end for t in data['tokens']):
                continue
            if any(e['start'] < end and start < e['end'] for e in edits):
                continue
            edit(start, end, '')
    edits.sort(key=lambda e: (e['start'], e['end']))
    for a, b in zip(edits, edits[1:]):
        require(a['end'] <= b['start'], f"overlapping edits at offsets {a['start']} and {b['start']}")
    return edits


def apply_edits(text, edits):
    for row in reversed(edits):
        require(text[row['start']:row['end']] == row['before'], 'edit no longer matches source')
        text = text[:row['start']] + row['after'] + text[row['end']:]
    return text


def prepare(plan, text):
    edits = compile_edits(plan, text)
    result = apply_edits(text, edits)
    plan = {**plan, 'prepared': {'instructions_sha256': instructions_hash(plan),
                              'result_sha256': digest(result), 'edits': edits}}
    return plan, result


def recover_original(plan, text):
    """Recover an applied plan's original, checking every edit and instruction."""
    validate_plan(plan)
    require('prepared' in plan, 'prior plan is not prepared')
    prepared = plan['prepared']
    require(digest(text) == prepared['result_sha256'], 'source is not the prior plan result')
    original = text
    shifted = []
    delta = 0
    for row in prepared['edits']:
        keys(row, {'start', 'end', 'before', 'after'}, {'start', 'end', 'before', 'after'}, 'prepared edit')
        require(type(row['start']) is int and type(row['end']) is int and 0 <= row['start'] <= row['end'], 'invalid prepared edit offsets')
        require(isinstance(row['before'], str) and isinstance(row['after'], str), 'invalid prepared edit text')
        shifted.append((row['start'] + delta, row))
        delta += len(row['after']) - len(row['before'])
    for start, row in reversed(shifted):
        require(original[start:start + len(row['after'])] == row['after'], 'applied edit does not match prepared payload')
        original = original[:start] + row['before'] + original[start + len(row['after']):]
    fresh, result = prepare(plan, original)
    require(fresh['prepared'] == prepared and result == text, 'prepared edits do not match reviewed instructions')
    return original


def reviewed_input(plan, text, prior=None):
    """Accept an exact original, final result or explicitly checked prior result."""
    if digest(text) in {plan['source_sha256'], plan.get('prepared', {}).get('result_sha256')}:
        return text
    require(prior is not None, 'source differs from the reviewed original and result; supply its prior plan')
    require(prior['path'] == plan['path'] and prior['source_sha256'] == plan['source_sha256'],
            'prior plan must describe the same file and reviewed original')
    return recover_original(prior, text)


def require_documentation(text):
    """Check source declarations and members have docs; reject unknown member forms."""
    data = inventory(text)
    require(not data['unsupported_children'], f'unsupported member forms: {data["unsupported_children"]}')
    missing = [d['key'] for d in data['declarations'] + data['children'] if not d['doc']]
    require(not missing, f'missing docstrings: {missing}')


def apply_plan(plan, text):
    validate_plan(plan)
    require('prepared' in plan, 'plan is not prepared; run prepare first')
    prepared = plan['prepared']
    keys(prepared, {'instructions_sha256', 'result_sha256', 'edits'}, {'instructions_sha256', 'result_sha256', 'edits'}, 'prepared')
    require(prepared['instructions_sha256'] == instructions_hash(plan), 'instructions changed after preparation; prepare again')
    if digest(text) == prepared['result_sha256']:
        # Recover the reviewed original and recompile even on repeated runs.
        # A result digest alone must not turn a corrupt plan into a valid no-op.
        recover_original(plan, text)
        return text
    fresh, result = prepare(plan, text)
    require(fresh['prepared'] == prepared, 'prepared edits do not match reviewed instructions')
    return result


def atomic_write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    mode = path.stat().st_mode if path.exists() else 0o644
    pending = None
    try:
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=path.parent, prefix=path.name + '.', delete=False) as handle:
            pending = Path(handle.name)
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        pending.chmod(mode)
        os.replace(pending, path)
    finally:
        if pending is not None:
            pending.unlink(missing_ok=True)


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f'duplicate JSON key: {key}')
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['inspect', 'prepare', 'check', 'diff', 'apply'])
    parser.add_argument('input', type=Path, help='Lean source for inspect, JSON plan otherwise')
    parser.add_argument('--prior-plan', type=Path, help='explicit earlier plan currently applied to the same original')
    parser.add_argument('--require-docs', action='store_true', help='require documentation for declarations and source members')
    args = parser.parse_args(argv)
    try:
        if args.command == 'inspect':
            path = args.input.resolve()
            text = path.read_text()
            data = inventory(text)
            print(encoded({'schema': SCHEMA, 'path': path.relative_to(ROOT).as_posix(), 'source_sha256': digest(text),
                           'imports': data['imports'], 'declarations': data['declarations'],
                           'children': data['children'], 'unsupported_children': data['unsupported_children'],
                           'syntax_commands': data['syntax_commands'],
                           'qualified_identifiers': sorted({t.text for t in data['tokens'] if t.kind == 'ident' and '.' in t.text})}), end='')
            return 0
        plan = read_json(args.input)
        validate_plan(plan)
        path = source_path(plan)
        text = path.read_text()
        original = reviewed_input(plan, text, read_json(args.prior_plan) if args.prior_plan else None)
        if args.command == 'prepare':
            if 'prepared' in plan and digest(text) == plan['prepared']['result_sha256']:
                apply_plan(plan, text)
                if args.require_docs:
                    require_documentation(text)
                print(f'already applied: {plan["path"]}')
                return 0
            plan, result = prepare(plan, original)
            if args.require_docs:
                require_documentation(result)
            atomic_write(args.input, encoded(plan))
            print(f'prepared {len(plan["prepared"]["edits"])} edits: {plan["path"]}')
            return 0
        result = apply_plan(plan, original)
        if args.require_docs:
            require_documentation(result)
        if args.command == 'diff':
            sys.stdout.writelines(difflib.unified_diff(text.splitlines(True), result.splitlines(True), fromfile=plan['path'], tofile=plan['path']))
        elif args.command == 'apply':
            if result != text:
                atomic_write(path, result)
            print(f'{"applied" if result != text else "already applied"}: {plan["path"]}')
        else:
            print(f'valid {"applied" if result == text else "pending"} plan: {plan["path"]}')
        return 0
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(f'module-style: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
