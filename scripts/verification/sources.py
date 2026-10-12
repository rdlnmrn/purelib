"""Current Lean source headers and lexical declaration ownership.

These source facts support policy and coverage checks; compiled metadata remains
authoritative for visibility, elaboration and mathematical dependency closures.
"""

import re

from scripts.module_style.core import lex, mask


IMPORT = re.compile(r"(?:(public|private)\s+)?(?:(meta)\s+)?import(?:\s+(all))?\s+(.+)")


def code(source, quoted_input=False):
    """Mask comments and literals while retaining exact offsets and newlines."""
    masked = mask(source, lex(source))
    if not quoted_input:
        return masked
    # Lean syntax quotations in regression inputs are data. Balance their
    # parentheses after masking strings/comments so inner delimiters are safe.
    chars, position = list(masked), 0
    while match := re.search(r"`\(\s*\w+\s*\|", masked[position:]):
        start = position + match.start()
        finish, depth = position + match.end(), 1
        while finish < len(masked) and depth:
            if masked[finish] == "(":
                depth += 1
            elif masked[finish] == ")":
                depth -= 1
            finish += 1
        if depth:
            raise ValueError("unterminated Lean syntax quotation")
        for index in range(start, finish):
            if chars[index] not in "\r\n":
                chars[index] = " "
        position = finish
    return "".join(chars)


def imports(source):
    """Read all module-header imports and their retained visibility/phase modes."""
    result = []
    for line in code(source).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        if not (match := IMPORT.fullmatch(line)):
            break
        mode = " ".join(part for part in match.groups()[:3] if part) or "ordinary"
        result.extend((name, mode) for name in match[4].split())
    return result


def explicit(source):
    """Determine whether the source opts into Lean's explicit module system."""
    return bool(re.search(r"(?m)^\s*module\s*$", code(source)))


DECL = re.compile(r"^\s*(?:@\[[^]]+\]\s*)*(?:(private|public|protected)\s+)?"
                  r"(?:noncomputable\s+|unsafe\s+|partial\s+|meta\s+)*"
                  r"(def|theorem|lemma|structure|inductive|class|abbrev|instance|opaque)\s+([^\s:{[(]+)")
NAMED_SYNTAX = re.compile(r"^\s*(?:@\[[^]]+\]\s*)*(?:(private|public|protected)\s+)?"
                         r"(?:meta\s+)?(syntax)\s+\(name\s*:=\s*([^\s)]+)\)")
SECTION = re.compile(r"^(?:@\[[^]]+\]\s*)?(?:(?:public|private|meta)\s+)?section(?:\s+[^\s]+)?$")


def namespace_and_declarations(path, source):
    """Read authored declaration names with namespace, section and mutual scopes.

    The visibility column records written modifiers, with the legacy default;
    consumers must use compiled metadata for explicit-module API visibility.
    """
    scopes, declarations = [], []
    for number, line in enumerate(code(source).splitlines(), 1):
        stripped = line.strip()
        if match := re.fullmatch(r"namespace\s+(\S+)", stripped):
            scopes.append(("namespace", match[1]))
        elif SECTION.fullmatch(stripped):
            scopes.append(("section", ""))
        elif stripped == "mutual":
            scopes.append(("mutual", ""))
        elif re.fullmatch(r"end(?:\s+\S+)?", stripped):
            if scopes:
                scopes.pop()
        elif (match := DECL.match(line) or NAMED_SYNTAX.match(line)) and match[1] != "private":
            name = match[3].rstrip(".")
            namespaces = [name for kind, name in scopes if kind == "namespace"]
            full = (name.removeprefix("_root_.") if name.startswith("_root_.")
                    else ".".join([*namespaces, name]))
            declarations.append((full, name.removeprefix("_root_."), match[2], match[1] or "public", number))
    return declarations


def declaration_contract(lines, line_number, kind):
    """Read the written declaration telescope/data fields, without proof bodies."""
    index, collected = line_number - 1, []
    data_declaration = kind in {"structure", "class", "inductive"}
    while index < len(lines):
        line, stripped = lines[index], lines[index].strip()
        if collected and data_declaration and not stripped:
            break
        if (collected and data_declaration and line and not line[0].isspace() and
                (DECL.match(line) or SECTION.match(stripped) or re.match(r"(?:namespace|end)\b", stripped))):
            break
        if collected and not data_declaration and stripped.startswith("|"):
            break
        if not data_declaration and ":=" in line:
            collected.append(line.partition(":=")[0].rstrip() + " :=")
            break
        collected.append(line.rstrip())
        if not data_declaration and (stripped.endswith(" where") or stripped == "where"):
            break
        index += 1
        if len(collected) >= 1000:
            raise ValueError(f"declaration contract exceeds 1000 lines at source line {line_number}")
    return "\\n".join(collected).replace("\t", "\\t")
