"""Token-preserving formatting for current generated Lean witnesses."""

def format_lean(source):
    """Render shared parent routes and bounded lines without changing Lean tokens."""
    from scripts.module_style.core import lex
    import re

    # All fixtures are standalone root modules. The single parent opening
    # preserves the full short object qualifier and every selected operation.
    rewritten = []
    for token in reversed(lex(source)):
        if token.kind != "ident" or not token.text.startswith("Purelib."):
            continue
        line = source[source.rfind("\n", 0, token.start) + 1:token.start]
        if line.lstrip().startswith(("import ", "public import ", "meta import ")):
            continue
        after = "_root_." + token.text if line.lstrip().startswith("open ") else token.text[8:]
        rewritten.append((token.start, token.end, after))
    for start, end, after in rewritten:
        source = source[:start] + after + source[end:]
    first_open = source.index("\nopen ")
    source = source[:first_open] + "\nopen Purelib\n" + source[first_open:]

    summaries = {
        "profileLog": "Flush an enabled finite replay progress message.",
        "vertexCount": "The number of retained source vertices.",
        "faceCount": "The number of retained ordered triangle occurrences.",
        "faceData": "The exact finite vector of oriented source triangles.",
        "faces": "Read the retained oriented triangle at its bounded source index.",
        "trees": "The independently generated ordered sewing trees.",
        "localPrimitiveData": "The retained primitive values on every source triangle.",
        "certified": "The checked complete sewing forest for the retained ordered triangles.",
        "rightNestedTrees": "The second retained nesting of the same ordered sewing trees.",
        "rightNestedCertified": "The checked forest for the retained right-nested sewing trees.",
        "connection": "The checked dual connection with its exact source-path witnesses.",
        "dualPathData": "The retained finite vector of source-face dual paths.",
        "singlePolygon": "The checked single sewn polygon with its complete face coverage.",
        "meshNonloop": "Every retained source edge has distinct endpoints.",
        "cutPairs": "The original cut-occurrence pairing of the retained sewn polygon.",
        "cutWord": "The ordered signed word of the retained cut-occurrence pairing.",
        "cutIntegralPairing": "The exact integral pairing of the retained signed cut word.",
        "checkedNormalForm": "The finite checked normal-form attempt for the retained pairing.",
        "cutAutomaticNormalForm": "The retained constructive normal form of the cut-word pairing.",
        "cutNormalForm": "The checked constructive normal-form certificate of the cut-word pairing.",
        "pairedLetters": "The retained paired signed letters of the cut word.",
        "checkGeneratedWord": "Compare retained signed-word reductions with their independent expected data.",
        "checkCutPairing": "Replay the retained cut pairing and compare its certificates with exact expected data.",
        "main": "Replay finite sewing, primitive, boundary and area certificates with their cached expected data.",
    }
    lines = source.splitlines(True)
    documented = []
    source_offset = 0
    doc_ends = [token.end for token in lex(source) if token.kind == "doc"]
    for line in lines:
        has_doc = any(end <= source_offset and not source[end:source_offset].strip()
                      for end in doc_ends)
        match = re.match(r"(?:(?:public|private) )?(?:def|theorem) ([A-Za-z0-9_]+)\b", line)
        if line.startswith("private instance ") and not has_doc:
            documented.append("/-- Decide boundedness of both primitive coordinates using their retained comparisons. -/\n")
        if match and not has_doc:
            name = match[1]
            words = re.sub(r"([a-z])([A-Z])", r"\1 \2", name).lower()
            summary = summaries.get(name, "The retained " + words + " for exact finite replay.")
            documented.append("/-- " + summary + " -/\n")
        documented.append(line)
        source_offset += len(line)
    source = "".join(documented)

    # Retain complete string tokens, including interpolation expressions.
    # Inserting a backslash/newline can change Lean syntax and runtime bytes.
    protected = [token for token in lex(source) if token.kind in ("string", "comment", "doc")]
    result = []
    source_offset = 0
    for line in source.splitlines():
        line_start = source_offset
        source_offset += len(line) + 1
        if any(token.start < source_offset and line_start < token.end for token in protected):
            result.append(line)
            continue
        indent = len(line) - len(line.lstrip())
        continuation = " " * (indent + 4)
        while len(line) > 120:
            # Token gaps preserve punctuation, complete location clauses and
            # tactic separators. Continuations remain inside the original term.
            tokens = lex(line)
            gaps = [(match.start(), match.end()) for match in re.finditer(r"[ \t]+", line)
                    if indent + 8 < match.start() <= 116
                    and not any(token.start <= match.start() < token.end for token in tokens)]
            if not gaps:
                raise ValueError("unbreakable generated Lean line: " + line)
            left, right = gaps[-1]
            result.append(line[:left])
            line = continuation + line[right:]
        result.append(line)
    return "\n".join(result) + "\n"
