"""Rank Lean files whose code repeats long namespace-shaped prefixes.

This lexical review aid does not resolve names or prove that an opening is safe.
It ignores comments, literals, explicit and notation quotations, declaration
names and scope/import commands. Namespace components follow the repository's
capitalization convention, apart from established lower-case project roots.
Reports never rewrite sources.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from collections import defaultdict
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from scripts.module_style.core import NAME, lex, mask
from scripts.paths import ROOT

LOWER_ROOTS = {"formalisations", "papers", "scripts", "checkpoint",
               "observations", "saved", "benchmarks", "profiling"}
COMMAND = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*"
    r"(import|namespace|section|open|export|end|with_weak_namespace)\b[^\n]*")
NOTATION = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|local|scoped|meta)[ \t]+)*"
    r"(?:notation|infixl|infixr|infix|prefix|postfix)\b")
DECL_START = re.compile(
    r"(?:(?:public|private|protected|meta|unsafe|partial|noncomputable)[ \t]+)*"
    r"(?:def|abbrev|opaque|theorem|lemma|structure|inductive|class|instance|axiom)\b")
DECLARATION = re.compile(
    r"\b(?:class\s+inductive|def|abbrev|opaque|theorem|lemma|structure|"
    r"inductive|class|instance|axiom)\s+(" + NAME.pattern + r")")


@dataclass(frozen=True)
class Thresholds:
    """Minimum size and repetition required for an independently reported prefix."""

    min_uses: int = 6
    min_components: int = 3
    min_prefix_chars: int = 24
    min_lines: int = 3

    def __post_init__(self):
        if self.min_uses < 2 or min(self.min_components, self.min_prefix_chars, self.min_lines) < 1:
            raise ValueError("min-uses must be at least 2; other thresholds must be positive")


def masked_code(source, tokens):
    """Hide syntax quotations as well as the lexer's comments and literal spans."""
    code = mask(source, tokens)
    chars, position = list(code), 0
    while (start := code.find("`(", position)) >= 0:
        finish, depth = start + 2, 1
        while finish < len(code) and depth:
            depth += (code[finish] == "(") - (code[finish] == ")")
            finish += 1
        if depth:
            raise ValueError("unterminated Lean syntax quotation")
        for index in range(start, finish):
            if chars[index] not in "\r\n":
                chars[index] = " "
        position = finish
    return "".join(chars)


def notation_spans(code):
    """Keep implicit notation quotations intact, including conventional multiline RHSs."""
    spans = []
    for match in NOTATION.finditer(code):
        start = match.start()
        indent = len(code[start:match.end()]) - len(code[start:match.end()].lstrip())
        finish = code.find("\n", match.end())
        finish = len(code) if finish < 0 else finish
        def depth_change(line):
            plain = re.sub(r"«[^»]*»", "", line)
            return sum(plain.count(left) - plain.count(right)
                       for left, right in (("(", ")"), ("[", "]"), ("{", "}")))
        depth = depth_change(code[start:finish])
        position = finish + 1
        while position < len(code):
            end = code.find("\n", position)
            end = len(code) if end < 0 else end
            line = code[position:end]
            stripped = line.lstrip()
            if not stripped:
                position = end + 1
                continue
            next_indent = len(line) - len(stripped)
            boundary = stripped.startswith(("@[", "#")) or DECL_START.match(stripped)
            if depth == 0 and (boundary or next_indent <= indent):
                break
            finish = end
            depth += depth_change(line)
            position = end + 1
        spans.append((start, finish))
    return spans


def command_spans(code, tokens):
    """Exclude complete conventional multiline headers, preserving local-open bodies."""
    visible = [token for token in tokens if token.kind == "ident"
               and not code[token.start].isspace()]
    local_ins = [token.start for token in visible if token.text == "in"]
    commands = {match.start(1): (match.start(), match.end(), match[1])
                for match in COMMAND.finditer(code)}
    # Local openings can occur after another command on the same line.
    for token in visible:
        if token.text == "open":
            end = code.find("\n", token.end)
            commands.setdefault(token.start, (token.start, len(code) if end < 0 else end, "open"))
    spans = notation_spans(code)
    for keyword, (start, finish, kind) in sorted(commands.items()):
        line_start = code.rfind("\n", 0, keyword) + 1
        indent = len(code[line_start:keyword]) - len(code[line_start:keyword].lstrip())
        # Namespace names are opaque to delimiter counting, including escaped identifiers.
        def depth_change(line):
            plain = re.sub(r"«[^»]*»", "", line)
            return sum(plain.count(left) - plain.count(right) for left, right in (("(", ")"), ("[", "]")))
        depth = depth_change(code[keyword:finish])
        position = finish + 1
        while position < len(code):
            end = code.find("\n", position)
            end = len(code) if end < 0 else end
            line = code[position:end]
            stripped = line.lstrip()
            if not stripped:
                position = end + 1
                continue
            next_indent = len(line) - len(stripped)
            first = NAME.match(stripped)
            word = first[0] if first else ""
            clause = word in {"renaming", "hiding", "scoped", "in"}
            # A new command must remain visible even when indented beyond the opening.
            boundary = (stripped.startswith(("@[", "#")) or
                        (word and word[0].islower() and word not in LOWER_ROOTS and not clause))
            if depth == 0 and (boundary or (next_indent <= indent and not clause)):
                break
            finish = end
            depth += depth_change(line)
            position = end + 1
            if kind == "open":
                index = bisect_left(local_ins, keyword)
                if index < len(local_ins) and local_ins[index] < finish:
                    break
        if kind == "open":
            index = bisect_left(local_ins, keyword)
            if index < len(local_ins) and local_ins[index] < finish:
                finish = local_ins[index] + 2
        spans.append((start, finish))
    # Combine overlapping headers so a nested interval cannot expose its outer tail.
    merged = []
    for start, finish in sorted(spans):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], finish))
        else:
            merged.append((start, finish))
    return merged


def references(source):
    """Locate namespace-shaped uses, retaining original names and source positions."""
    tokens = lex(source)
    code = masked_code(source, tokens)
    blocked = command_spans(code, tokens)
    starts = [start for start, _ in blocked]
    declarations = {match.start(1) for match in DECLARATION.finditer(code)}
    newlines = [-1] + [match.start() for match in re.finditer("\n", source)]
    result = []
    for token in tokens:
        if token.kind != "ident" or "." not in token.text or code[token.start].isspace():
            continue
        index = bisect_right(starts, token.start) - 1
        if index >= 0 and token.start < blocked[index][1]:
            continue
        if token.start in declarations or source[max(0, token.start - 1):token.start] in {"`", "$"}:
            continue
        parts = re.findall(r"«[^»]*»|[^.]+", token.text.removeprefix("_root_."))
        # A lower-case head usually denotes a local variable's field chain.
        first = parts[0].removeprefix("«")
        if not first or not (first[0].isupper() or first in LOWER_ROOTS):
            continue
        namespace_length = 1
        for part in parts[1:-1]:
            if not part.removeprefix("«")[:1].isupper():
                break
            namespace_length += 1
        line = bisect_right(newlines, token.start)
        result.append({"name": token.text, "parts": parts, "namespace_length": namespace_length,
                       "line": line, "column": token.start - newlines[line - 1],
                       "start": token.start, "end": token.end})
    return result


def inspect_source(path: str, source: str, thresholds: Thresholds = Thresholds()) -> dict:
    """Greedily rank disjoint occurrences so nested prefix scores are not added twice."""
    refs = references(source)
    groups = defaultdict(list)
    for index, ref in enumerate(refs):
        for length in range(thresholds.min_components,
                            min(len(ref["parts"]) - 1, ref["namespace_length"]) + 1):
            prefix = ".".join(ref["parts"][:length])
            if len(prefix) >= thresholds.min_prefix_chars:
                groups[prefix].append(index)
    claimed, findings = set(), []
    while groups:
        candidates = []
        for prefix, indices in groups.items():
            available = [index for index in indices if index not in claimed]
            lines = sorted({refs[index]["line"] for index in available})
            if len(available) >= thresholds.min_uses and len(lines) >= thresholds.min_lines:
                # Characters spent writing the same prefix after its first use.
                score = (len(available) - 1) * (len(prefix) + 1)
                candidates.append((score, prefix, available, lines))
        if not candidates:
            break
        score, prefix, indices, lines = min(candidates, key=lambda row: (-row[0], row[1]))
        claimed.update(indices)
        del groups[prefix]
        examples = {}
        for index in indices:
            ref = refs[index]
            examples.setdefault(ref["name"], {key: ref[key] for key in ("name", "line", "column")})
        findings.append({"prefix": prefix, "uses": len(indices), "lines": lines,
                         "repeated_chars": score, "examples": list(examples.values())[:3]})
    return {"path": path, "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "qualified_references": len(refs), "prefixes": findings,
            "repeated_chars": sum(row["repeated_chars"] for row in findings)}


def discover(paths: list[Path], root: Path = ROOT) -> list[Path]:
    """Select explicit files or every tracked/unignored current Lean source using Git."""
    if paths:
        selected = [path.resolve() for path in paths]
        if any(path.suffix != ".lean" or not path.is_file() for path in selected):
            raise ValueError("explicit scope requires existing .lean files")
    else:
        output = subprocess.check_output(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
            cwd=root)
        selected = sorted({root / name.decode("utf-8") for name in output.split(b"\0") if name})
        selected = [path for path in selected if path.is_file()]
    if not selected or len(selected) != len(set(selected)):
        raise ValueError("source scope must be nonempty and contain distinct files")
    return sorted(selected)


def main(argv=None) -> int:
    """Print the review list; only explicit --check mode fails because of findings."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path, help="Lean files; default: all current Git-visible sources")
    for field, default in asdict(Thresholds()).items():
        parser.add_argument("--" + field.replace("_", "-"), type=int, default=default)
    parser.add_argument("--json", action="store_true", help="emit the complete report, ignoring --limit")
    parser.add_argument("--limit", type=int, default=20, help="maximum files to print; 0 prints all (default: 20)")
    parser.add_argument("--check", action="store_true", help="exit 1 when review candidates are present")
    args = parser.parse_args(argv)
    try:
        thresholds = Thresholds(**{field: getattr(args, field) for field in asdict(Thresholds())})
        if args.limit < 0:
            raise ValueError("limit must be nonnegative")
        paths = discover(args.files)
        rows = []
        for path in paths:
            label = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
            row = inspect_source(label, path.read_bytes().decode("utf-8"), thresholds)
            if row["prefixes"]:
                rows.append(row)
        rows.sort(key=lambda row: (-row["repeated_chars"], row["path"]))
        report = {"schema": 1, "thresholds": asdict(thresholds), "scanned_files": len(paths),
                  "flagged_files": len(rows), "files": rows}
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
        else:
            print(f"Namespace repetition: {len(rows)} of {len(paths)} files flagged "
                  f"(uses >= {thresholds.min_uses}, components >= {thresholds.min_components}, "
                  f"prefix chars >= {thresholds.min_prefix_chars}, lines >= {thresholds.min_lines}).")
            for row in rows[:args.limit or None]:
                print(f"\n{row['path']} ({row['repeated_chars']} repeated prefix characters)")
                for prefix in row["prefixes"]:
                    first = prefix["examples"][0]
                    print(f"  :{first['line']}  {prefix['uses']} uses on {len(prefix['lines'])} lines: "
                          f"{prefix['prefix']}")
                    print("    e.g. " + first["name"])
            if args.limit and len(rows) > args.limit:
                print(f"\n{len(rows) - args.limit} further files; use --limit 0 or --json for all.")
            print("\nReview candidates only: check namespace ownership, collisions and retained syntax before editing.")
        return 1 if args.check and rows else 0
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"namespace-prefix analysis failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
