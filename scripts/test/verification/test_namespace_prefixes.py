"""Check lexical exclusions, ranking and CLI failure semantics for namespace reports."""

import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.verification import namespace_prefixes as checker

PREFIX = "Purelib.ReallyLongSubject.DeepNamespace"


def fixture(prefix=PREFIX, count=6):
    return "module\n" + "".join(f"def value{index} := {prefix}.item{index}\n" for index in range(count))


class NamespacePrefixTests(unittest.TestCase):
    def inspect(self, source, **thresholds):
        return checker.inspect_source("Fixture.lean", source, checker.Thresholds(**thresholds))

    def test_repetition_reports_exact_names_positions_and_score(self):
        source = fixture()
        row = self.inspect(source)
        self.assertEqual(row["qualified_references"], 6)
        self.assertEqual(len(row["prefixes"]), 1)
        finding = row["prefixes"][0]
        self.assertEqual(finding["prefix"], PREFIX)
        self.assertEqual(finding["uses"], 6)
        self.assertEqual(finding["lines"], list(range(2, 8)))
        self.assertEqual(finding["repeated_chars"], 5 * (len(PREFIX) + 1))
        example = finding["examples"][0]
        self.assertEqual(example["line"], 2)
        line = source.splitlines()[example["line"] - 1]
        self.assertEqual(line[example["column"] - 1:], example["name"])

    def test_comments_literals_and_syntax_or_name_quotations_are_ignored(self):
        forms = [
            lambda name: f"-- {name}",
            lambda name: f"/-- {name} /- {name} -/ -/",
            lambda name: f'def x := "{name}"',
            lambda name: f'def x := r##"{name}"##',
            lambda name: f"def x := `{name}",
            lambda name: f"def x := ``{name}",
            lambda name: f"def x := `({name})",
            lambda name: f"def x := `(tactic| exact {name})",
        ]
        for form in forms:
            with self.subTest(form=form(PREFIX + ".item")):
                self.assertEqual(self.inspect("\n".join(
                    form(PREFIX + ".item") for _ in range(6)))["prefixes"], [])

    def test_imports_scopes_openings_exports_and_declaration_heads_are_ignored(self):
        for command in ("import", "public meta import all", "namespace", "end",
                        "open", "open scoped", "export", "with_weak_namespace", "section", "public section"):
            with self.subTest(command=command):
                self.assertEqual(self.inspect(
                    "\n".join(command + " " + PREFIX for _ in range(6)))["prefixes"], [])
        for kind in ("def", "theorem", "structure", "inductive", "class inductive"):
            with self.subTest(kind=kind):
                text = "\n".join(f"{kind}\n  {PREFIX}.item{index} := 1" for index in range(6))
                self.assertEqual(self.inspect(text)["prefixes"], [])

    def test_notation_expansions_are_implicit_quotations(self):
        for kind in ("notation", "local notation", "scoped notation", "public notation",
                     "local infixl:70", "infixr:60", "infix:50", "prefix:80", "postfix:max"):
            with self.subTest(kind=kind):
                source = "\n".join(f'{kind} "token{index}" => {PREFIX}.item{index}'
                                   for index in range(6))
                self.assertEqual(self.inspect(source)["prefixes"], [])

    def test_multiline_notation_preserves_following_real_code(self):
        expansion = "\n".join(f"    {PREFIX}.item{index} x" for index in range(6))
        for rhs in ("(\n  fun x => [\n" + expansion + "\n  ]\n)",
                    "fun x =>\n  open Other.Namespace in\n  [\n" + expansion + "\n  ]"):
            with self.subTest(rhs=rhs):
                source = 'local notation "N" =>\n  ' + rhs + "\n\n" + fixture()
                finding = self.inspect(source)["prefixes"][0]
                self.assertEqual(finding["uses"], 6)
        source = 'local notation "N" => ' + PREFIX + ".item\n" + "\n".join(
            f"  def x{index} := {PREFIX}.item{index}" for index in range(6))
        self.assertEqual(self.inspect(source)["prefixes"][0]["uses"], 6)

    def test_same_line_local_open_preserves_following_references(self):
        source = "\n".join(
            f"open Other.Long.Namespace in def x{index} := {PREFIX}.item{index}" for index in range(6))
        finding = self.inspect(source)["prefixes"][0]
        self.assertEqual(finding["prefix"], PREFIX)
        self.assertEqual(finding["uses"], 6)

    def test_multiline_open_import_and_selected_names_are_not_references(self):
        names = "\n".join(f"  {PREFIX}.Namespace{index}" for index in range(8))
        for command in ("open", "import", "public meta import all"):
            with self.subTest(command=command):
                source = command + "\n" + names + "\n\ndef scalar := 1\n"
                self.assertEqual(self.inspect(source)["prefixes"], [])
        selected = "open Owner (\n" + names + "\n)\n"
        self.assertEqual(self.inspect(selected)["prefixes"], [])

    def test_multiline_and_nested_local_open_bodies_remain_visible(self):
        source = "\n".join(
            f"open\n  Other.Long.Namespace\nin\n  def x{index} := {PREFIX}.item{index}"
            for index in range(6))
        self.assertEqual(self.inspect(source)["prefixes"][0]["uses"], 6)
        source = "\n".join(
            f"open Other.Long.Namespace in open Other.Second.Namespace in "
            f"def x{index} := {PREFIX}.item{index}" for index in range(6))
        self.assertEqual(self.inspect(source)["prefixes"][0]["uses"], 6)

    def test_indented_declarations_after_shared_open_still_count(self):
        source = "open Other.Long.Namespace\n" + "\n".join(
            f"  def x{index} := {PREFIX}.item{index}" for index in range(6))
        self.assertEqual(self.inspect(source)["prefixes"][0]["uses"], 6)

    def test_escaped_opening_names_are_not_mistaken_for_local_in(self):
        source = "\n".join("open Other.«in»." + PREFIX for _ in range(6))
        self.assertEqual(self.inspect(source)["prefixes"], [])

    def test_source_hash_and_positions_preserve_crlf_and_unicode(self):
        source = fixture("Purelib.ReallyLongSubject.ΔNamespace").replace("\n", "\r\n")
        row = self.inspect(source)
        self.assertEqual(row["source_sha256"], hashlib.sha256(source.encode()).hexdigest())
        self.assertEqual(row["prefixes"][0]["lines"], list(range(2, 8)))
        for ref in checker.references(source):
            self.assertEqual(source[ref["start"]:ref["end"]], ref["name"])

    def test_local_field_chains_and_lowercase_function_components_are_not_namespaces(self):
        self.assertEqual(self.inspect(fixture("owner.cached.preparedData"))["prefixes"], [])
        # Long paths through a function's result are not longer namespace candidates.
        refs = checker.references(fixture(PREFIX + ".builder.Result"))
        self.assertTrue(all(ref["namespace_length"] == 3 for ref in refs))

    def test_roots_and_escaped_components_are_counted_correctly(self):
        source = fixture() + fixture("_root_." + PREFIX)
        self.assertEqual(self.inspect(source)["prefixes"][0]["uses"], 12)
        escaped = "Purelib.«Really.Long.Subject».DeepNamespace"
        self.assertEqual(self.inspect(fixture(escaped))["prefixes"][0]["prefix"], escaped)
        lower = "formalisations.ReallyLongSubject.DeepNamespace"
        self.assertEqual(self.inspect(fixture(lower))["prefixes"][0]["prefix"], lower)

    def test_thresholds_are_joint_and_configurable(self):
        self.assertEqual(self.inspect(fixture(count=5))["prefixes"], [])
        self.assertTrue(self.inspect(fixture(count=5), min_uses=5)["prefixes"])
        self.assertEqual(self.inspect(fixture(), min_components=4)["prefixes"], [])
        self.assertEqual(self.inspect(fixture(), min_prefix_chars=100)["prefixes"], [])
        self.assertEqual(self.inspect(fixture(), min_lines=7)["prefixes"], [])
        self.assertEqual(self.inspect("def x := [" + ", ".join(
            PREFIX + ".item" for _ in range(12)) + "]")["prefixes"], [])

    def test_nested_candidates_do_not_double_count_and_residual_branches_survive(self):
        source = fixture(PREFIX + ".ExtremelyLongNestedNamespace", 20) + fixture(PREFIX + ".Other", 6)
        row = self.inspect(source)
        self.assertEqual(len(row["prefixes"]), 2)
        self.assertEqual(sum(finding["uses"] for finding in row["prefixes"]), 26)
        self.assertEqual(row["qualified_references"], 26)
        self.assertEqual(row["repeated_chars"], sum(
            finding["repeated_chars"] for finding in row["prefixes"]))

    def test_malformed_input_and_invalid_thresholds_fail(self):
        for source in ("/- unterminated", 'def x := "unterminated', "def x := `(unterminated"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.inspect(source)
        for overrides in ({"min_uses": 1}, {"min_components": 0}, {"min_prefix_chars": -1},
                          {"min_lines": 0}):
            with self.subTest(overrides=overrides), self.assertRaises(ValueError):
                checker.Thresholds(**overrides)

    def test_git_discovery_includes_untracked_sources_and_excludes_ignored_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text(".lake/\n")
            (root / "Tracked.lean").write_text("module\n")
            subprocess.run(["git", "add", "Tracked.lean"], cwd=root, check=True)
            (root / "New.lean").write_text(fixture())
            (root / ".lake").mkdir()
            (root / ".lake/Generated.lean").write_text(fixture())
            self.assertEqual(checker.discover([], root),
                             [root / "New.lean", root / "Tracked.lean"])

    def test_cli_json_check_mode_and_invalid_scopes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Flagged.lean"
            path.write_text(fixture())
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(checker.main([str(path), "--json", "--check"]), 1)
            report = json.loads(output.getvalue())
            self.assertEqual((report["scanned_files"], report["flagged_files"]), (1, 1))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(checker.main([str(path)]), 0)
            for paths in ([path, path], [path.with_suffix(".txt")]):
                with self.subTest(paths=paths), self.assertRaises(ValueError):
                    checker.discover(paths)
            with self.assertRaisesRegex(ValueError, "nonempty"):
                subprocess.run(["git", "init", "-q", directory], check=True)
                path.unlink()
                checker.discover([], Path(directory))


if __name__ == "__main__":
    unittest.main()
