"""Check current Lake ownership, facade reachability and publication boundaries."""

from collections import defaultdict, deque
from pathlib import Path
import sys
import tomllib

from scripts.paths import ROOT
from scripts.verification import modules, sources


PROJECT_PREFIXES = {"Purelib", "TestPurelib", "scripts", "papers", "formalisations"}
PUBLICATION_ROOTS = {"papers.CCL.CCL", "papers.RFAP.RFAP", "papers.RFAP.RFAP2",
                     "formalisations.DivineProportions.DivineProportions",
                     "formalisations.RationalRotations.RationalRotations",
                     "formalisations.MinkowskiRotations.MinkowskiRotations"}


def closure(graph, roots):
    """Follow exact current project imports and reject absent selected roots."""
    seen, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if name not in graph:
            raise ValueError("missing project module: " + name)
        seen.add(name)
        pending.extend(graph[name] - seen)
    return seen


def target_sources(target, active, root=ROOT):
    """Resolve current Lake roots and recursive namespace globs against sources."""
    if target.get("srcDir", ".") != ".":
        raise ValueError("unsupported Lake source directory: " + target["name"])
    patterns = target.get("roots", []) + target.get("globs", [])
    if "root" in target:
        patterns = [*patterns, target["root"]]
    result = set()
    for pattern in patterns:
        if pattern.endswith(".+"):
            matches = {name for name in active if name.startswith(pattern[:-1])}
            if not matches and (Path(root) / pattern[:-2].replace(".", "/")).is_dir():
                continue  # Retained empty namespace directories are valid Lake globs.
        else:
            matches = {pattern} & active
        if not matches:
            raise ValueError(f"Lake target {target['name']} has an empty or missing source pattern: {pattern}")
        result.update(matches)
    if not result:
        raise ValueError("Lake target has no current source ownership: " + target["name"])
    return result


def check_test_dependencies(graph):
    """Keep mathematical sources independent of regressions, including through tools."""
    parents = defaultdict(set)
    for owner, dependencies in graph.items():
        for dependency in dependencies:
            parents[dependency].add(owner)
    routes = {name: [name] for name in graph if name.startswith("TestPurelib.")}
    pending = deque(sorted(routes))
    while pending:
        dependency = pending.popleft()
        for owner in sorted(parents[dependency]):
            if owner not in routes:
                routes[owner] = [owner, *routes[dependency]]
                pending.append(owner)
    violations = [" -> ".join(routes[name]) for name in sorted(routes)
                  if name.startswith(("Purelib.", "papers.", "formalisations."))]
    if violations:
        raise ValueError("mathematical sources depend on regression modules: " + "; ".join(violations))


def check(config, graph, root=ROOT):
    """Check current coverage without a historical provider or relocation ledger."""
    active = set(graph)
    targets = [*config.get("lean_lib", []), *config.get("lean_exe", [])]
    names = [target["name"] for target in targets]
    if len(names) != len(set(names)):
        raise ValueError("duplicate Lake target name")
    defaults = config.get("defaultTargets", [])
    if set(defaults) != set(names) or len(defaults) != len(set(defaults)):
        raise ValueError("defaultTargets must select every declared library and executable exactly once")
    owners, selected = defaultdict(set), set()
    for target in targets:
        selected.update(target_sources(target, active, root))
    for target in config.get("lean_lib", []):
        for name in target_sources(target, active, root):
            owners[name].add(target["name"])
    overlapping = {name: sorted(labels) for name, labels in owners.items() if len(labels) > 1}
    if overlapping:
        raise ValueError("overlapping Lake library owners: " + str(overlapping))
    if missing := active - closure(graph, selected):
        raise ValueError("Lake targets omit active sources: " + ", ".join(sorted(missing)))
    check_test_dependencies(graph)
    for facade in PUBLICATION_ROOTS:
        closure(graph, [facade])
    ccl = closure(graph, ["papers.CCL.CCL"])
    required = {"papers.CCL.Chapters.Paper", "papers.CCL.Chapters.Bridge", "papers.RFAP.Chapters.Paper"}
    if missing := required - ccl:
        raise ValueError("CCL facade omits required publication providers: " + ", ".join(sorted(missing)))
    for facade in ("Purelib.Library", "Purelib.Measure", "Purelib.Riemann", "Purelib.Geometry",
                 "Purelib.Geometry.Rotations", "Purelib.Curves"):
        dependencies = closure(graph, [facade])
        foreign = {name for name in dependencies if name.startswith(
            ("Purelib.Examples.", "TestPurelib.", "papers.", "formalisations.", "scripts."))}
        if foreign:
            raise ValueError(f"reusable facade {facade} reaches optional/publication/tool sources: {sorted(foreign)}")
    examples = {name for name in active if name.startswith("Purelib.Examples.")}
    example_targets = [target for target in config.get("lean_lib", []) if target["name"] == "PurelibExamples"]
    example_coverage = closure(graph, ["Purelib.Examples.All"])
    for target in example_targets:
        example_coverage.update(target_sources(target, active, root))
    if missing := examples - example_coverage:
        raise ValueError("optional example facade and library omit active examples: " + ", ".join(sorted(missing)))
    # Standalone main declarations require isolated executable import closures.
    executable_roots = [target["root"] for target in config.get("lean_exe", [])
                        if target["root"].startswith("TestPurelib.")]
    tests = {name for name in active if name.startswith("TestPurelib.")}
    if missing := tests - closure(graph, ["TestPurelib.All", *executable_roots]):
        raise ValueError("test facade and standalone executables omit regressions: " + ", ".join(sorted(missing)))


def inspect(root=ROOT):
    """Read the authoritative active sources and direct project import graph."""
    root = Path(root)
    paths, _ = modules.discover(include_scripts=True, root=root)
    if not paths:
        raise ValueError("surface check has an empty active inventory")
    graph = {path.removesuffix(".lean").replace("/", "."): set() for path in paths}
    for path in paths:
        name = path.removesuffix(".lean").replace("/", ".")
        for dependency, _ in sources.imports((root / path).read_text(encoding="utf-8")):
            if dependency.startswith(("legacy.", "CCL.Constructive.")):
                raise ValueError(f"retired implementation import: {name} -> {dependency}")
            if dependency.split(".")[0] not in PROJECT_PREFIXES:
                continue
            if dependency not in graph:
                raise ValueError(f"missing current project import: {name} -> {dependency}")
            graph[name].add(dependency)
    check(tomllib.loads((root / "lakefile.toml").read_text()), graph, root)
    return graph


def main():
    try:
        graph = inspect()
        print(f"Current Purelib surfaces cover {len(graph)} active modules and all declared targets")
        return 0
    except (OSError, UnicodeError, ValueError, KeyError) as error:
        print(f"Purelib surface check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
