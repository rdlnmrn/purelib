"""Bounded comparison-only export through the retained raw compiled-record reader."""

from pathlib import Path
import sys

from scripts.lean_module_data.export import Environment, Serializer, drive
from scripts.lean_module_data.paths import search_path


def main():
    """Write exactly one bounded reference graph, without legacy production scheduling."""
    if len(sys.argv) != 3:
        raise SystemExit('usage: reference_export MANIFEST STREAM')
    modules = Path(sys.argv[1]).read_text().splitlines()
    if not modules or len(modules) != len(set(modules)):
        raise ValueError('nonempty distinct reference modules required')
    env = Environment(modules, search_path())
    roots, _ = env.roots(modules)
    with Path(sys.argv[2]).open('wb') as output:
        writer = Serializer(env, output)
        writer.metadata()
        for _, name in roots:
            drive(writer.constant(name))


if __name__ == '__main__':
    main()
