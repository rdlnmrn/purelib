"""Read compiled declaration graphs and input headers without producing checker streams."""

import sys

from scripts.lean_module_data.export import main as read_graph
from scripts.lean_module_data.paths import search_path


def main():
    """Keep the raw-reader diagnostic contract separate from native proof export."""
    args = sys.argv[1:]
    if args == ['--metadata'] or len(args) == 3 and args[0] in ('--graph', '--module-inputs'):
        read_graph(args, search_path())
    else:
        raise SystemExit('usage: graph_data --metadata | --graph MANIFEST OUTPUT | --module-inputs MANIFEST OUTPUT')


if __name__ == '__main__':
    main()
