#!/usr/bin/env python3
"""Read checked compiled module data through the pinned backend."""

from paths import bootstrap
bootstrap()
from scripts.lean_module_data.cli import main


if __name__ == '__main__':
    import sys
    try:
        main()
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
