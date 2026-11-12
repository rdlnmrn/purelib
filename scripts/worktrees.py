#!/usr/bin/env python3
"""Create, inspect and retire repository task worktrees."""

from paths import bootstrap
bootstrap()
from scripts.maintenance.worktrees import main


if __name__ == "__main__":
    raise SystemExit(main())
