#!/usr/bin/env python3
"""List the current authoritative project source boundary."""

from paths import bootstrap
bootstrap()
from scripts.verification.modules import main


if __name__ == '__main__':
    raise SystemExit(main())
