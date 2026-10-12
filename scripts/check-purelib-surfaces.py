#!/usr/bin/env python3
"""Check current library, publication, example and executable source coverage."""

from paths import bootstrap
bootstrap()
from scripts.verification.surfaces import main


if __name__ == "__main__":
    raise SystemExit(main())
