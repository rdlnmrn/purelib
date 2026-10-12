"""Shared repository startup for retained Python command frontdoors."""

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent


def bootstrap():
    """Make ordinary repository package imports available from any working directory."""
    value = str(ROOT)
    if value not in sys.path:
        sys.path.insert(0, value)
    return ROOT
