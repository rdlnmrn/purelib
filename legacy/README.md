# Archived implementation modules

This directory preserves the superseded CCL and FTA implementation paths for
historical comparison.  They are intentionally outside the active `CCL` and
`FTA` Lake libraries and are not imported by either `CCL.Paper` or
`FTA.Paper`.

The archived files retain their original module imports and are not maintained
as a separately buildable library.  The warning-fatal repository build checks
only the finite constructive implementation under the top-level `CCL/` and
`FTA/` directories.
