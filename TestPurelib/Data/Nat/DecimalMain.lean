module
import TestPurelib.Data.Nat.Decimal
import Purelib.System.IO

/-- Check complete decimal bytes across caches, word boundaries, large values and signed prefixes. -/
public def main : IO Unit := do
  TestPurelib.Data.Nat.Decimal.check
  Purelib.System.IO.println "decimal rendering: original edge cases and all-input byte readbacks checked"
