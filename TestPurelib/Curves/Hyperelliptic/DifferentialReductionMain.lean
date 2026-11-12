module

import TestPurelib.Curves.Hyperelliptic.DifferentialReduction
import TestPurelib.Curves.Hyperelliptic.InfinityCoefficients

/-- Execute exact differential reduction and infinity-coefficient regressions in both curve parities. -/
public def main : IO Unit := do
  TestPurelib.Curves.Hyperelliptic.DifferentialReduction.run
  TestPurelib.Curves.Hyperelliptic.InfinityCoefficients.run
