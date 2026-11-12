module

import TestPurelib.Approximation.Gaussian.Observation.Enclosure
import TestPurelib.Approximation.Gaussian.Observation.Imported

/-! # Compiled numerical-observer regression entry point -/

/-- Run the original-source and finite-code numerical-observer execution regressions. -/
public def main : IO Unit := do
  TestPurelib.Approximation.Gaussian.Observation.Enclosure.run
  TestPurelib.Approximation.Gaussian.Observation.Imported.run
