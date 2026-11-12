module

import TestPurelib.RootIsolation.SquareRoot.Newton.Observation
import TestPurelib.Integration.Algebraic.SquareFactor.CoefficientObservation
import TestPurelib.RootIsolation.CCL.Persistent.Terminal.Observation
import TestPurelib.Integration.Replay.Expansion
import TestPurelib.RootIsolation.SquareRoot.Newton.Search.Expansion
import TestPurelib.Integration.Algebraic.SquareFactor.OwnedCellObservation
import TestPurelib.Integration.Algebraic.SquareFactor.PreparationObservation
import TestPurelib.Integration.Algebraic.SquareFactor.ProgramObservation
import TestPurelib.Integration.Algebraic.SquareFactor.PathExpansion
import TestPurelib.Computation.Query.CheckedExpansion

/-! # Executed domain observer coverage regressions -/

/-- Run the actual root-checking and integrand callback boundaries. -/
public def main : IO Unit := do
  TestPurelib.RootIsolation.SquareRoot.Newton.Observation.run
  TestPurelib.Integration.Algebraic.SquareFactor.CoefficientObservation.run
  TestPurelib.RootIsolation.CCL.Persistent.Terminal.Observation.run
  TestPurelib.Integration.Replay.Expansion.run
  TestPurelib.RootIsolation.SquareRoot.Newton.Search.Expansion.run
  TestPurelib.Integration.Algebraic.SquareFactor.OwnedCellObservation.run
  TestPurelib.Integration.Algebraic.SquareFactor.PreparationObservation.run
  TestPurelib.Integration.Algebraic.SquareFactor.ProgramObservation.run
  TestPurelib.Integration.Algebraic.SquareFactor.PathExpansion.run
  TestPurelib.Computation.Query.CheckedExpansion.run
