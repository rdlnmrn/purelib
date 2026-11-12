module

import TestPurelib.Approximation.Gaussian.Translation.CursorArithmetic
import TestPurelib.Approximation.Gaussian.Logarithm.TransitionComparison
import TestPurelib.Integration.Exponential.Comparison
import TestPurelib.Geometry.Path.Gaussian.LiftedIncidence
import TestPurelib.Approximation.Gaussian.Geometric.Preparation
import TestPurelib.Approximation.Gaussian.Geometric.Enclosure
import TestPurelib.Approximation.Gaussian.Geometric.Enclosure.Inverse

open TestPurelib.Approximation.Gaussian TestPurelib.Integration TestPurelib.Geometry.Path.Gaussian

/-- Execute original translation, prepared-chart and integration schedules with their typed incidence diagnostics.

The geometric preparation case can also be selected independently. -/
public def main (args : List String) : IO Unit := do
  match args with
  | ["--geometric-preparation"] => Geometric.Preparation.check
  | _ => do
      Translation.CursorArithmetic.check
      Logarithm.TransitionComparison.check
      Logarithm.TransitionComparison.checkAnchors
      Exponential.Comparison.check
      LiftedIncidence.check
      Geometric.Preparation.check
      Geometric.Enclosure.check
      Geometric.Enclosure.Inverse.check
