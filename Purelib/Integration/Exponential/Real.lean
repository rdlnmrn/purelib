module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real
public import Purelib.Integration.Cell.Numerical.Continuous.Comparison
public import Purelib.Integration.Cell.Numerical.Continuous.Producer

/-!
# Finite integration of real-coordinate exponential observations

Each rational point request runs the original finite Gaussian exponential
process. The integration frontier retains those point states and their
coordinate intervals along with the computed variation and mesh budgets.
-/

public section

namespace Purelib.Integration.Exponential.Real

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Horner

/-- Build the actual finite exponential point observations and integral enclosure for a positive request. -/
@[expose] def integrate (request : AccuracyRequest) : NumericalFrontier.Continuous.Result Real.modulus :=
  NumericalFrontier.Continuous.build Real.modulus request

/-- Construct persistent integration bounds from the original finite exponential point processes. -/
@[expose] def boundProcess : BoundProcess :=
  (NumericalFrontier.Continuous.producer Real.modulus).boundProcess

/-- Construct the original cell-splitting integration process for the finite exponential point family. -/
@[expose] def integrationProcess : IntegrationProcess (NumericalPoint Real.source) :=
  (NumericalFrontier.Continuous.producer Real.modulus).integrationProcess

end Purelib.Integration.Exponential.Real

end
