module
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Right

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Riemann.Integration

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic

/-- A uniform constructive preparation provider, with no per-word analytic requirements once it has been built from the
initial positive enclosure. -/
def Provider (tau :
  Coherent.CoherentNamed) : Type 1 :=
  (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix) → Right.RightInverse matrix →
    Prepared.DenominatorPreparation (LegendreModularMonodromy.fractionalDenominator matrix tau)
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic

end
