module

import Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Geometry.Rational.Box.Resource
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Resource
import Purelib.Polynomial.Dense.Resource
import Purelib.Polynomial.Elimination.Separated.Bezout
import Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation
import Purelib.Polynomial.Winding.Box.Resource
public import Purelib.RootIsolation.Resource.Budget
import Purelib.RootIsolation.Resource.Input
import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.RootIsolation.Subdivision.Raw.Resource
import Purelib.RootIsolation.Subdivision.Raw.Resource.Winding
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.LinearAlgebra

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Basic

/-- Checked operation and magnitude bounds for the original finite raw-isolation calculation.

The certificate covers retained elimination and Bézout data, coefficient clearing, safe evaluation, refined coordinates
and every inspected winding box, with the exact resulting bit width. -/
structure StageThreeResourcesWithin (input : Resource.Input.StageThreeInput)
    (steps bits : Nat) : Prop where
  /-- The original coefficient-clearing operation count fits the supplied step bound. -/ coefficientClearingSteps :
    Dense.Gaussian.Denominator.Clearing.Resource.coefficientClearingOperationBudget
      input.polynomial.normalize.coeffs ≤ steps
  /-- The original vertical eliminant operation count fits the step bound. -/ verticalEliminantSteps :
    Elimination.Separated.Normalized.Resource.Operation.eliminantOperationBudget input.polynomial ≤ steps
  /-- The original quarter-turn eliminant operation count fits the step bound. -/ horizontalEliminantSteps :
    Elimination.Separated.Normalized.Resource.Operation.eliminantOperationBudget input.horizontalPolynomial ≤ steps
  /-- The original fixed-depth subdivision search count fits the step bound. -/ searchCalls :
    Subdivision.Raw.Resource.subdivisionSearchBudget
      input.degreeBound input.depth ≤ steps
  /-- The original safe-cut field operations fit the step bound. -/ safeCutSteps :
    Resource.Budget.safeCutFieldOperationBudget input ≤ steps
  /-- The original finite winding calculations fit the step bound. -/ windingSteps :
    Subdivision.Raw.Resource.Winding.refinementWindingStepBudget input.elimination input.state
      input.depth ≤ steps
  /-- The retained vertical eliminant coefficients fit the combined magnitude budget. -/ verticalElimination :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
    (id input.elimination.vertical)
    (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- The retained horizontal eliminant coefficients fit the combined magnitude budget. -/ horizontalElimination :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
    (id input.elimination.horizontal)
    (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- The original safe-evaluation envelope fits the combined magnitude budget. -/ safeEvaluationEnvelope :
    Resource.Budget.safeEvaluationMagnitudeBudget input ≤
    Resource.Budget.stageThreeMagnitudeBudget input
  /-- The original vertical separated Bézout data fit the combined magnitude budget. -/ verticalBezout :
    PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin
    (Elimination.Separated.Bezout.separatedData
      (id input.polynomial))
    (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- The original quarter-turn separated Bézout data fit the combined magnitude budget. -/ horizontalBezout :
    PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin
    (Elimination.Separated.Bezout.separatedData
      (id input.horizontalPolynomial))
    (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- The original coefficient denominator-clearing scale fits the combined magnitude budget. -/ coefficientScale :
    Dense.Gaussian.Denominator.Clearing.LCM.lcmScale
      input.polynomial.normalize.coeffs ≤ Resource.Budget.stageThreeMagnitudeBudget input
  /-- Every original cleared Gaussian coefficient has real and imaginary magnitudes within the budget. -/
    clearedCoefficients : ∀ coefficient ∈ input.polynomial.normalize.coeffs,
    max
        (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
          (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale input.polynomial.normalize.coeffs)
          coefficient).re.natAbs
        (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
          (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale input.polynomial.normalize.coeffs)
          coefficient).im.natAbs ≤ Resource.Budget.stageThreeMagnitudeBudget input
  /-- The requested original refined box coordinates fit the combined magnitude budget. -/ refinedBox :
    Box.Resource.BoxWithin
    (Subdivision.Raw.Request.refineTo input.elimination input.state input.threshold).box
    (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- Every original inspected winding box has its retained arithmetic resource certificate. -/ windingBoxes : ∀ box ∈
      Subdivision.Raw.Resource.Winding.refinementWindingBoxes input.elimination input.state input.depth,
    Winding.Box.Resource.BoxWindingResourcesWithin input.polynomial box
      (Resource.Budget.stageThreeMagnitudeBudget input)
  /-- The supplied bit count is exactly the width of the combined original magnitude budget. -/ bitBudget :
    Data.Nat.BitWidth.natWidth (Resource.Budget.stageThreeMagnitudeBudget input) = bits
end Purelib.RootIsolation.Resource.Basic

end
