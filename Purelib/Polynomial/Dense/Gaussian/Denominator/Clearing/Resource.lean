module
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Divisibility
public import Purelib.Data.Gaussian.Resource
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator
import Purelib.Data.Gaussian.Resource.List
import Purelib.Data.Nat.LCM
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.ScaledNumerator
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

open Purelib.Data.Gaussian.Fraction.NaturalDenominator

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Resource

open Purelib.Data
open Purelib.Polynomial.Dense.Gaussian.Denominator

/-- Multiply the reduced real and imaginary denominators of the finite coefficient list.

The empty list contributes one, so the result bounds the least common denominator without requiring a nonempty input. -/
def coefficientDenominatorProduct : List
  Gaussian.Basic.Canonical → Nat
  | [] => 1
  | coefficient :: remaining =>
      let realDen :=
        (Fraction.Basic.representative coefficient.re).den
      let imaginaryDen :=
        (Fraction.Basic.representative coefficient.im).den
      realDen * imaginaryDen *
        Resource.coefficientDenominatorProduct remaining

/-- A coefficient's least natural denominator is bounded by its coordinate product.

Both coordinate denominators are positive, and their least common multiple
divides the retained product. -/
theorem coefficientDenominator_le_product
  (coefficient : Gaussian.Basic.Canonical) :
    LeastDenominator.coefficientDenominator coefficient ≤
      (Fraction.Basic.representative coefficient.re).den *
        (Fraction.Basic.representative coefficient.im).den := by
  apply Nat.Divisibility.le_of_dvd
  · exact Nat.mul_pos
      (Fraction.Basic.representative coefficient.re).den_pos
      (Fraction.Basic.representative coefficient.im).den_pos
  · exact Nat.LCM.lcm_dvd_mul _ _

/-- The coefficient LCM scale is bounded by the coordinate-denominator product.

Structural recursion retains each original coordinate denominator and bounds
the least common multiple at each actual list entry. -/
theorem lcmScale_le_denominatorProduct : ∀
  coefficients : List Gaussian.Basic.Canonical,
    LCM.lcmScale coefficients ≤
      coefficientDenominatorProduct coefficients
  | [] => le_refl 1
  | coefficient :: remaining => by
      unfold LCM.lcmScale coefficientDenominatorProduct
      have lcmBound : Nat.LCM.lcm
          (LeastDenominator.coefficientDenominator coefficient)
          (LCM.lcmScale remaining) ≤
          LeastDenominator.coefficientDenominator coefficient *
            LCM.lcmScale remaining := by
        apply Nat.Divisibility.le_of_dvd
        · exact Nat.mul_pos
            (LeastDenominator.coefficientDenominator_pos coefficient)
            (LCM.lcmScale_pos remaining)
        · exact Nat.LCM.lcm_dvd_mul _ _
      exact lcmBound.trans (Nat.mul_le_mul
        (coefficientDenominator_le_product coefficient)
        (Resource.lcmScale_le_denominatorProduct remaining))

/-- Bound every cleared integer component by the displayed denominator product.

The finite fold takes the maximum source magnitude multiplied by the common
product of all original coordinate denominators. -/
def clearedCoefficientMagnitudeEnvelope
    (coefficients : List Gaussian.Basic.Canonical) : Nat :=
  coefficients.foldl (fun bound coefficient =>
    max bound (Gaussian.Resource.ClearingCalculationSize.coefficientComponentMagnitude coefficient *
      coefficientDenominatorProduct coefficients)) 0

section
/-- Each displayed coefficient contribution lies within the clearing magnitude envelope. -/
private theorem
  member_le_clearedEnvelope
    (coefficients : List Gaussian.Basic.Canonical) (candidate : Gaussian.Basic.Canonical)
    (member : candidate ∈ coefficients) :
    Gaussian.Resource.ClearingCalculationSize.coefficientComponentMagnitude candidate *
        coefficientDenominatorProduct coefficients ≤
      clearedCoefficientMagnitudeEnvelope coefficients := by
  exact Gaussian.Resource.List.member_le_foldl_max
    (fun value => Gaussian.Resource.ClearingCalculationSize.coefficientComponentMagnitude value *
      coefficientDenominatorProduct coefficients)
    coefficients 0 candidate member
end

/-- Every integral component in a cleared coefficient fits the product-scale envelope.

The retained membership witness identifies the actual source coefficient.
Its component magnitudes and the original product of coordinate denominators
bound the corresponding scaled integer components. -/
theorem scaledGaussianCoefficient_component_le
    (coefficients : List Gaussian.Basic.Canonical) (coefficient : Gaussian.Basic.Canonical)
    (member : coefficient ∈ coefficients) :
    max
        (ScaledNumerator.scaledGaussianCoefficient
          (LCM.lcmScale coefficients) coefficient).re.natAbs
        (ScaledNumerator.scaledGaussianCoefficient
          (LCM.lcmScale coefficients) coefficient).im.natAbs ≤
      clearedCoefficientMagnitudeEnvelope coefficients := by
  apply Nat.Order.max_le
  · exact (Fraction.ScaledNumerator.scaledCoordinateNumerator_le
      (LCM.lcmScale coefficients) coefficient.re).trans
      ((Nat.mul_le_mul
        (Nat.Order.le_max_left _ _)
        (lcmScale_le_denominatorProduct coefficients)).trans
        (member_le_clearedEnvelope coefficients
          coefficient member))
  · exact (Fraction.ScaledNumerator.scaledCoordinateNumerator_le
      (LCM.lcmScale coefficients) coefficient.im).trans
      ((Nat.mul_le_mul
        (Nat.Order.le_max_right _ _)
        (lcmScale_le_denominatorProduct coefficients)).trans
        (member_le_clearedEnvelope coefficients
          coefficient member))

/-- The declared coefficient-clearing operation budget is six times the coefficient count. -/
def coefficientClearingOperationBudget
  (coefficients : List Gaussian.Basic.Canonical) : Nat :=
  6 * coefficients.length
end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Resource

end
