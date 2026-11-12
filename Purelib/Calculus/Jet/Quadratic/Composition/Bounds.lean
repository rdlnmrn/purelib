module

public import Purelib.Calculus.Jet.Quadratic.Composition
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Fixed budgets for the original composition certificate

The original two certificates retain their slopes, remainders and movement
sensitivities. Fixed scalar upper bounds pay the actual composed slope and
factor without changing either original certificate or constructor.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Fixed slope and remainder budgets bound the retained certificate's original movement sensitivity. -/
theorem sensitivity_le {increment : Basic.Canonical} (certificate : Certificate increment)
    {slope factor : Fraction.Rational} (slopeBound : Norm.Basic.normSq certificate.slope ≤ slope)
    (factorBound : certificate.factor ≤ factor) : certificate.sensitivity ≤ 2 * (slope + factor) := by
  unfold sensitivity
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct slopeBound factorBound) (by decide +kernel)

/-- The original composed slope is bounded by the product of the two retained slope budgets. -/
theorem compose_slope_le {increment : Basic.Canonical} (inner : Certificate increment)
    (outer : Certificate (inner.output - inner.base)) (unit : Basic.Canonical.normSq increment ≤ 1)
    {innerSlope outerSlope : Fraction.Rational}
    (innerBound : Norm.Basic.normSq inner.slope ≤ innerSlope)
    (outerBound : Norm.Basic.normSq outer.slope ≤ outerSlope) :
    Norm.Basic.normSq (inner.compose outer unit).slope ≤ innerSlope * outerSlope := by
  change Norm.Basic.normSq (inner.slope * outer.slope) ≤ _
  rewrite [Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_direct innerBound outerBound (Norm.Basic.normSq_nonneg _)
    ((Norm.Basic.normSq_nonneg inner.slope).trans innerBound)

/-- Fixed input budgets bound the original composed quadratic factor without replacing either certificate.

The original slope and remainder-factor bounds also pay the inner movement
sensitivity. Both terms of the actual original composition are bounded by
these same finite budgets, independently of the displayed increment's size.
-/
theorem compose_factor_le {increment : Basic.Canonical} (inner : Certificate increment)
    (outer : Certificate (inner.output - inner.base)) (unit : Basic.Canonical.normSq increment ≤ 1)
    {innerSlope innerFactor outerSlope outerFactor : Fraction.Rational}
    (innerSlopeBound : Norm.Basic.normSq inner.slope ≤ innerSlope) (innerFactorBound : inner.factor ≤ innerFactor)
    (outerSlopeBound : Norm.Basic.normSq outer.slope ≤ outerSlope) (outerFactorBound : outer.factor ≤ outerFactor) :
    (inner.compose outer unit).factor ≤
      2 * (outerSlope * innerFactor + outerFactor * (2 * (innerSlope + innerFactor)) ^ 2) := by
  have outerSlopeNonnegative := (Norm.Basic.normSq_nonneg outer.slope).trans outerSlopeBound
  have outerFactorNonnegative := outer.factor_nonneg.trans outerFactorBound
  have first := Arithmetic.mul_le_mul_direct outerSlopeBound innerFactorBound
    inner.factor_nonneg outerSlopeNonnegative
  have sensitivity := inner.sensitivity_le innerSlopeBound innerFactorBound
  have second := Arithmetic.mul_le_mul_direct outerFactorBound
    (Arithmetic.pow_le_pow_direct inner.sensitivity_nonneg sensitivity 2)
    (Arithmetic.pow_nonneg_direct inner.sensitivity_nonneg 2) outerFactorNonnegative
  change 2 * (Basic.Canonical.normSq outer.slope * inner.factor + outer.factor * inner.sensitivity ^ 2) ≤ _
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct first second) (by decide +kernel)

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate

end
