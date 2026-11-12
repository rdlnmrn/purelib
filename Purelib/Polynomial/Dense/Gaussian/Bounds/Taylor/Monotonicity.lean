module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Monotonicity of the original three-component Taylor Horner fold

Increasing the retained squared radius and three nonnegative accumulator
bounds increases the original value, slope and remainder outputs. The finite
induction uses the same coefficient list and original step operation.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The original Taylor step preserves its three nonnegative accumulator bounds. -/
theorem step_nonnegative {radius : Fraction.Rational} (radiusNonnegative : 0 ≤ radius)
    (bounds : HornerTaylorNormBounds) (coefficient : Canonical)
    (valueNonnegative : 0 ≤ bounds.value) (slopeNonnegative : 0 ≤ bounds.slope)
    (remainderNonnegative : 0 ≤ bounds.remainder) :
    0 ≤ (step radius bounds coefficient).value ∧ 0 ≤ (step radius bounds coefficient).slope ∧
      0 ≤ (step radius bounds coefficient).remainder := by
  constructor
  · exact Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct valueNonnegative radiusNonnegative)
        (Norm.Basic.normSq_nonneg coefficient))
  · constructor
    · exact Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct slopeNonnegative radiusNonnegative) valueNonnegative)
    · exact Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
        (Arithmetic.add_le_add_direct slopeNonnegative
          (Arithmetic.mul_nonneg_direct radiusNonnegative remainderNonnegative))

/-- Increasing the original radius and accumulator bounds increases all three Taylor step outputs. -/
theorem step_le {smallRadius largeRadius : Fraction.Rational} (radiusNonnegative : 0 ≤ smallRadius)
    (radiusBound : smallRadius ≤ largeRadius) (small large : HornerTaylorNormBounds) (coefficient : Canonical)
    (valueNonnegative : 0 ≤ small.value) (slopeNonnegative : 0 ≤ small.slope)
    (remainderNonnegative : 0 ≤ small.remainder) (valueBound : small.value ≤ large.value)
    (slopeBound : small.slope ≤ large.slope) (remainderBound : small.remainder ≤ large.remainder) :
    (step smallRadius small coefficient).value ≤ (step largeRadius large coefficient).value ∧
      (step smallRadius small coefficient).slope ≤ (step largeRadius large coefficient).slope ∧
      (step smallRadius small coefficient).remainder ≤ (step largeRadius large coefficient).remainder := by
  constructor
  · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_direct valueBound radiusBound radiusNonnegative
          (valueNonnegative.trans valueBound)) (Fraction.Order.Basic.le_refl _))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  · constructor
    · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_le_mul_direct slopeBound radiusBound radiusNonnegative
            (slopeNonnegative.trans slopeBound)) valueBound) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct slopeBound
          (Arithmetic.mul_le_mul_direct radiusBound remainderBound remainderNonnegative
            (radiusNonnegative.trans radiusBound))) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)

/-- The finite original Taylor coefficient fold preserves componentwise bounds under a larger radius and initial jet. -/
theorem fold_le (coefficients : List Canonical) {smallRadius largeRadius : Fraction.Rational}
    (radiusNonnegative : 0 ≤ smallRadius) (radiusBound : smallRadius ≤ largeRadius)
    (small large : HornerTaylorNormBounds) (valueNonnegative : 0 ≤ small.value)
    (slopeNonnegative : 0 ≤ small.slope) (remainderNonnegative : 0 ≤ small.remainder)
    (valueBound : small.value ≤ large.value) (slopeBound : small.slope ≤ large.slope)
    (remainderBound : small.remainder ≤ large.remainder) :
    (coefficients.foldl (step smallRadius) small).value ≤ (coefficients.foldl (step largeRadius) large).value ∧
      (coefficients.foldl (step smallRadius) small).slope ≤ (coefficients.foldl (step largeRadius) large).slope ∧
      (coefficients.foldl (step smallRadius) small).remainder ≤
        (coefficients.foldl (step largeRadius) large).remainder := by
  induction coefficients generalizing small large with
  | nil => exact ⟨valueBound, slopeBound, remainderBound⟩
  | cons coefficient coefficients induction =>
      rewrite [List.foldl_cons, List.foldl_cons]
      have nonnegative := step_nonnegative radiusNonnegative small coefficient
        valueNonnegative slopeNonnegative remainderNonnegative
      have bounds := step_le radiusNonnegative radiusBound small large coefficient valueNonnegative slopeNonnegative
        remainderNonnegative valueBound slopeBound remainderBound
      exact induction (step smallRadius small coefficient) (step largeRadius large coefficient)
        nonnegative.1 nonnegative.2.1 nonnegative.2.2 bounds.1 bounds.2.1 bounds.2.2

end Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds
