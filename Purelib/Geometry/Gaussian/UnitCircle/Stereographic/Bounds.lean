module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Coordinates
public import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Strong coordinate bounds at the original stereographic quarter start

The real displacement has a fourth-power squared-norm bound, while the
imaginary displacement has a second-power squared-norm bound. Both inequalities
follow from the original cleared scalar readings and the explicit squared
denominator lower bound. They hold at every retained finite rational time.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The original stereographic scalar denominator's square is at least one. -/
private theorem scalar_square_lower (time : Fraction.Rational) : 1 ≤ (time ^ 2 + 1) ^ 2 := by
  have lower : (1 : Fraction.Rational) ≤ time ^ 2 + 1 := by
    have result := Arithmetic.add_le_add_direct
      (Arithmetic.sq_nonneg_direct time) (Fraction.Order.Basic.le_refl (1 : Fraction.Rational))
    rewrite [Fraction.Field.zero_add] at result
    exact result
  have result := Arithmetic.pow_le_pow_direct (by decide +kernel) lower 2
  rewrite [show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel] at result
  exact result

/-- The original real direction displacement satisfies its exact cleared scalar equation. -/
private theorem real_displacement_product (time : Fraction.Rational) :
    ((unitQuarterPoint time).re - 1) * (time ^ 2 + 1) = -2 * time ^ 2 := by
  calc
    _ = (unitQuarterPoint time).re * (time ^ 2 + 1) - (time ^ 2 + 1) := by ring1
    _ = (1 - time ^ 2) - (time ^ 2 + 1) :=
      congrArg (fun value => value - (time ^ 2 + 1)) (unitQuarterPoint_re_mul_scalar time)
    _ = _ := by ring1

/-- The original real projection departs from the quarter start with a fourth-power squared-norm bound. -/
public theorem real_displacement_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq (Components.Projection.realPart (unitQuarterPoint time) - 1) ≤ 4 * time ^ 4 := by
  have reading : Norm.Basic.normSq (Components.Projection.realPart (unitQuarterPoint time) - 1) =
      ((unitQuarterPoint time).re - 1) ^ 2 := by
    change ((unitQuarterPoint time).re - 1) ^ 2 + (0 - 0) ^ 2 = _
    ring1
  rewrite [reading]
  calc
    _ = ((unitQuarterPoint time).re - 1) ^ 2 * 1 := (Fraction.Field.mul_one_direct _).symm
    _ ≤ ((unitQuarterPoint time).re - 1) ^ 2 * (time ^ 2 + 1) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (scalar_square_lower time)
        (Arithmetic.sq_nonneg_direct _)
    _ = (((unitQuarterPoint time).re - 1) * (time ^ 2 + 1)) ^ 2 := by ring1
    _ = (-2 * time ^ 2) ^ 2 := congrArg (fun value => value ^ 2) (real_displacement_product time)
    _ = _ := by ring1

/-- The original imaginary projection has a second-power squared-norm bound at the quarter start. -/
public theorem imaginary_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq (Components.Projection.imaginaryPart (unitQuarterPoint time)) ≤ 4 * time ^ 2 := by
  have reading : Norm.Basic.normSq (Components.Projection.imaginaryPart (unitQuarterPoint time)) =
      (unitQuarterPoint time).im ^ 2 := by
    change (0 : Fraction.Rational) ^ 2 + (unitQuarterPoint time).im ^ 2 = _
    ring1
  rewrite [reading]
  calc
    _ = (unitQuarterPoint time).im ^ 2 * 1 := (Fraction.Field.mul_one_direct _).symm
    _ ≤ (unitQuarterPoint time).im ^ 2 * (time ^ 2 + 1) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (scalar_square_lower time)
        (Arithmetic.sq_nonneg_direct _)
    _ = ((unitQuarterPoint time).im * (time ^ 2 + 1)) ^ 2 := by ring1
    _ = (2 * time) ^ 2 := congrArg (fun value => value ^ 2) (unitQuarterPoint_im_mul_scalar time)
    _ = _ := by ring1

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic
