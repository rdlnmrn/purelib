module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Cleared coordinate readings of the original stereographic point

The original retained Gaussian point satisfies the displayed real and imaginary
scalar equations. Consumers can clear its positive scalar denominator without
unfolding the point construction or duplicating its coordinate calculation.
-/

public section

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- The original real reading satisfies its exact cleared stereographic equation. -/
theorem unitQuarterPoint_re_mul_scalar (time : Fraction.Rational) :
    (unitQuarterPoint time).re * (time ^ 2 + 1) = 1 - time ^ 2 := by
  have value := congrArg Basic.re (unitQuarterPoint_mul_denominator time)
  change (unitQuarterPoint time).re * (time ^ 2 + 1) -
    (unitQuarterPoint time).im * 0 = 1 - time ^ 2 at value
  rewrite [Fraction.Field.mul_zero_direct] at value
  calc
    _ = (unitQuarterPoint time).re * (time ^ 2 + 1) - 0 := by ring0
    _ = _ := value

/-- The original imaginary reading satisfies its exact cleared stereographic equation. -/
theorem unitQuarterPoint_im_mul_scalar (time : Fraction.Rational) :
    (unitQuarterPoint time).im * (time ^ 2 + 1) = 2 * time := by
  have value := congrArg Basic.im (unitQuarterPoint_mul_denominator time)
  change (unitQuarterPoint time).re * 0 +
    (unitQuarterPoint time).im * (time ^ 2 + 1) = 2 * time at value
  rewrite [Fraction.Field.mul_zero_direct, Fraction.Field.zero_add] at value
  exact value

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic
