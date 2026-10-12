module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Natural-powered finite Lp geometry

Natural powers of rational separations satisfy a uniform constructive
quasi-triangle estimate.  The factor `2 ^ exponent` is intentionally coarse:
it is obtained from a finite maximum comparison and works also at exponent
zero, without roots, real exponentiation, or convexity machinery.
-/

namespace Purelib.Measure
namespace Content

open Purelib
open Purelib.Data.Rat
/-- The powered magnitude integral of a sum is bounded by two to the exponent times the sum of the original powered
integrals. -/
theorem poweredLp_add_le_two_pow_mul {α : Type}
    (content : Measure.Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    content.poweredLp exponent (fun item => left item + right item) ≤
      (2 : Fraction.Rational) ^ exponent *
        (content.poweredLp exponent left +
          content.poweredLp exponent right) := by
  unfold poweredLp
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (left item + right item) 0 ^ exponent) ≤
      content.integral (fun item =>
        (2 : Fraction.Rational) ^ exponent *
          (Distance.rationalSeparation (left item) 0 ^ exponent +
            Distance.rationalSeparation (right item) 0 ^ exponent)) := by
      apply content.integral_mono
      intro atom member
      exact Distance.rationalSeparation_add_pow_le_two_pow_mul exponent
        (left atom.item) (right atom.item)
    _ = (2 : Fraction.Rational) ^ exponent *
        (content.integral (fun item =>
            Distance.rationalSeparation (left item) 0 ^ exponent) +
          content.integral (fun item =>
            Distance.rationalSeparation (right item) 0 ^ exponent)) := by
      rw [content.integral_scale, content.integral_add]

/-- Powered distance through a middle observable is bounded by two to the exponent times the sum of its two powered
distances. -/
theorem poweredLpDistance_le_two_pow_mul {α : Type}
    (content : Measure.Content α) (exponent : Nat)
    (left middle right : α → Fraction.Rational) :
    content.poweredLpDistance exponent left right ≤
      (2 : Fraction.Rational) ^ exponent *
        (content.poweredLpDistance exponent left middle +
          content.poweredLpDistance exponent middle right) := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ exponent) ≤
      content.integral (fun item =>
        (2 : Fraction.Rational) ^ exponent *
          (Distance.rationalSeparation (left item) (middle item) ^ exponent +
            Distance.rationalSeparation (middle item) (right item) ^ exponent)) := by
      apply content.integral_mono
      intro atom member
      exact Distance.rationalSeparation_pow_triangle_le_two_pow_mul exponent
        (left atom.item) (middle atom.item) (right atom.item)
    _ = (2 : Fraction.Rational) ^ exponent *
        (content.integral (fun item =>
            Distance.rationalSeparation (left item) (middle item) ^ exponent) +
          content.integral (fun item =>
            Distance.rationalSeparation (middle item) (right item) ^ exponent)) := by
      rw [content.integral_scale, content.integral_add]

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
