module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Lp.Geometry
import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

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
end Content

namespace Distribution

open Purelib.Data.Rat
/-- Bound the powered magnitude expectation of a sum by two to the exponent times the sum of the original powered
expectations. -/
theorem poweredLp_add_le_two_pow_mul {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    distribution.poweredLp exponent (fun item => left item + right item) ≤
      (2 : Fraction.Rational) ^ exponent *
        (distribution.poweredLp exponent left +
          distribution.poweredLp exponent right) :=
  distribution.toContent.poweredLp_add_le_two_pow_mul
    exponent left right

/-- Bound powered distance through an intermediate observable by two to the exponent times the two original powered
distances. -/
theorem poweredLpDistance_le_two_pow_mul {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left middle right : α → Fraction.Rational) :
    distribution.poweredLpDistance exponent left right ≤
      (2 : Fraction.Rational) ^ exponent *
        (distribution.poweredLpDistance exponent left middle +
          distribution.poweredLpDistance exponent middle right) :=
  distribution.toContent.poweredLpDistance_le_two_pow_mul
    exponent left middle right

end Distribution

end Purelib.Measure

end
