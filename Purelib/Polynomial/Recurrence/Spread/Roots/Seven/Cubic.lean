module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Cubic

section

variable {K : Type*} [ExplicitField K]

/-! ## Problem 13: the seven-sided pagoda -/

/-- The nonzero factor in the seventh spread polynomial. -/
def seventhSpreadFactor (spread : K) : K :=
  7 - 56 * spread + 112 * spread ^ 2 - 64 * spread ^ 3

open Purelib.Polynomial in
/-- The degree-seven spread expression obtained by multiplying the coordinate by the square of its cubic factor. -/
def seventhSpreadValue (spread : K) : K :=
  spread * seventhSpreadFactor spread ^ 2

/-- Integer numerator of the cubic factor at the rational label `n/d`.
Multiplication by `d³` preserves its sign when `d>0`. -/
def seventhSpreadFactorNumerator (numerator denominator :
  Int) : Int :=
  7 * denominator ^ 3 - 56 * numerator * denominator ^ 2 +
    112 * numerator ^ 2 * denominator - 64 * numerator ^ 3
end
end Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Cubic

end
