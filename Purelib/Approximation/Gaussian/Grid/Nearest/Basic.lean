module
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Rounding.Floor
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

/-!
# Rounded, checked finite square-root proposals

Round each speculative Newton point to a dyadic grid before checking it and
before computing the next point.  This avoids carrying the exact Newton
orbit's rapidly growing denominators into an accepted root sample.

The predicate, not Newton convergence or a rounding estimate, certifies the
returned point.  A finite unsuccessful search returns `none`; callers retain
their independently proved total fallback.  No floating-point arithmetic or
external certificate producer is involved.
-/

@[expose] public section

namespace Purelib.Approximation.Gaussian.Grid.Nearest.Basic

/-- Round to the nearest grid point (ties upward), only as proposal generation. Unlike downward rounding, this can
remove a tiny imaginary component near a real root. Explicit integer conversion avoids expanding the rounded numerator
as a unary natural-number cast. -/
def rounded (grid : Fraction.Rational) (point :
  Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  let coordinate := fun value : Fraction.Rational =>
    Fraction.Cast.fromInt
      (Floor.floor (value / grid + 1 / 2)) * grid
  ⟨coordinate point.re, coordinate point.im⟩
end Purelib.Approximation.Gaussian.Grid.Nearest.Basic

end
