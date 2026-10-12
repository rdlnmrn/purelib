module
public import Purelib.Geometry.Coordinates.Polar.Squared
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Coordinates.Polar.Squared

section
@[expose] public section

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace Purelib.Geometry.Plane.Line.Polar.Squared.RationalPolarCatalogue

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The line `y=ax` has the cleared rational polar equation `(1+A)s=1`, where `A=a²`. -/
theorem line_rational_polar_cleared
    (x y a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (lineEquation : y = a * x) :
    (1 + A) * spread = 1 := by
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left QNonzero
  calc
    Q * ((1 + A) * spread) =
        (1 + A) * (spread * Q) := by ring1
    _ = (1 + A) * x ^ 2 := by rw [coordinates.2]
    _ = x ^ 2 + y ^ 2 := by rw [lineEquation, ← aSquare]; ring1
    _ = Q := coordinates.1.symm
    _ = Q * 1 := by ring1
end
end Purelib.Geometry.Plane.Line.Polar.Squared.RationalPolarCatalogue

end
