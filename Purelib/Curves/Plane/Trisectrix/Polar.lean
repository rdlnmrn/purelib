module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Limacon.Polar
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib

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

namespace Purelib.Curves.Plane.Trisectrix.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

attribute [local instance 2000] Purelib.Data.Nat.successorNeZero in
/-- The corrected trisectrix specialization has a minus sign. -/
theorem trisectrix_rational_polar_cleared
    (radial cosine a A spread Q : K)
    (radialSquare : radial ^ 2 = Q) (cosineSquare : cosine ^ 2 = spread)
    (aSquare : a ^ 2 = A)
    (trisectrixEquation : radial = 2 * a * cosine + a) :
    (4 * A * spread - (Q + A)) ^ 2 = 4 * A * Q := by
  exact Curves.Plane.Limacon.Polar.RationalPolarCatalogue.limacon_rational_polar_cleared
    radial cosine a a A A spread Q
    radialSquare cosineSquare aSquare aSquare trisectrixEquation
end Purelib.Curves.Plane.Trisectrix.Polar.RationalPolarCatalogue

end
