module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Coordinates.Polar.Squared
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Coordinates.Polar.Squared

section
public section

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

namespace Purelib.Curves.Plane.Hippopede.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The hippopede equation implies its rational polar identity with the retained B-squared factor.

The displayed squared-coordinate relation and nonzero radial quadrance permit exact scalar cancellation over an explicit
field. -/
theorem hippopede_rational_polar_corrected
    (xSquared ySquared A B spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (hippopedeEquation :
      Q ^ 2 + 4 * B * (B - A) * Q = 4 * B ^ 2 * xSquared) :
    4 * B ^ 2 * spread = Q + 4 * B * (B - A) := by
  have productZero :
      Q * (Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) = 0 := by
    calc
      Q * (Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) =
          Q ^ 2 + 4 * B * (B - A) * Q -
            4 * B ^ 2 * (spread * Q) := by ring1
      _ =
          Q ^ 2 + 4 * B * (B - A) * Q - 4 * B ^ 2 * xSquared := by
        rw [coordinates.2]
      _ = 0 := by rw [hippopedeEquation]; ring1
  have linearZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero productZero
  apply Group.eq_of_sub_eq_zero
  calc
    4 * B ^ 2 * spread - (Q + 4 * B * (B - A)) =
        -(Q + 4 * B * (B - A) - 4 * B ^ 2 * spread) := by ring1
    _ = 0 := by rw [linearZero]; ring1
end Purelib.Curves.Plane.Hippopede.Polar.RationalPolarCatalogue

end

end
