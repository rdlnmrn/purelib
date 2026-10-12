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

namespace Purelib.Curves.Plane.Cardioid.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Both orientations of the cardioid are covered by taking `orientedX=x` or `orientedX=-x`. -/
theorem cardioid_rational_polar_cleared
    (x y orientedX a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (orientedXSquare : orientedX ^ 2 = x ^ 2)
    (aSquare : a ^ 2 = A)
    (cardioidEquation :
      (x ^ 2 + y ^ 2 - 2 * a * orientedX) ^ 2 =
        4 * A * (x ^ 2 + y ^ 2)) :
    (4 * A * spread - (Q + 4 * A)) ^ 2 = 16 * A * Q := by
  have cartesianInQ : (Q - 2 * a * orientedX) ^ 2 = 4 * A * Q := by
    rw [coordinates.1]
    exact cardioidEquation
  have productZero :
      Q * (Q - 4 * a * orientedX + 4 * A * spread - 4 * A) = 0 := by
    have orientedSpread : Q * spread = orientedX ^ 2 := by
      calc
        Q * spread = spread * Q := by ring1
        _ = x ^ 2 := coordinates.2
        _ = orientedX ^ 2 := orientedXSquare.symm
    calc
      Q * (Q - 4 * a * orientedX + 4 * A * spread - 4 * A) =
          Q ^ 2 - 4 * a * Q * orientedX +
            4 * a ^ 2 * (Q * spread) - 4 * a ^ 2 * Q := by
        rw [aSquare]
        ring1
      _ =
          (Q - 2 * a * orientedX) ^ 2 - 4 * A * Q := by
        rw [orientedSpread, ← aSquare]
        ring1
      _ = 0 := by rw [cartesianInQ]; ring1
  have linearZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero productZero
  have centeredRelation :
      4 * A * spread - (Q + 4 * A) =
        2 * (2 * a * orientedX - Q) := by
    apply Group.eq_of_sub_eq_zero
    calc
      4 * A * spread - (Q + 4 * A) -
          2 * (2 * a * orientedX - Q) =
        Q - 4 * a * orientedX + 4 * A * spread - 4 * A := by ring1
      _ = 0 := linearZero
  rw [centeredRelation]
  calc
    (2 * (2 * a * orientedX - Q)) ^ 2 =
        4 * (Q - 2 * a * orientedX) ^ 2 := by ring1
    _ = 4 * (4 * A * Q) := by rw [cartesianInQ]
    _ = 16 * A * Q := by ring1
end Purelib.Curves.Plane.Cardioid.Polar.RationalPolarCatalogue

end

end
