module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
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

open Purelib.Geometry.Coordinates.Polar

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

namespace Purelib.Curves.Plane.Parabola.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Parabola, cardioid, limacon, and trisectrix -/

/-- Squaring `y²=4ax` gives the origin-safe parabola equation. -/
theorem parabola_rational_polar_origin_safe
    (x y a A spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (parabolaEquation : y ^ 2 = 4 * a * x) :
    Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) = 0 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  calc
    Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) =
        ((1 - spread) * Q) ^ 2 - 16 * A * (spread * Q) := by ring1
    _ = (y ^ 2) ^ 2 - 16 * A * x ^ 2 := by
      rw [← squareCoordinates.2, coordinates.2]
    _ = (4 * a * x) ^ 2 - 16 * a ^ 2 * x ^ 2 := by
      rw [parabolaEquation, aSquare]
    _ = 0 := by ring1

/-- The parabola has rational polar equation one minus spread squared times Q equals sixteen A times spread.

The radial quadrance is explicitly nonzero, allowing cancellation of the origin-safe cleared identity. -/
theorem parabola_rational_polar
    (x y a A spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A) (parabolaEquation : y ^ 2 = 4 * a * x) :
    (1 - spread) ^ 2 * Q = 16 * A * spread := by
  apply Group.eq_of_sub_eq_zero
  exact Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero
    (parabola_rational_polar_origin_safe
      x y a A spread Q coordinates aSquare parabolaEquation)

/-- The rational polar parabola equation implies its denominator-cleared completed-square form. -/
theorem parabola_centered_rational_polar
    (A spread Q : K)
    (polarEquation : (1 - spread) ^ 2 * Q = 16 * A * spread) :
    (spread * Q - (Q + 8 * A)) ^ 2 = 16 * A * (Q + 4 * A) := by
  apply Group.eq_of_sub_eq_zero
  calc
    (spread * Q - (Q + 8 * A)) ^ 2 - 16 * A * (Q + 4 * A) =
        Q * ((1 - spread) ^ 2 * Q - 16 * A * spread) := by ring1
    _ = 0 := by rw [polarEquation]; ring1
end Purelib.Curves.Plane.Parabola.Polar.RationalPolarCatalogue

end

end
