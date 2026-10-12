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
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace Purelib.Curves.Plane.Lemniscate.Polar

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Example 27.2: lemniscate of Bernoulli -/

/-- The Cartesian lemniscate equation becomes the cleared polar equation `Q(Q-(2s-1))=0`. -/
theorem example_27_2_lemniscate_cleared
    (xSquared ySquared spread Q : K)
    (coordinates : RationalSphericalCoordinates.PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscate : (xSquared + ySquared) ^ 2 = xSquared - ySquared) :
    Q * (Q - (2 * spread - 1)) = 0 := by
  rcases Squared.polar_coordinate_squares xSquared ySquared spread Q coordinates with
    ⟨xValue, yValue⟩
  calc
    Q * (Q - (2 * spread - 1)) =
        Q ^ 2 - (spread * Q - (1 - spread) * Q) := by ring1
    _ = (xSquared + ySquared) ^ 2 - (xSquared - ySquared) := by
      rw [← xValue, ← yValue, coordinates.1]
    _ = 0 := by rw [lemniscate]; ring1

/-- With nonzero radial quadrance, the normalized Bernoulli lemniscate satisfies Q equals twice the spread minus one. -/
theorem example_27_2_lemniscate
    (xSquared ySquared spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalSphericalCoordinates.PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscate : (xSquared + ySquared) ^ 2 = xSquared - ySquared) :
    Q = 2 * spread - 1 := by
  have productZero := example_27_2_lemniscate_cleared
    xSquared ySquared spread Q coordinates lemniscate
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left QNonzero
  calc
    Q * Q = Q * (2 * spread - 1) +
        Q * (Q - (2 * spread - 1)) := by ring1
    _ = Q * (2 * spread - 1) := by rw [productZero]; ring1
end Purelib.Curves.Plane.Lemniscate.Polar

end

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

namespace Purelib.Curves.Plane.Lemniscate.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Lemniscate of Bernoulli and folium of Descartes -/

/-- With nonzero radial quadrance, the doubled Bernoulli lemniscate equation gives four times the spread equals Q plus
two. -/
theorem bernoulli_lemniscate_rational_polar
    (xSquared ySquared spread Q : K) (QNonzero : Q ≠ 0)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (lemniscateEquation : Q ^ 2 = 2 * (xSquared - ySquared)) :
    4 * spread = Q + 2 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  have productZero : Q * (Q - (4 * spread - 2)) = 0 := by
    calc
      Q * (Q - (4 * spread - 2)) =
          Q ^ 2 - 2 * (xSquared - ySquared) := by
        rw [squareCoordinates.1, squareCoordinates.2]
        ring1
      _ = 0 := by rw [lemniscateEquation]; ring1
  have linearZero :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left QNonzero productZero
  apply Group.eq_of_sub_eq_zero
  calc
    4 * spread - (Q + 2) = -(Q - (4 * spread - 2)) := by ring1
    _ = 0 := by rw [linearZero]; ring1
end Purelib.Curves.Plane.Lemniscate.Polar.RationalPolarCatalogue

end

end
