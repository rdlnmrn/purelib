module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Plane.Medians
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, Theorem 116: the Euler line

The centroid is an explicit finite affine combination.  The key identity is
the source's relation `G = (2/3)C + (1/3)O`, proved first for the already
formalized affine circumcenter and orthocenter weights and then transferred to
the geometric center constructions.  No completed line or infinite locus is
introduced: collinearity is the finite three-point determinant relation.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Median.Affine

/-- Multiplying the centroid coordinates by three recovers the coordinate sums, with the nonzero characteristic-three
premise made explicit. -/
theorem centroidPoint_scaled_coordinates
    (first second third : Plane.Point K) (threeNonzero : (3 : K) ≠ 0) :
    (Geometry.centroidPoint first second third).x * 3 =
        first.x + second.x + third.x ∧
      (Geometry.centroidPoint first second third).y * 3 =
        first.y + second.y + third.y := by
  constructor
  · unfold Geometry.centroidPoint
    exact Algebra.Field.ExplicitField.div_mul_cancel _ threeNonzero
  · unfold Geometry.centroidPoint
    exact Algebra.Field.ExplicitField.div_mul_cancel _ threeNonzero

/-- Three times the centroid quadrance difference for the first two vertices equals the difference of their opposite
side quadrances.

The field has nonzero three, so the centroid's coordinate average cancels. -/
theorem centroid_quadrance_difference_first_second
    (first second third : Plane.Point K) (threeNonzero : (3 : K) ≠ 0) :
    3 * (Quadrance.quadrance (Geometry.centroidPoint first second third) first -
        Quadrance.quadrance (Geometry.centroidPoint first second third) second) =
      Quadrance.quadrance first third - Quadrance.quadrance second third := by
  have scaled := Geometry.Triangles.Median.Affine.centroidPoint_scaled_coordinates first second third
    threeNonzero
  calc
    3 * (Quadrance.quadrance (Geometry.centroidPoint first second third) first -
          Quadrance.quadrance (Geometry.centroidPoint first second third) second) =
      (first.x - second.x) *
          (3 * (first.x + second.x) -
            2 * ((Geometry.centroidPoint first second third).x * 3)) +
        (first.y - second.y) *
          (3 * (first.y + second.y) -
            2 * ((Geometry.centroidPoint first second third).y * 3)) := by
              unfold Quadrance.quadrance
              ring1
    _ = Quadrance.quadrance first third - Quadrance.quadrance second third := by
      rw [scaled.1, scaled.2]
      unfold Quadrance.quadrance
      ring1

/-- The cyclic centroid quadrance-difference identity for the second and third vertices.

The field has nonzero three, so the centroid's coordinate average cancels. -/
theorem centroid_quadrance_difference_second_third
    (first second third : Plane.Point K) (threeNonzero : (3 : K) ≠ 0) :
    3 * (Quadrance.quadrance (Geometry.centroidPoint first second third) second -
        Quadrance.quadrance (Geometry.centroidPoint first second third) third) =
      Quadrance.quadrance first second - Quadrance.quadrance first third := by
  have scaled := Geometry.Triangles.Median.Affine.centroidPoint_scaled_coordinates first second third
    threeNonzero
  calc
    3 * (Quadrance.quadrance (Geometry.centroidPoint first second third) second -
          Quadrance.quadrance (Geometry.centroidPoint first second third) third) =
      (second.x - third.x) *
          (3 * (second.x + third.x) -
            2 * ((Geometry.centroidPoint first second third).x * 3)) +
        (second.y - third.y) *
          (3 * (second.y + third.y) -
            2 * ((Geometry.centroidPoint first second third).y * 3)) := by
              unfold Quadrance.quadrance
              ring1
    _ = Quadrance.quadrance first second - Quadrance.quadrance first third := by
      rw [scaled.1, scaled.2]
      unfold Quadrance.quadrance
      ring1

end Purelib.Geometry.Triangles.Median.Affine

end

end

end
