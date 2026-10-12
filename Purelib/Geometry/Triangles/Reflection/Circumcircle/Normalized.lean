module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Circles.Concyclic.Determinant
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Quadrilaterals.Basic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Triangles.Reflection.Circumcircle.Normalized

section ResectionApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The orthocenter of the normalized triangle with vertices `(u,v),(0,0),(d,0)`. -/
def normalizedOrthocenter (u v d : K) :
  Plane.Point K :=
  ⟨u, u * (d - u) / v⟩

/-- Reflection in the normalized side joining `(0,0)` and `(d,0)`. -/
def normalizedSideReflection (x y : K) :
  Plane.Point K := ⟨x, -y⟩

/-- The source's many-to-one observation, in a finite coordinate normal form: if `B` is on the reference circumcircle,
reflecting `B` in the horizontal side produces a point whose side-circle contains the orthocenter. Cyclic relabelling
gives the same statement for the other two sides. -/
theorem
  circumcircle_reflection_collapses_to_orthocenter_normalized
    (u v d x y : K) (vNonzero : v ≠ 0) (dNonzero : d ≠ 0)
    (baseCyclic :
      Quadrilateral.coordinateCircleDeterminant
        ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩ = 0) :
    Quadrilateral.coordinateCircleDeterminant
      ⟨0, 0⟩ ⟨d, 0⟩ (Geometry.Triangles.Reflection.Circumcircle.Normalized.normalizedSideReflection x y)
        (Geometry.Triangles.Reflection.Circumcircle.Normalized.normalizedOrthocenter u v d) = 0 := by
  let t := u * (d - u)
  let w := t / v
  let f := x ^ 2 + y ^ 2 - d * x
  let circleResidual := v * f + (t - v ^ 2) * y
  have expandedBase :
      Quadrilateral.coordinateCircleDeterminant
          ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩ =
        -d * circleResidual := by
    unfold Quadrilateral.coordinateCircleDeterminant
      Quadrilateral.circleRowNorm Quadrilateral.determinantThree
      circleResidual f t
    ring1
  have scaledResidualZero : d * circleResidual = 0 := by
    calc
      d * circleResidual =
          -(Quadrilateral.coordinateCircleDeterminant
            ⟨u, v⟩ ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, y⟩) := by
              rw [expandedBase]
              ring1
      _ = 0 := by rw [baseCyclic]; ring1
  have residualZero : circleResidual = 0 :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left dNonzero scaledResidualZero
  have heightCleared : w * v = t := by
    unfold w
    exact Algebra.Field.ExplicitField.div_mul_cancel t vNonzero
  let reflectedResidual :=
    f * w + y * (u ^ 2 + w ^ 2 - d * u)
  have residualIdentity :
      v ^ 2 * reflectedResidual = t * circleResidual := by
    calc
      v ^ 2 * reflectedResidual =
          f * (w * v) * v + y * (w * v) ^ 2 -
            y * t * v ^ 2 := by
              unfold reflectedResidual t
              ring1
      _ = f * t * v + y * t ^ 2 - y * t * v ^ 2 := by
            rw [heightCleared]
      _ = t * circleResidual := by
            unfold circleResidual
            ring1
  have vSquareNonzero : v ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero vNonzero vNonzero
  have reflectedResidualZero : reflectedResidual = 0 := by
    apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left vSquareNonzero
    calc
      v ^ 2 * reflectedResidual = t * circleResidual := residualIdentity
      _ = 0 := by rw [residualZero]; ring1
  change
    Quadrilateral.coordinateCircleDeterminant
      ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, -y⟩ ⟨u, u * (d - u) / v⟩ = 0
  have orthocenterY : u * (d - u) / v = w := by rfl
  rw [orthocenterY]
  calc
    Quadrilateral.coordinateCircleDeterminant
        ⟨0, 0⟩ ⟨d, 0⟩ ⟨x, -y⟩ ⟨u, w⟩ =
      d * reflectedResidual := by
        unfold Quadrilateral.coordinateCircleDeterminant
          Quadrilateral.circleRowNorm Quadrilateral.determinantThree
          reflectedResidual f
        ring1
    _ = 0 := by rw [reflectedResidualZero]; ring1
end ResectionApplications
end Purelib.Geometry.Triangles.Reflection.Circumcircle.Normalized

end
