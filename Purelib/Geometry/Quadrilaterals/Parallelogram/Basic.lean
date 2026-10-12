module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

@[expose] public section

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

namespace Purelib.Geometry.Quadrilaterals.Parallelogram.Basic

variable {K : Type*} [ExplicitField K]

/-- The two coordinate determinant equations saying that opposite sides of `A₁A₂A₃A₄` are parallel. -/
def ParallelogramSideConditions
    (first second third fourth : Plane.Point K) : Prop :=
  (first.y - second.y) * (fourth.x - third.x) -
      (third.y - fourth.y) * (second.x - first.x) = 0 ∧
    (second.y - third.y) * (first.x - fourth.x) -
      (fourth.y - first.y) * (third.x - second.x) = 0

/-- Theorem 11 (Parallelogram center): the exact two parallel-side equations, together with the source's noncollinearity
determinant, force the two diagonal midpoints to coincide. -/
theorem parallelogram_center [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (_twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth)
      :
    Affine.midpoint first third = Affine.midpoint second fourth := by
  rcases parallelSides with ⟨firstParallel, secondParallel⟩
  let errorX := fourth.x - (first.x - second.x + third.x)
  let errorY := fourth.y - (first.y - second.y + third.y)
  have firstLinear :
      (first.y - second.y) * errorX +
        (second.x - first.x) * errorY = 0 := by
    unfold errorX errorY
    calc
      (first.y - second.y) *
            (fourth.x - (first.x - second.x + third.x)) +
          (second.x - first.x) *
            (fourth.y - (first.y - second.y + third.y)) =
        (first.y - second.y) * (fourth.x - third.x) -
          (third.y - fourth.y) * (second.x - first.x) := by ring1
      _ = 0 := firstParallel
  have secondLinear :
      (third.y - second.y) * errorX +
        (second.x - third.x) * errorY = 0 := by
    unfold errorX errorY
    calc
      (third.y - second.y) *
            (fourth.x - (first.x - second.x + third.x)) +
          (second.x - third.x) *
            (fourth.y - (first.y - second.y + third.y)) =
        (second.y - third.y) * (first.x - fourth.x) -
          (fourth.y - first.y) * (third.x - second.x) := by ring1
      _ = 0 := secondParallel
  have xProduct : errorX * Incidence.pointDeterminant first second third = 0 := by
    unfold Incidence.pointDeterminant
    calc
      errorX *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
        -((second.x - third.x) *
              ((first.y - second.y) * errorX +
                (second.x - first.x) * errorY) -
            (second.x - first.x) *
              ((third.y - second.y) * errorX +
                (second.x - third.x) * errorY)) := by ring1
      _ = 0 := by rw [firstLinear, secondLinear]; ring1
  have yProduct : errorY * Incidence.pointDeterminant first second third = 0 := by
    unfold Incidence.pointDeterminant
    calc
      errorY *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
        -((first.y - second.y) *
              ((third.y - second.y) * errorX +
                (second.x - third.x) * errorY) -
            (third.y - second.y) *
              ((first.y - second.y) * errorX +
                (second.x - first.x) * errorY)) := by ring1
      _ = 0 := by rw [firstLinear, secondLinear]; ring1
  have errorXZero : errorX = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_right determinantNonzero xProduct
  have errorYZero : errorY = 0 :=
    ExplicitField.eq_zero_of_mul_eq_zero_right determinantNonzero yProduct
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = errorX + (first.x - second.x + third.x) := by
        unfold errorX
        ring1
      _ = first.x - second.x + third.x := by rw [errorXZero]; ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = errorY + (first.y - second.y + third.y) := by
        unfold errorY
        ring1
      _ = first.y - second.y + third.y := by rw [errorYZero]; ring1
  apply Plane.Point.ext
  · change (first.x + third.x) / 2 = (second.x + fourth.x) / 2
    rw [fourthX]
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  · change (first.y + third.y) / 2 = (second.y + fourth.y) / 2
    rw [fourthY]
    simp only [ExplicitField.div_eq_mul_inv]
    ring1

/-- The coordinate-sum form of the Parallelogram center theorem. It is the finite equality used in the source's proof of
Theorem 21 and Exercises 5.4--5.6. -/
theorem parallelogram_coordinate_sums [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth)
      :
    first.x + third.x = second.x + fourth.x ∧
      first.y + third.y = second.y + fourth.y := by
  have centersEqual := parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  have centerX := congrArg Plane.Point.x centersEqual
  have centerY := congrArg Plane.Point.y centersEqual
  change (first.x + third.x) / 2 = (second.x + fourth.x) / 2 at centerX
  change (first.y + third.y) / 2 = (second.y + fourth.y) / 2 at centerY
  constructor
  · calc
      first.x + third.x = ((first.x + third.x) / 2) * 2 := by
        rw [ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.x + fourth.x) / 2) * 2 := by rw [centerX]
      _ = second.x + fourth.x :=
        ExplicitField.div_mul_cancel _ twoNonzero
  · calc
      first.y + third.y = ((first.y + third.y) / 2) * 2 := by
        rw [ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.y + fourth.y) / 2) * 2 := by rw [centerY]
      _ = second.y + fourth.y :=
        ExplicitField.div_mul_cancel _ twoNonzero
end Purelib.Geometry.Quadrilaterals.Parallelogram.Basic

end
