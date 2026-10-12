module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Algebra.Group.Basic
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
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.PerpendicularBisector

/-- The displayed perpendicular bisector from Theorem 12. -/
@[expose] def perpendicularBisector [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) : Line K where
  a := first.x - second.x
  b := first.y - second.y
  c := (second.x ^ 2 - first.x ^ 2 + second.y ^ 2 - first.y ^ 2) / 2
  direction_nonzero := by
    by_cases sameX : first.x = second.x
    · right
      apply sub_ne_zero_of_ne
      intro sameY
      exact distinct (Point.ext sameX sameY)
    · exact Or.inl (sub_ne_zero_of_ne sameX)

/-- Theorem 12: the displayed bisector passes through the midpoint. -/
theorem perpendicularBisector_contains_midpoint [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (PerpendicularBisector.perpendicularBisector first second distinct).Contains (Affine.midpoint first second) := by
  unfold PerpendicularBisector.perpendicularBisector Affine.midpoint Contains
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 12: the displayed bisector is perpendicular to the side line. -/
theorem perpendicularBisector_perpendicular [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (PerpendicularBisector.perpendicularBisector first second distinct).Perpendicular
      (Incidence.lineThrough first second distinct) := by
  unfold PerpendicularBisector.perpendicularBisector Incidence.lineThrough Perpendicular
  ring1

end Purelib.Geometry.Plane.Line.PerpendicularBisector

end

end

public section

/-!
# Divine Proportions, §5.4: quadrance to a line

Both results are proved directly from the finite coordinate formulas.  They
therefore apply unchanged to finite fields, subject only to the displayed
nonzero denominators.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.PerpendicularBisector

/-- Theorem 24 (Equal quadrance to two points): the perpendicular bisector is exactly the equal-quadrance locus. -/
theorem equal_quadrance_iff_perpendicularBisector_contains [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance point first = Quadrance.quadrance point second ↔
      (Geometry.Plane.Line.PerpendicularBisector.perpendicularBisector first second distinct).Contains point := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  let linearValue :=
    (first.x - second.x) * point.x +
      (first.y - second.y) * point.y +
      (second.x ^ 2 - first.x ^ 2 +
        second.y ^ 2 - first.y ^ 2) / 2
  have identity : Quadrance.quadrance point first - Quadrance.quadrance point second =
      -(2 * linearValue) := by
    unfold Quadrance.quadrance linearValue
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      ((first.x - point.x) ^ 2 + (first.y - point.y) ^ 2) -
          ((second.x - point.x) ^ 2 + (second.y - point.y) ^ 2) =
        -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y)) -
          (second.x ^ 2 - first.x ^ 2 +
            second.y ^ 2 - first.y ^ 2) := by ring1
      _ = -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y)) -
          (2 * (2 : K)⁻¹) *
            (second.x ^ 2 - first.x ^ 2 +
              second.y ^ 2 - first.y ^ 2) := by rw [twoInverse]; ring1
      _ = -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y +
          (second.x ^ 2 - first.x ^ 2 +
            second.y ^ 2 - first.y ^ 2) * (2 : K)⁻¹)) := by ring1
  change Quadrance.quadrance point first = Quadrance.quadrance point second ↔ linearValue = 0
  constructor
  · intro equalQuadrances
    have productZero : (2 : K) * linearValue = 0 := by
      have differenceZero : Quadrance.quadrance point first - Quadrance.quadrance point second = 0 := by
        rw [equalQuadrances]
        ring1
      rw [identity] at differenceZero
      calc
        (2 : K) * linearValue = -(-(2 * linearValue)) := by ring1
        _ = 0 := by rw [differenceZero]; exact neg_zero
    exact Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero productZero
  · intro linearZero
    have differenceZero : Quadrance.quadrance point first - Quadrance.quadrance point second = 0 := by
      rw [identity, linearZero]
      ring1
    calc
      Quadrance.quadrance point first =
          (Quadrance.quadrance point first - Quadrance.quadrance point second) +
            Quadrance.quadrance point second := by ring1
      _ = Quadrance.quadrance point second := by rw [differenceZero]; ring1

end Purelib.Geometry.Plane.Line.PerpendicularBisector

end

end

end
