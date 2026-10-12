module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace Purelib.Geometry.Triangles.Right.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Theorem 23 (Pythagoras): the quadrance relation is equivalent to perpendicularity at the third vertex. -/
theorem pythagoras_iff_perpendicular [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance second third + Quadrance.quadrance first third = Quadrance.quadrance first second ↔
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct) := by
  have identity :
      Quadrance.quadrance second third + Quadrance.quadrance first third - Quadrance.quadrance first second =
        2 * ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) := by
    unfold Quadrance.quadrance
    ring1
  constructor
  · intro pythagoras
    have productZero :
        (2 : K) * ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) = 0 := by
      calc
        (2 : K) * ((first.y - third.y) * (second.y - third.y) +
            (third.x - first.x) * (third.x - second.x)) =
          Quadrance.quadrance second third + Quadrance.quadrance first third -
            Quadrance.quadrance first second := identity.symm
        _ = 0 := by rw [pythagoras]; ring1
    have dotZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero productZero
    unfold Plane.Line.Perpendicular Incidence.lineThrough
    exact dotZero
  · intro perpendicular
    unfold Plane.Line.Perpendicular Incidence.lineThrough at perpendicular
    calc
      Quadrance.quadrance second third + Quadrance.quadrance first third =
          Quadrance.quadrance first second +
            2 * ((first.y - third.y) * (second.y - third.y) +
              (third.x - first.x) * (third.x - second.x)) := by
                calc
                  Quadrance.quadrance second third + Quadrance.quadrance first third =
                      (Quadrance.quadrance second third + Quadrance.quadrance first third -
                        Quadrance.quadrance first second) + Quadrance.quadrance first second := by ring1
                  _ = 2 * ((first.y - third.y) * (second.y - third.y) +
                        (third.x - first.x) * (third.x - second.x)) +
                      Quadrance.quadrance first second := by rw [identity]
                  _ = Quadrance.quadrance first second +
                      2 * ((first.y - third.y) * (second.y - third.y) +
                        (third.x - first.x) * (third.x - second.x)) := by ring1
      _ = Quadrance.quadrance first second := by rw [perpendicular]; ring1

end Purelib.Geometry.Triangles.Right.Quadrance

end

/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Right.Quadrance

variable {K : Type*} [ExplicitField K]

/-- The quadrea of a right triangle is four times the product of its two adjacent side quadrances.

The side lines at the right vertex have distinct endpoints, and two is nonzero. -/
theorem right_triangle_quadrea [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (perpendicular :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct)) :
    Quadrea.Basic.quadrea first second third =
      4 * Quadrance.quadrance second third * Quadrance.quadrance first third := by
  apply QuadTriple.Basic.right_quadrea
  exact (pythagoras_iff_perpendicular first second third
    firstThirdDistinct secondThirdDistinct twoNonzero).2 perpendicular
end Purelib.Geometry.Triangles.Right.Quadrance

end

/-!
# Divine Proportions, Chapter 5 quad-triple exercises

The exercises below are direct finite polynomial consequences of
Archimedes' function.  Exercise 5.11 exposes the same distinct-centre premise
missing from the source's earlier quadratic-compatibility claim; no root is
selected in the degenerate case.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Right.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Exercise 5.12: the two quadrances adjacent to the right vertex of a noncollinear triangle are necessarily nonzero.
-/
theorem exercise_5_12 [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct)) :
    Quadrance.quadrance second third ≠ 0 ∧ Quadrance.quadrance first third ≠ 0 := by
  have areaNonzero : Quadrea.Basic.quadrea first second third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have rightArea := right_triangle_quadrea first second third
    firstThirdDistinct secondThirdDistinct twoNonzero rightAtThird
  constructor
  · intro firstQuadranceZero
    apply areaNonzero
    rw [rightArea, firstQuadranceZero]
    ring1
  · intro secondQuadranceZero
    apply areaNonzero
    rw [rightArea, secondQuadranceZero]
    ring1

end Purelib.Geometry.Triangles.Right.Quadrance

end
