module

import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Space.Cube.Boundary
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Space.Cube.Boundary

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

namespace Purelib.Geometry

namespace Surfaces.Ellipson.Boundary

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The six edges of the tetrahedron printed in Appendix B. -/
def OnTetrahedronEdge (x y z : K) : Prop :=
  (x = 0 ∧ y = z) ∨
    (x = 1 ∧ y + z = 1) ∨
    (y = 0 ∧ x = z) ∨
    (y = 1 ∧ x + z = 1) ∨
    (z = 0 ∧ x = y) ∨
    (z = 1 ∧ x + y = 1)

/-- The ellipson equation on the `x = 0` face is `(y - z)² = 0`. -/
theorem x_zero_face_square (y z : K) :
    Ellipson.Contains 0 y z ↔ (y - z) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (y - z) ^ 2 = -((0 + y + z) ^ 2 -
          2 * (0 ^ 2 + y ^ 2 + z ^ 2) - 4 * 0 * y * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (0 + y + z) ^ 2 - 2 * (0 ^ 2 + y ^ 2 + z ^ 2) -
          4 * 0 * y * z = -(y - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- The ellipson equation on the `x = 1` face is `(1 - y - z)² = 0`. -/
theorem x_one_face_square (y z : K) :
    Ellipson.Contains 1 y z ↔ (1 - y - z) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (1 - y - z) ^ 2 = -((1 + y + z) ^ 2 -
          2 * (1 ^ 2 + y ^ 2 + z ^ 2) - 4 * 1 * y * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (1 + y + z) ^ 2 - 2 * (1 ^ 2 + y ^ 2 + z ^ 2) -
          4 * 1 * y * z = -(1 - y - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- The ellipson equation on the `y = 0` face is `(x - z)² = 0`. -/
theorem y_zero_face_square (x z : K) :
    Ellipson.Contains x 0 z ↔ (x - z) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (x - z) ^ 2 = -((x + 0 + z) ^ 2 -
          2 * (x ^ 2 + 0 ^ 2 + z ^ 2) - 4 * x * 0 * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + 0 + z) ^ 2 - 2 * (x ^ 2 + 0 ^ 2 + z ^ 2) -
          4 * x * 0 * z = -(x - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- The ellipson equation on the `y = 1` face is `(1 - x - z)² = 0`. -/
theorem y_one_face_square (x z : K) :
    Ellipson.Contains x 1 z ↔ (1 - x - z) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (1 - x - z) ^ 2 = -((x + 1 + z) ^ 2 -
          2 * (x ^ 2 + 1 ^ 2 + z ^ 2) - 4 * x * 1 * z) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + 1 + z) ^ 2 - 2 * (x ^ 2 + 1 ^ 2 + z ^ 2) -
          4 * x * 1 * z = -(1 - x - z) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- The ellipson equation on the `z = 0` face is `(x - y)² = 0`. -/
theorem z_zero_face_square (x y : K) :
    Ellipson.Contains x y 0 ↔ (x - y) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (x - y) ^ 2 = -((x + y + 0) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + 0 ^ 2) - 4 * x * y * 0) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + y + 0) ^ 2 - 2 * (x ^ 2 + y ^ 2 + 0 ^ 2) -
          4 * x * y * 0 = -(x - y) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- The ellipson equation on the `z = 1` face is `(1 - x - y)² = 0`. -/
theorem z_one_face_square (x y : K) :
    Ellipson.Contains x y 1 ↔ (1 - x - y) ^ 2 = 0 := by
  unfold Ellipson.Contains Ellipson.polynomial
  constructor
  · intro equation
    calc
      (1 - x - y) ^ 2 = -((x + y + 1) ^ 2 -
          2 * (x ^ 2 + y ^ 2 + 1 ^ 2) - 4 * x * y * 1) := by ring1
      _ = 0 := by rw [equation]; ring1
  · intro squareZero
    calc
      (x + y + 1) ^ 2 - 2 * (x ^ 2 + y ^ 2 + 1 ^ 2) -
          4 * x * y * 1 = -(1 - x - y) ^ 2 := by ring1
      _ = 0 := by rw [squareZero]; ring1

/-- On fields with decidable equality, the ellipson meets the algebraic cube boundary at exactly the six edges of the
displayed tetrahedron. -/
theorem cube_boundary_intersection [DecidableEq K] (x y z :
  K) :
    Ellipson.Contains x y z ∧ Ellipson.OnCubeBoundary x y z ↔
      OnTetrahedronEdge x y z := by
  constructor
  · rintro ⟨onEllipson, boundary⟩
    rcases boundary with xZero | xOne | yZero | yOne | zZero | zOne
    · apply Or.inl
      refine ⟨xZero, ?_⟩
      apply Purelib.Algebra.Field.Squares.eq_of_sub_square_eq_zero y z
      exact (x_zero_face_square y z).mp (by simpa [xZero] using onEllipson)
    · apply Or.inr
      apply Or.inl
      refine ⟨xOne, ?_⟩
      apply Purelib.Algebra.Field.Squares.sum_eq_one_of_square_zero y z
      exact (x_one_face_square y z).mp (by simpa [xOne] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨yZero, ?_⟩
      apply Purelib.Algebra.Field.Squares.eq_of_sub_square_eq_zero x z
      exact (y_zero_face_square x z).mp (by simpa [yZero] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨yOne, ?_⟩
      apply Purelib.Algebra.Field.Squares.sum_eq_one_of_square_zero x z
      exact (y_one_face_square x z).mp (by simpa [yOne] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨zZero, ?_⟩
      apply Purelib.Algebra.Field.Squares.eq_of_sub_square_eq_zero x y
      exact (z_zero_face_square x y).mp (by simpa [zZero] using onEllipson)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      refine ⟨zOne, ?_⟩
      apply Purelib.Algebra.Field.Squares.sum_eq_one_of_square_zero x y
      exact (z_one_face_square x y).mp (by simpa [zOne] using onEllipson)
  · intro edge
    rcases edge with xEdge | xOpposite | yEdge | yOpposite | zEdge | zOpposite
    · rcases xEdge with ⟨xZero, yzEqual⟩
      constructor
      · rw [xZero]
        apply (x_zero_face_square y z).mpr
        rw [yzEqual]
        ring1
      · exact Or.inl xZero
    · rcases xOpposite with ⟨xOne, yzSum⟩
      constructor
      · rw [xOne]
        apply (x_one_face_square y z).mpr
        rw [← yzSum]
        ring1
      · exact Or.inr (Or.inl xOne)
    · rcases yEdge with ⟨yZero, xzEqual⟩
      constructor
      · rw [yZero]
        apply (y_zero_face_square x z).mpr
        rw [xzEqual]
        ring1
      · exact Or.inr (Or.inr (Or.inl yZero))
    · rcases yOpposite with ⟨yOne, xzSum⟩
      constructor
      · rw [yOne]
        apply (y_one_face_square x z).mpr
        rw [← xzSum]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inl yOne)))
    · rcases zEdge with ⟨zZero, xyEqual⟩
      constructor
      · rw [zZero]
        apply (z_zero_face_square x y).mpr
        rw [xyEqual]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl zZero))))
    · rcases zOpposite with ⟨zOne, xySum⟩
      constructor
      · rw [zOne]
        apply (z_one_face_square x y).mpr
        rw [← xySum]
        ring1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr zOne))))
end Surfaces.Ellipson.Boundary
end Purelib.Geometry

end
