module

import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Geometry.Quadratic.Ternary.Isometry
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.LinearAlgebra.Coordinates3.Vector
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Constructive displayed ternary forms

This module begins the finite coordinate-algebra part of Problem 71.  A form
stores its displayed symmetric matrix together with cached determinant,
adjugate, and inverse data.  The certificates connect every cached value to
the canonical fixed-size matrix calculation, so downstream executable code
does not repeat those calculations or recover an inverse by choice.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

set_option genInjectivity false in
/-- A special orthogonal transformation of a displayed ternary form. -/
structure SpecialOrthogonal (form : Ternary.Basic.TernaryForm
  K) extends form.Isometry where
  /-- The forward matrix has determinant one. -/ determinantOne : Matrix3.determinant matrix = 1

constructive_injectivity SpecialOrthogonal

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

section

namespace Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal

/-- A displayed special-orthogonal transformation is determined by its forward matrix. -/
theorem eq_of_matrix_eq {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.SpecialOrthogonal)
    (matrixEq : left.matrix = right.matrix) : left = right := by
  have isometryEq := Isometry.eq_of_matrix_eq
    left.toIsometry right.toIsometry matrixEq
  cases left with
  | mk leftIsometry leftDeterminant =>
      cases right with
      | mk rightIsometry rightDeterminant =>
          cases isometryEq
          rfl

/-- The identity special orthogonal transformation. -/
def identity (form :
  Ternary.Basic.TernaryForm K) : form.SpecialOrthogonal where
  toIsometry := Isometry.identity form
  determinantOne := Matrix3.determinant_identity

/-- Product of special orthogonal transformations. -/
def mul {form : Ternary.Basic.TernaryForm
  K} (left right : form.SpecialOrthogonal) :
    form.SpecialOrthogonal where
  toIsometry := Isometry.mul left.toIsometry right.toIsometry
  determinantOne := by
    change Matrix3.determinant
      (Matrix3.mul left.matrix right.matrix) = 1
    rw [Matrix3.determinant_mul, left.determinantOne,
      right.determinantOne, one_mul]

/-- Inverse special orthogonal transformation. -/
def inverse {form :
  Ternary.Basic.TernaryForm K} (rotation : form.SpecialOrthogonal) :
    form.SpecialOrthogonal where
  toIsometry := Isometry.inverse rotation.toIsometry
  determinantOne := by
    have determinantProduct := congrArg Matrix3.determinant
      rotation.inverse_mul_matrix
    change Matrix3.determinant rotation.inverseMatrix = 1
    rw [Matrix3.determinant_mul, rotation.determinantOne,
      Matrix3.determinant_identity, mul_one] at determinantProduct
    exact determinantProduct

/-- The identity is a left unit for the product of special orthogonal transformations. -/
@[simp] theorem identity_mul {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul
      (identity form) rotation = rotation := by
  apply eq_of_matrix_eq
  exact Matrix3.identity_mul rotation.matrix

/-- The identity is a right unit for the product of special orthogonal transformations. -/
@[simp] theorem mul_identity {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul rotation
      (identity form) = rotation := by
  apply eq_of_matrix_eq
  exact Matrix3.mul_identity rotation.matrix

/-- Products of displayed special orthogonal transformations associate. -/
theorem mul_assoc {form :
  Ternary.Basic.TernaryForm K}
    (first second third : form.SpecialOrthogonal) :
    mul
      (mul first second) third =
      mul first
      (mul second third) := by
  apply eq_of_matrix_eq
  exact Matrix3.mul_assoc first.matrix second.matrix third.matrix

/-- A transformation times its retained inverse is the identity. -/
@[simp] theorem mul_inverse {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul rotation
      (inverse rotation) =
      identity form := by
  apply eq_of_matrix_eq
  exact rotation.matrix_mul_inverse

/-- The retained inverse times its transformation is the identity. -/
@[simp] theorem inverse_mul {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul
      (inverse rotation) rotation =
      identity form := by
  apply eq_of_matrix_eq
  exact rotation.inverse_mul_matrix

/-- Inverting twice recovers the original displayed transformation. -/
@[simp] theorem inverse_inverse {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    inverse
      (inverse rotation) = rotation := by
  apply eq_of_matrix_eq
  rfl

/-- The inverse of a product is the reversed product of retained inverses. -/
theorem inverse_mul_reverse {form :
  Ternary.Basic.TernaryForm K}
    (left right : form.SpecialOrthogonal) :
    inverse
      (mul left right) =
      mul
      (inverse right)
      (inverse left) := by
  apply eq_of_matrix_eq
  rfl

/-- A special orthogonal transformation preserves the displayed form's quadrance. -/
theorem quadrance_act {form :
  Ternary.Basic.TernaryForm K}
    (rotation : form.SpecialOrthogonal) (vector : Coordinates3.Vector K) :
    form.quadrance ((Isometry.act rotation.toIsometry) vector) =
        form.quadrance vector :=
  (Isometry.quadrance_act rotation.toIsometry) vector

end Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal

end
end

end

end
