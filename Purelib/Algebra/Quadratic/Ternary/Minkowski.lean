module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Algebra.Quadratic.Ternary.Basic

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

namespace Purelib.Algebra.Quadratic.Ternary.Basic

variable {K : Type*} [ExplicitField K]
namespace TernaryForm

/-- Construct the ternary quadratic form with diagonal coefficients one, one and negative one.

Nonzero one certifies the displayed symmetric matrix is invertible; determinant, adjugate and inverse caches retain
their exact matrix certificates. -/
def minkowski (oneNonzero : (1 : K) ≠ 0) : TernaryForm K :=
  TernaryForm.ofMatrix (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) (by
    ext <;> unfold Matrix3.transpose <;> ring1) (by
    intro determinantZero
    apply oneNonzero
    have negOneZero : (-1 : K) = 0 := by
      calc
        (-1 : K) = Matrix3.determinant
            (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) := by
          unfold Matrix3.determinant
          ring1
        _ = 0 := determinantZero
    calc
      (1 : K) = -(-1) := by ring1
      _ = -0 := by rw [negOneZero]
      _ = 0 := by ring1)

/-- The Minkowski form evaluates to the first two coordinate squares minus the third.

The form retains the supplied nonzero-unit certificate. -/
theorem quadrance_minkowski (oneNonzero : (1 : K) ≠ 0)
    (vector : Vector K) :
    (minkowski oneNonzero).quadrance vector =
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
  unfold TernaryForm.quadrance TernaryForm.bilinear minkowski TernaryForm.ofMatrix Matrix3.rowMul Vector.dot
  ring1

/-- The cached determinant of the Minkowski form is negative one. -/
theorem minkowski_determinant (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).determinant = -1 := by
  unfold minkowski TernaryForm.ofMatrix Matrix3.determinant
  ring1

/-- The cached Minkowski adjugate has diagonal negative one, negative one and one. -/
theorem minkowski_adjugate (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).adjugate =
      (⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩ : Matrix3 K) := by
  unfold minkowski TernaryForm.ofMatrix Matrix3.adjugate
  ext <;> ring1

/-- The cached Minkowski inverse equals its defining diagonal matrix.

The diagonal entries are one, one and negative one, whose displayed matrix squares to the identity. -/
theorem minkowski_inverse (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).inverse =
      (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) := by
  let form := minkowski oneNonzero
  let matrix : Matrix3 K := ⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩
  have matrixValue : form.matrix = matrix := rfl
  have selfInverse : Matrix3.mul matrix matrix = Matrix3.identity := by
    ext <;> unfold matrix Matrix3.mul Matrix3.identity <;> ring1
  calc
    form.inverse = Matrix3.mul form.inverse Matrix3.identity := by
      rw [Matrix3.mul_identity]
    _ = Matrix3.mul form.inverse (Matrix3.mul form.matrix form.matrix) := by
      rw [matrixValue, selfInverse]
    _ = Matrix3.mul
        (Matrix3.mul form.inverse form.matrix) form.matrix := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul Matrix3.identity form.matrix := by
      rw [form.inverse_mul_matrix]
    _ = form.matrix := by rw [Matrix3.identity_mul]
    _ = matrix := matrixValue

/-- The vector with coordinates one, zero and one is null for the Minkowski form.

The supplied nonzero-unit certificate makes the form nondegenerate. -/
theorem minkowski_null_direction (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).IsNull (⟨1, 0, 1⟩ : Vector K) := by
  unfold TernaryForm.IsNull
  rw [quadrance_minkowski]
  ring1
end TernaryForm

end Purelib.Algebra.Quadratic.Ternary.Basic

end
