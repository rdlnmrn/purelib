module

public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# The time-first Lorentz form

The displayed Gram matrix is `diag(1,-1,-1)`. Its determinant is one,
so its even Clifford norm has the same scalar-plus-quadrance convention
as the positive Euclidean form.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- The nondegenerate time-first form with quadrance `t²-r²-s²`.

The displayed Gram matrix, determinant, adjugate and inverse belong to the
original ternary-form owner; the nonzero-unit certificate proves invertibility.
-/
@[expose] def lorentz (oneNonzero : (1 : K) ≠ 0) : TernaryForm K :=
  ofMatrix (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 K)
    (by ext <;> unfold Matrix3.transpose <;> ring1)
    (by
      intro zeroDeterminant
      apply oneNonzero
      calc
        (1 : K) = Matrix3.determinant
            (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 K) := by
          unfold Matrix3.determinant
          ring1
        _ = 0 := zeroDeterminant)

/-- The Lorentz pairing subtracts the two spatial-coordinate products. -/
theorem bilinear_lorentz (oneNonzero : (1 : K) ≠ 0) (left right : Vector3 K) :
    (lorentz oneNonzero).bilinear left right =
      left.t * right.t - left.r * right.r - left.s * right.s := by
  unfold bilinear lorentz ofMatrix Matrix3.rowMul Vector3.dot
  ring1

/-- Lorentz quadrance is the time-coordinate square minus the spatial squares. -/
theorem quadrance_lorentz (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (lorentz oneNonzero).quadrance vector = vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2 := by
  unfold quadrance
  rw [bilinear_lorentz]
  ring1

/-- The Lorentz dual preserves time and negates the two spatial coordinates. -/
theorem dual_lorentz (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (lorentz oneNonzero).dual vector = ⟨vector.t, -vector.r, -vector.s⟩ := by
  ext <;> unfold dual lorentz ofMatrix Matrix3.rowMul <;> ring1

/-- Squaring the time-first Lorentz Gram matrix gives the identity. -/
theorem lorentz_matrix_square (oneNonzero : (1 : K) ≠ 0) :
    Matrix3.mul (lorentz oneNonzero).matrix (lorentz oneNonzero).matrix = Matrix3.identity := by
  ext <;> unfold lorentz ofMatrix Matrix3.mul Matrix3.identity <;> ring1

/-- The retained inverse of the time-first Lorentz form equals its original Gram matrix. -/
theorem lorentz_inverse (oneNonzero : (1 : K) ≠ 0) :
    (lorentz oneNonzero).inverse = (lorentz oneNonzero).matrix := by
  calc
    _ = Matrix3.mul (lorentz oneNonzero).inverse Matrix3.identity := (Matrix3.mul_identity _).symm
    _ = Matrix3.mul (lorentz oneNonzero).inverse
        (Matrix3.mul (lorentz oneNonzero).matrix (lorentz oneNonzero).matrix) := by rw [lorentz_matrix_square]
    _ = Matrix3.mul (Matrix3.mul (lorentz oneNonzero).inverse (lorentz oneNonzero).matrix)
        (lorentz oneNonzero).matrix := (Matrix3.mul_assoc _ _ _).symm
    _ = _ := by rw [(lorentz oneNonzero).inverse_mul_matrix, Matrix3.identity_mul]

/-- The retained Lorentz determinant is one. -/
theorem lorentz_determinant (oneNonzero : (1 : K) ≠ 0) :
    (lorentz oneNonzero).determinant = 1 := by
  unfold lorentz ofMatrix Matrix3.determinant
  ring1

/-- The retained Lorentz adjugate equals its Gram matrix. -/
theorem lorentz_adjugate (oneNonzero : (1 : K) ≠ 0) :
    (lorentz oneNonzero).adjugate = (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 K) := by
  unfold lorentz ofMatrix Matrix3.adjugate
  ext <;> ring1

/-- The vector `(1,1,0)` is Lorentz-null over every explicit field. -/
theorem lorentz_null_direction (oneNonzero : (1 : K) ≠ 0) :
    (lorentz oneNonzero).IsNull (⟨1, 1, 0⟩ : Vector3 K) := by
  unfold IsNull
  rw [quadrance_lorentz]
  ring1

/-- The displayed Lorentz-null direction is nonzero when the unit is nonzero. -/
theorem lorentz_null_direction_ne_zero (oneNonzero : (1 : K) ≠ 0) :
    (⟨1, 1, 0⟩ : Vector3 K) ≠ Vector3.zero := by
  intro equal
  exact oneNonzero (congrArg Vector3.t equal)

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
