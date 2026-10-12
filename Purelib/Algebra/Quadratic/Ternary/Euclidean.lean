module

public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector

/-!
# The displayed Euclidean ternary form

The identity Gram matrix connects ordinary vector dot products to the
form-indexed constructions without changing their vector or matrix owners.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- The Euclidean ternary form retains the identity Gram matrix and its inverse. -/
@[expose] def euclidean (oneNonzero : (1 : K) ≠ 0) : TernaryForm K :=
  ofMatrix Matrix3.identity Matrix3.transpose_identity
    (by rw [Matrix3.determinant_identity]; exact oneNonzero)

/-- The Euclidean form pairing is the original vector dot product. -/
theorem bilinear_euclidean (oneNonzero : (1 : K) ≠ 0) (left right : Vector3 K) :
    (euclidean oneNonzero).bilinear left right = Vector3.dot left right := by
  unfold bilinear euclidean ofMatrix
  rw [Matrix3.rowMul_identity]

/-- The Euclidean form quadrance is the original vector quadrance. -/
theorem quadrance_euclidean (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (euclidean oneNonzero).quadrance vector = Vector3.quadrance vector :=
  bilinear_euclidean oneNonzero vector vector

/-- The Euclidean form dual retains the original vector. -/
theorem dual_euclidean (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (euclidean oneNonzero).dual vector = vector := by
  unfold dual euclidean ofMatrix
  exact Matrix3.rowMul_identity vector

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
