module

public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

@[expose] public section

namespace Purelib.Geometry.Rotations.Basic

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A rotation is an executable matrix together with the two finite certificates defining membership in `SO(3)`. -/
structure Rotation (K : Type*) [Algebra.Field.ExplicitField K] where
  /-- The displayed three-dimensional row-action matrix. -/ matrix : Matrix3 K
  /-- Multiplication by the transpose gives the identity matrix. -/ orthogonal : matrix.IsOrthogonal
  /-- The displayed matrix has determinant one. -/ determinantOne : matrix.determinant = 1

constructive_injectivity Rotation

end Purelib.Geometry.Rotations.Basic

section
public section
namespace Purelib.Geometry.Rotations.Basic.Rotation

open Purelib.LinearAlgebra.Coordinates3 (Matrix3)

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Multiply two certified Euclidean rotations in row-action order.

The forward matrix is the original matrix product. Orthogonality and
determinant-one certificates are composed from the two supplied rotations.
-/
def mul (left right : Rotations.Basic.Rotation K) : Rotations.Basic.Rotation K where
  matrix := Matrix3.mul left.matrix right.matrix
  orthogonal := Matrix3.isOrthogonal_mul left.orthogonal right.orthogonal
  determinantOne := by rw [Matrix3.determinant_mul, left.determinantOne, right.determinantOne, one_mul]

/-- Two certified rotations with equal displayed matrices are equal. -/
public theorem eq_of_matrix_eq (left right : Rotations.Basic.Rotation K)
    (matrix_eq : left.matrix = right.matrix) : left = right := by
  cases left with
  | mk leftMatrix leftOrthogonal leftDeterminant =>
      cases right with
      | mk rightMatrix rightOrthogonal rightDeterminant =>
          cases matrix_eq
          rfl

end Purelib.Geometry.Rotations.Basic.Rotation
end

end
