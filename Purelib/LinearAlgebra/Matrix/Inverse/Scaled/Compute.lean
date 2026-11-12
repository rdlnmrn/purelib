module
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Schur
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute

universe u
variable {K : Type*} [CommRing K]

/-- Every finite square matrix has a canonically computed fraction-free
scaled inverse.  The construction makes no invertibility decision: its
displayed scalar may be zero.  A later use as an actual inverse must supply a
separate constructive nonzero witness for that one finite scalar. -/
def scaledInverse : {n : Nat} -> (matrix
  : SquareMatrix K n) -> Basic.ScaledInverse matrix
  | 0, matrix =>
      { scalar := 1
        inverse := .nil
        left_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row
        right_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row }
  | n + 1, matrix =>
      Block.extendScaledInverse matrix
        (Compute.scaledInverse (Schur.schur
        matrix))

/-- The recursively constructed inverse satisfies the left scaled identity. -/
theorem scaledInverse_left_identity {n :
  Nat} (matrix : SquareMatrix K n) :
    Multiplication.mul (scaledInverse matrix).inverse matrix =
      Multiplication.scaleIdentity (scaledInverse matrix).scalar :=
  (scaledInverse matrix).left_identity

/-- The recursively constructed inverse satisfies the right scaled identity. -/
theorem scaledInverse_right_identity {n :
  Nat} (matrix : SquareMatrix K n) :
    Multiplication.mul matrix (scaledInverse matrix).inverse =
      Multiplication.scaleIdentity (scaledInverse matrix).scalar :=
  (scaledInverse matrix).right_identity

end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute

end
