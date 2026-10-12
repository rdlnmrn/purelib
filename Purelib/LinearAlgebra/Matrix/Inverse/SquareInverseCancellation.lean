module
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse
import Purelib.LinearAlgebra.Matrix.Blocks

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

@[expose] public section

/-! A displayed one-sided inverse of a finite Gaussian square matrix is two-sided. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.SquareInverseCancellation

open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse (LeftKernelTrivial)
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian :=
  Data.Gaussian.Basic.Canonical

/-- An explicit right inverse forces the original square matrix to have trivial left kernel. -/
theorem
  leftKernelTrivial_of_rightInverse
  {size : Nat} (first last : SquareMatrix SquareMatrix.Inverse.SquareInverseCancellation.Gaussian size)
    (inverse : SquareMatrix.Multiplication.mul first last = SquareMatrix.Multiplication.scaleIdentity 1) :
      LeftKernelTrivial first := open Purelib.Algebra in by
  intro vector kernel column
  have composed := Data.Vector.Basic.vector_eq_at (SquareMatrix.Multiplication.vectorMatrix_mul vector first last)
    column
  rw [inverse] at composed
  have unit := Data.Vector.Basic.vector_eq_at (SquareMatrix.Multiplication.vectorMatrix_scaleIdentity vector (1 :
    SquareMatrix.Inverse.SquareInverseCancellation.Gaussian)) column
  rw [Data.Vector.Basic.vectorOfFn_apply, mul_one] at unit
  have zero : SquareMatrix.Multiplication.vectorMatrix (SquareMatrix.Multiplication.vectorMatrix vector first) last
    column = 0 := by
    rw [SquareMatrix.Multiplication.vectorMatrix_apply]
    exact (FiniteSum.Fin.sumFin_congr (fun index => by rw [kernel index, zero_mul])).trans FiniteSum.Fin.sumFin_zero
  exact unit.symm.trans (composed.trans zero)

/-- A right inverse of a finite square Gaussian matrix is also a left inverse.

The proof constructs a certified nonzero scaled inverse and cancels its retained scalar. -/
theorem reverse_inverse {size
  : Nat} (first last : SquareMatrix SquareMatrix.Inverse.SquareInverseCancellation.Gaussian size)
    (inverse : SquareMatrix.Multiplication.mul first last = SquareMatrix.Multiplication.scaleIdentity 1) :
      SquareMatrix.Multiplication.mul last first = SquareMatrix.Multiplication.scaleIdentity 1 := by
  let certified := SquareMatrix.Inverse.ExactPivotInverse.invert first
    (SquareMatrix.Inverse.SquareInverseCancellation.leftKernelTrivial_of_rightInverse first last inverse)
  have scaled : SquareMatrix.Multiplication.mul (SquareMatrix.Multiplication.scaleIdentity certified.inverse.scalar)
    last = certified.inverse.inverse := by
    calc
      _ = SquareMatrix.Multiplication.mul (SquareMatrix.Multiplication.mul certified.inverse.inverse first) last :=
        congrArg (fun matrix => SquareMatrix.Multiplication.mul matrix last) certified.inverse.left_identity.symm
      _ = SquareMatrix.Multiplication.mul certified.inverse.inverse (SquareMatrix.Multiplication.mul first last) :=
        SquareMatrix.Multiplication.mul_assoc _ _ _
      _ = certified.inverse.inverse := by rw [inverse, SquareMatrix.Multiplication.mul_unit]
  have product : SquareMatrix.Multiplication.mul (SquareMatrix.Multiplication.scaleIdentity certified.inverse.scalar)
    (SquareMatrix.Multiplication.mul last first) =
      SquareMatrix.Multiplication.scaleIdentity certified.inverse.scalar := by
    rw [← SquareMatrix.Multiplication.mul_assoc, scaled]
    exact certified.inverse.left_identity
  apply SquareMatrix.matrix_ext
  intro row column
  have equal := SquareMatrix.matrix_eq_at product row column
  rw [SquareMatrix.Multiplication.scaleIdentity_mul, SquareMatrix.matrixOfFn_apply,
    SquareMatrix.Multiplication.scaleIdentity_apply] at equal
  apply Data.Gaussian.Field.mul_right_cancel_of_ne certified.scalar_nonzero
  rw [SquareMatrix.Multiplication.scaleIdentity_apply, _root_.mul_comm (SquareMatrix.Multiplication.mul last first row
    column)]
  apply equal.trans
  by_cases same : row = column
  · simp only [if_pos same, one_mul, -eq_self, -iff_self]
    rfl
  · simp only [if_neg same, zero_mul, -eq_self, -iff_self]
    rfl

end Purelib.LinearAlgebra.Matrix.Inverse.SquareInverseCancellation
