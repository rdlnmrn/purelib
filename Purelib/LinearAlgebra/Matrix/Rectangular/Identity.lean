module

public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Fin

/-!
# Original square identities acting on rectangular matrices

The same square scalar identity acts on either original dimension of a
rectangle. These laws retain the shared rectangular multiplication kernel.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Rectangular

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] {rows columns : Nat}

/-- Multiplication by the original left scalar identity scales each retained entry. -/
theorem scaleIdentity_mul (coefficient : K) (matrix : Rectangular K rows columns) :
    mul (Multiplication.scaleIdentity coefficient) matrix =
      ofFn (fun row column => coefficient * matrix row column) := by
  apply ext
  intro row column
  rw [mul_at, ofFn_apply]
  calc
    _ = sumFin (fun index => if index = row then coefficient * matrix index column else 0) := by
      apply sumFin_congr
      intro index
      rw [Multiplication.scaleIdentity_apply]
      by_cases equal : index = row
      · cases equal
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (Ne.symm equal), if_neg equal, zero_mul]
    _ = coefficient * matrix row column := sumFin_ite_eq row _

/-- Multiplication by the original right scalar identity scales each retained entry. -/
theorem mul_scaleIdentity (matrix : Rectangular K rows columns) (coefficient : K) :
    mul matrix (Multiplication.scaleIdentity coefficient) =
      ofFn (fun row column => matrix row column * coefficient) := by
  apply ext
  intro row column
  rw [mul_at, ofFn_apply]
  calc
    _ = sumFin (fun index => if index = column then matrix row index * coefficient else 0) := by
      apply sumFin_congr
      intro index
      rw [Multiplication.scaleIdentity_apply]
      by_cases equal : index = column
      · cases equal
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg equal, if_neg equal, mul_zero]
    _ = matrix row column * coefficient := sumFin_ite_eq column _

/-- The original square identity preserves a rectangle on the left. -/
theorem unit_mul (matrix : Rectangular K rows columns) :
    mul (Multiplication.scaleIdentity 1) matrix = matrix := by
  rw [scaleIdentity_mul]
  apply ext
  intro row column
  rw [ofFn_apply, one_mul]

/-- The original square identity preserves a rectangle on the right. -/
theorem mul_unit (matrix : Rectangular K rows columns) :
    mul matrix (Multiplication.scaleIdentity 1) = matrix := by
  rw [mul_scaleIdentity]
  apply ext
  intro row column
  rw [ofFn_apply, mul_one]

/-- The original scalar identity at one acts identically on structural vectors. -/
theorem apply_unit {size : Nat} (values : Vec K size) :
    apply (Multiplication.scaleIdentity 1) values = values := by
  apply vector_ext
  intro row
  rw [apply_at]
  calc
    _ = sumFin (fun column => if column = row then values column else 0) := by
      apply sumFin_congr
      intro column
      rw [Multiplication.scaleIdentity_apply]
      by_cases equal : column = row
      · cases equal
        rw [if_pos rfl, if_pos rfl, one_mul]
      · rw [if_neg (Ne.symm equal), if_neg equal, zero_mul]
    _ = values row := sumFin_ite_eq row _

/-- Transposing the original scalar identity preserves its same diagonal scalar. -/
theorem transpose_scaleIdentity (coefficient : K) {size : Nat} :
    transpose (Multiplication.scaleIdentity (n := size) coefficient) =
      Multiplication.scaleIdentity coefficient := by
  apply ext
  intro row column
  rw [transpose_apply, Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
  · rw [if_neg equal, if_neg (Ne.symm equal)]

end Purelib.LinearAlgebra.Matrix.Rectangular
