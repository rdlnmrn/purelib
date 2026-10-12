module

import Purelib.Data.Vector.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Integral unit-pivot changes of basis

The rows are executable finite data. A two-column shear has an explicit
inverse, and its congruence is computed by a quadratic entry formula rather
than by repeated matrix multiplication. No nondegeneracy is assumed for the
remaining matrix.
-/

namespace Purelib.LinearAlgebra.Alternating

-- Retain the original UnitPivot.UnitPivot nominal type and all its methods.
open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.Data.Int
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

variable {n : Nat}

set_option genInjectivity false in
/-- Retain two oriented coordinates with positive unit entry in the original matrix.

The bounded first and last coordinates belong to the supplied integral matrix.
Their retained value certificate states that this same oriented entry is one;
no matrix, coordinate or witness is reconstructed. -/
structure UnitPivot (matrix : SquareMatrix.IntegralMatrix n) where
  /-- The first coordinate of the oriented pivot. -/ first : Fin n
  /-- The last coordinate of the oriented pivot. -/ last : Fin n
  /-- The selected oriented entry is positive one. -/ value : matrix first last = 1

constructive_injectivity UnitPivot

namespace UnitPivot

end UnitPivot
namespace UnitPivot

variable {matrix : SquareMatrix.IntegralMatrix n}

/-- An oriented unit pivot of a skew-symmetric integral matrix has distinct coordinates. -/
theorem distinct (pivot : UnitPivot matrix) (skew : ∀ row column, matrix row column = -matrix column row) :
    pivot.first ≠ pivot.last := by
  intro equal
  have diagonal := skew pivot.first pivot.first
  have value := pivot.value
  rw [← equal] at value
  omega0

/-- Compute the two-column shear cancelling the non-pivot entries of the two pivot rows.

Its coefficients vanish at both pivot coordinates and retain their exact structural vector data. -/
@[expose] def shear (pivot : UnitPivot matrix) : SquareMatrix.Integral.Shear pivot.first pivot.last where
  left := Data.Vector.Basic.vectorOfFn fun index => if index = pivot.first ∨ index = pivot.last then 0 else -matrix
    index pivot.last
  right := Data.Vector.Basic.vectorOfFn fun index => if index = pivot.first ∨ index = pivot.last then 0 else matrix
    index pivot.first
  left_first := by rw [Data.Vector.Basic.vectorOfFn_apply, if_pos (Or.inl rfl)]
  left_last := by rw [Data.Vector.Basic.vectorOfFn_apply, if_pos (Or.inr rfl)]
  right_first := by rw [Data.Vector.Basic.vectorOfFn_apply, if_pos (Or.inl rfl)]
  right_last := by rw [Data.Vector.Basic.vectorOfFn_apply, if_pos (Or.inr rfl)]

/-- Compute the matrix congruence by the original pivot shear.

The shear belongs to the original supplied integral matrix and its retained
unit-pivot coordinates. Its finite entry transformation uses those same
rows and original matrix entries. -/
@[expose] def reduced (pivot : UnitPivot matrix) : SquareMatrix.IntegralMatrix n := pivot.shear.transform matrix

/-- Read the signed last-column coefficient of the pivot shear. -/
theorem shear_left (pivot : UnitPivot matrix) (index : Fin n) :
    pivot.shear.left index = if index = pivot.first ∨ index = pivot.last then 0 else -matrix index pivot.last :=
  Data.Vector.Basic.vectorOfFn_apply _ index

/-- Read the first-column coefficient of the pivot shear. -/
theorem shear_right (pivot : UnitPivot matrix) (index : Fin n) :
    pivot.shear.right index = if index = pivot.first ∨ index = pivot.last then 0 else matrix index pivot.first :=
  Data.Vector.Basic.vectorOfFn_apply _ index

/-- The first reduced pivot row is the unit indicator at the last coordinate.

The original unit-pivot value and supplied skew equation determine the
pivot block. Its retained shear rows cancel every other entry in the
original first pivot row. -/
theorem reduced_first (pivot : UnitPivot matrix) (skew : ∀ row column, matrix row column = -matrix column row)
    (column : Fin n) : pivot.reduced pivot.first column = if column = pivot.last then 1 else 0 := by
  have diagonal : matrix pivot.first pivot.first = 0 := by have := skew pivot.first pivot.first; omega0
  rw [UnitPivot.reduced, SquareMatrix.Integral.Shear.transform, SquareMatrix.matrixOfFn_apply,
    pivot.shear.left_first, pivot.shear.right_first]
  simp only [Arithmetic.zero_mul, Int.add_zero]
  by_cases isFirst : column = pivot.first
  · subst column
    rw [pivot.shear.left_first, pivot.shear.right_first, Arithmetic.zero_mul, Arithmetic.zero_mul, Int.add_zero,
      Int.add_zero, diagonal,
      if_neg (pivot.distinct skew)]
  · by_cases isLast : column = pivot.last
    · subst column
      rw [pivot.shear.left_last, pivot.shear.right_last, Arithmetic.zero_mul, Arithmetic.zero_mul, Int.add_zero,
        Int.add_zero, pivot.value, if_pos rfl]
    · have neither : ¬ (column = pivot.first ∨ column = pivot.last) := fun equal => equal.elim isFirst isLast
      simp only [UnitPivot.shear, Data.Vector.Basic.vectorOfFn_apply, if_neg neither]
      rw [diagonal, pivot.value, if_neg isLast, skew column pivot.first]
      ring1

/-- The retained pivot reduction preserves the original skew symmetry.

The same cached shear rows occur on both sides of the coordinate comparison.
The supplied original matrix equations transport each term of the explicit
reduction formula, including both pivot diagonal entries. -/
theorem reduced_skew (pivot : UnitPivot matrix) (skew : ∀ row column, matrix row column = -matrix column row)
    (row column : Fin n) : pivot.reduced row column = -pivot.reduced column row := by
  have firstDiagonal : matrix pivot.first pivot.first = 0 := by have := skew pivot.first pivot.first; omega0
  have lastDiagonal : matrix pivot.last pivot.last = 0 := by have := skew pivot.last pivot.last; omega0
  change pivot.shear.transform matrix row column = -pivot.shear.transform matrix column row
  rw [SquareMatrix.Integral.Shear.transform_apply, SquareMatrix.Integral.Shear.transform_apply]
  simp only [firstDiagonal, lastDiagonal, Int.mul_zero, Int.add_zero]
  rw [skew row column, skew pivot.first column, skew pivot.last column, skew row pivot.first,
    skew row pivot.last, skew pivot.last pivot.first]
  ring1

/-- The last reduced pivot row is the negative unit indicator at the first coordinate.

The original unit-pivot value and supplied skew equation determine the
opposite pivot entry. Its retained shear rows cancel every other entry in
the original last pivot row. -/
theorem reduced_last (pivot : UnitPivot matrix) (skew : ∀ row column, matrix row column = -matrix column row)
    (column : Fin n) : pivot.reduced pivot.last column = if column = pivot.first then -1 else 0 := by
  have diagonal : matrix pivot.last pivot.last = 0 := by have := skew pivot.last pivot.last; omega0
  have opposite : matrix pivot.last pivot.first = -1 := by rw [skew, pivot.value]
  rw [UnitPivot.reduced, SquareMatrix.Integral.Shear.transform, SquareMatrix.matrixOfFn_apply,
    pivot.shear.left_last, pivot.shear.right_last]
  simp only [Arithmetic.zero_mul, Int.add_zero]
  by_cases isFirst : column = pivot.first
  · subst column
    rw [pivot.shear.left_first, pivot.shear.right_first, Arithmetic.zero_mul, Arithmetic.zero_mul, Int.add_zero,
      Int.add_zero, opposite, if_pos rfl]
  · by_cases isLast : column = pivot.last
    · subst column
      rw [pivot.shear.left_last, pivot.shear.right_last, Arithmetic.zero_mul, Arithmetic.zero_mul, Int.add_zero,
        Int.add_zero, diagonal, if_neg isFirst]
    · have neither : ¬ (column = pivot.first ∨ column = pivot.last) := fun equal => equal.elim isFirst isLast
      simp only [UnitPivot.shear, Data.Vector.Basic.vectorOfFn_apply, if_neg neither]
      rw [diagonal, opposite, if_neg isFirst, skew column pivot.last]
      ring1

/-- Read a non-pivot output entry by the explicit two-product correction formula.

Both row and column are supplied distinct from the two pivot coordinates. -/
theorem reduced_remaining (pivot : UnitPivot matrix) (skew : ∀ row column, matrix row column = -matrix column row)
    (row column : Fin n) (rowFirst : row ≠ pivot.first) (rowLast : row ≠ pivot.last)
    (columnFirst : column ≠ pivot.first) (columnLast : column ≠ pivot.last) :
    pivot.reduced row column = matrix row column +
      matrix row pivot.last * matrix column pivot.first - matrix row pivot.first * matrix column pivot.last := by
  have firstDiagonal : matrix pivot.first pivot.first = 0 := by have := skew pivot.first pivot.first; omega0
  have lastDiagonal : matrix pivot.last pivot.last = 0 := by have := skew pivot.last pivot.last; omega0
  have rowNeither : ¬ (row = pivot.first ∨ row = pivot.last) := fun equal => equal.elim rowFirst rowLast
  have columnNeither : ¬ (column = pivot.first ∨ column = pivot.last) := fun equal => equal.elim columnFirst columnLast
  change pivot.shear.transform matrix row column = _
  rw [SquareMatrix.Integral.Shear.transform_apply]
  simp only [UnitPivot.shear_left, UnitPivot.shear_right, if_neg rowNeither, if_neg columnNeither,
    firstDiagonal, lastDiagonal, Int.mul_zero, Int.add_zero]
  rw [skew pivot.first column, skew pivot.last column, skew pivot.last pivot.first, pivot.value]
  ring1

end UnitPivot

end Purelib.LinearAlgebra.Alternating

end
