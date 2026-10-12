module

import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Shear.Integral.Lift
import Mathlib.Tactic.Linter.Lint
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Retaining an orthogonal block through an integral reduction

A cached extra matrix with zero rows and columns at the selected pivots is
unchanged by the corresponding shears. Lifting reuses each existing shear;
only the full output matrix is computed anew.
-/

namespace Purelib.LinearAlgebra.Alternating.UnitPivot

open Purelib.LinearAlgebra

variable {n : Nat}
section UnitPivot

variable {matrix : SquareMatrix.IntegralMatrix n}

/-- Retain a unit pivot after adding a block clear on its pivot rows and columns.

The original coordinates and unit-value certificate determine the augmented pivot. -/
def withExtra (pivot : UnitPivot
  matrix) (extra augmented : SquareMatrix.IntegralMatrix n)
    (split : ∀ row column, augmented row column = extra row column + matrix row column)
    (clear : SquareMatrix.Shear.Integral.Lift.ClearAt extra pivot.first pivot.last) : UnitPivot augmented :=
  ⟨pivot.first, pivot.last, by rw [split, clear.row_first, zero_add, pivot.value]⟩

open Purelib.LinearAlgebra.Alternating in
/-- Adding a block clear at the pivot leaves the computed shear unchanged. -/
theorem withExtra_shear (pivot :
  UnitPivot matrix) (extra augmented : SquareMatrix.IntegralMatrix n)
    (split : ∀ row column, augmented row column = extra row column + matrix row column)
    (clear : SquareMatrix.Shear.Integral.Lift.ClearAt extra pivot.first pivot.last) :
    (withExtra pivot extra augmented split clear).shear = pivot.shear := by
  have left : (withExtra pivot extra augmented split clear).shear.left =
    pivot.shear.left := by
    apply Data.Vector.Basic.vector_ext; intro index
    rw [shear_left, shear_left]
    change (if index = pivot.first ∨ index = pivot.last then 0 else -augmented index pivot.last) = _
    rw [split, clear.column_last, zero_add]
  have right : (withExtra pivot extra augmented split clear).shear.right =
    pivot.shear.right := by
    apply Data.Vector.Basic.vector_ext; intro index
    rw [shear_right, shear_right]
    change (if index = pivot.first ∨ index = pivot.last then 0 else augmented index pivot.first) = _
    rw [split, clear.column_first, zero_add]
  cases firstShear : (withExtra pivot extra augmented split clear).shear
  cases lastShear : pivot.shear
  rw [firstShear, lastShear] at left right
  cases left
  cases right
  rfl

end UnitPivot

section Step

variable {matrix : SquareMatrix.IntegralMatrix n} {indices : Handle.Basic.PivotIndices n}
end Step

end Purelib.LinearAlgebra.Alternating.UnitPivot

end
