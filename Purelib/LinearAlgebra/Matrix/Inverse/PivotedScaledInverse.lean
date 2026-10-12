module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Matrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Schur
import Purelib.LinearAlgebra.Vector.Dot

import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Pivot-complete finite scaled inversion

The basic fraction-free block inverse is deliberately total, but fixes the
upper-left entry as its pivot at every recursive stage.  Its scalar can
therefore vanish for an invertible matrix.  This module keeps the construction
finite and polynomial while removing that accidental restriction: at every
stage it evaluates every displayed row/column pivot, transports the resulting
scaled inverses back to the original matrix, and combines them with conjugate
weights.  The combined scalar is a finite sum of Gaussian norm squares, so
there is no cancellation between successful pivot branches.
-/

-- Retain exact public scalar/carrier shorthand names after subject placement.

namespace Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse

open Purelib
open Purelib.Algebra
open Purelib.Data.Rat
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

public section

/-- The exact rational coordinate type. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A finite square structural matrix of Gaussian rationals. -/
abbrev Square (size : Nat) :=
  SquareMatrix SquareMatrix.Inverse.PivotedScaledInverse.Gaussian size
/-- A scaled inverse certificate for the retained Gaussian square matrix. -/
abbrev ScaledInverse {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) :=
  SquareMatrix.Inverse.Scaled.Basic.ScaledInverse matrix

open Purelib.Data.Gaussian.Basic.Canonical

/-! ## Finite transpositions -/

/-- Swap index zero with one displayed pivot index. -/
@[expose] def swapZero {size : Nat} (pivot index : Fin (size + 1)) : Fin (size + 1) :=
  if index = 0 then pivot else if index = pivot then 0 else index

/-- The transposition sends the leading coordinate to its retained pivot.

The first scalar equality test succeeds at that same coordinate, so the
original conditional construction returns its supplied pivot. -/
@[simp] theorem swapZero_zero {size : Nat} (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot 0 = pivot := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.swapZero
  rewrite [if_pos (Eq.refl (0 : Fin (size + 1)))]
  exact Eq.refl _

/-- The transposition sends its retained pivot to the leading coordinate.

A pivot already at the leading coordinate is retained. Otherwise the first
comparison fails and the second comparison selects the original zero index. -/
theorem swapZero_pivot {size : Nat} (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot pivot = 0 := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.swapZero
  by_cases pivotZero : pivot = 0
  · rewrite [if_pos pivotZero]
    exact pivotZero
  · rewrite [if_neg pivotZero, if_pos (Eq.refl pivot)]
    exact Eq.refl _

/-- The transposition fixes coordinates distinct from zero and its pivot.

The two supplied inequalities reject the original conditional branches.
The remaining branch retains the original bounded coordinate. -/
theorem swapZero_of_ne {size : Nat} {pivot index : Fin (size + 1)}
    (indexZero : index ≠ 0) (indexPivot : index ≠ pivot) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot index = index := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.swapZero
  rewrite [if_neg indexZero, if_neg indexPivot]
  exact Eq.refl _

/-- Applying the transposition twice restores the original coordinate.

The leading and pivot cases exchange those two retained positions. Every
other finite coordinate is fixed by both applications. -/
@[simp] theorem swapZero_involutive {size : Nat}
    (pivot index : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot
      index) = index := by
  by_cases indexZero : index = 0
  · cases indexZero
    rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero,
      SquareMatrix.Inverse.PivotedScaledInverse.swapZero_pivot]
    exact Eq.refl _
  · by_cases indexPivot : index = pivot
    · cases indexPivot
      rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_pivot,
        SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero]
      exact Eq.refl _
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_of_ne indexZero indexPivot,
        SquareMatrix.Inverse.PivotedScaledInverse.swapZero_of_ne indexZero indexPivot]
      exact Eq.refl _

/-- The displayed transposition is injective on the retained finite index type. -/
theorem swapZero_injective {size : Nat} (pivot : Fin (size + 1))
    {left right : Fin (size + 1)}
    (equal : SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot left =
      SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot right) : left = right := by
  have reapplied := congrArg (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot) equal
  simpa only [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive] using reapplied

/-- A finite commutative sum is invariant under the displayed transposition.

The two retained correction functions isolate the leading and pivot entries.
Their original finite sums cancel, leaving all other summands unchanged. -/
theorem sumFin_swapZero {K : Type*} [CommRing K] {size : Nat}
    (pivot : Fin (size + 1)) (values : Fin (size + 1) → K) :
    FiniteSum.Fin.sumFin
        (fun index => values (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot index)) =
      FiniteSum.Fin.sumFin values := by
  by_cases pivotZero : pivot = 0
  · subst pivot
    apply FiniteSum.Fin.sumFin_congr
    intro index
    by_cases indexZero : index = 0
    · cases indexZero
      rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero]
      exact Eq.refl _
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_of_ne indexZero indexZero]
      exact Eq.refl _
  · let correctionZero : Fin (size + 1) → K := fun index =>
      if index = 0 then values pivot - values 0 else 0
    let correctionPivot : Fin (size + 1) → K := fun index =>
      if index = pivot then values 0 - values pivot else 0
    have pointwise : forall index,
        values (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot index) =
          values index + correctionZero index + correctionPivot index := by
      intro index
      by_cases indexZero : index = 0
      · subst index
        rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero]
        dsimp only [correctionZero, correctionPivot]
        rewrite [if_pos (Eq.refl (0 : Fin (size + 1))), if_neg (Ne.symm pivotZero)]
        ring1
      · by_cases indexPivot : index = pivot
        · subst index
          rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_pivot]
          dsimp only [correctionZero, correctionPivot]
          rewrite [if_neg pivotZero, if_pos (Eq.refl pivot)]
          ring1
        · rw [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_of_ne indexZero indexPivot]
          dsimp only [correctionZero, correctionPivot]
          rewrite [if_neg indexZero, if_neg indexPivot]
          ring1
    rw [FiniteSum.Fin.sumFin_congr pointwise]
    rw [FiniteSum.Fin.sumFin_add,
      FiniteSum.Fin.sumFin_add]
    have zeroCorrection :
        FiniteSum.Fin.sumFin correctionZero =
          values pivot - values 0 := by
      unfold correctionZero
      exact FiniteSum.Fin.sumFin_ite_eq 0
        (fun _ => values pivot - values 0)
    have pivotCorrection :
        FiniteSum.Fin.sumFin correctionPivot =
          values 0 - values pivot := by
      unfold correctionPivot
      exact FiniteSum.Fin.sumFin_ite_eq pivot
        (fun _ => values 0 - values pivot)
    rw [zeroCorrection, pivotCorrection]
    ring1

/-- Swap two rows, retaining structural finite matrix data. -/
@[expose] def swapRows {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (pivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1) :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot row) column

/-- Swap two columns. -/
@[expose] def swapColumns {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (pivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1) :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix row (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot column)

/-- Read a row-swapped matrix at the transposed original row index. -/
@[simp] theorem swapRows_apply {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (pivot row column : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows matrix pivot row column = matrix
      (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot row) column :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Read a column-swapped matrix at the transposed original column index. -/
@[simp] theorem swapColumns_apply {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (pivot row column : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns matrix pivot row column = matrix row
      (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Swapping the same two rows twice restores the original matrix.

Each structural matrix entry reads the involutive transposition of its
original row while retaining the same column. -/
@[simp] theorem swapRows_involutive {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows (SquareMatrix.Inverse.PivotedScaledInverse.swapRows matrix pivot)
      pivot = matrix := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive]
  exact Eq.refl _

/-- Swapping the same two columns twice restores the original matrix.

Each structural matrix entry reads the involutive transposition of its
original column while retaining the same row. -/
@[simp] theorem swapColumns_involutive {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns matrix
      pivot) pivot = matrix := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive]
  exact Eq.refl _

/-- Matching inner column and row transpositions leave a matrix product unchanged. -/
theorem mul_swapColumns_swapRows {size : Nat}
    (left right : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns left pivot)
        (SquareMatrix.Inverse.PivotedScaledInverse.swapRows right pivot) =
      SquareMatrix.Multiplication.mul left right := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Multiplication.mul_apply,
    SquareMatrix.Multiplication.mul_apply]
  calc
    FiniteSum.Fin.sumFin (fun middle =>
        SquareMatrix.Inverse.PivotedScaledInverse.swapColumns left pivot row middle *
          SquareMatrix.Inverse.PivotedScaledInverse.swapRows right pivot middle column) =
        FiniteSum.Fin.sumFin (fun middle =>
          left row (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot middle) *
            right (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot middle) column) := by
      apply FiniteSum.Fin.sumFin_congr
      intro middle
      rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
        SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply]
    _ = FiniteSum.Fin.sumFin (fun middle =>
          left row middle * right middle column) :=
      SquareMatrix.Inverse.PivotedScaledInverse.sumFin_swapZero pivot
        (fun middle => left row middle * right middle column)

/-- Move an inner column transposition from the left factor to the rows of the right factor. -/
theorem mul_swapColumns_left {size : Nat}
    (left right : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns left pivot) right =
      SquareMatrix.Multiplication.mul left (SquareMatrix.Inverse.PivotedScaledInverse.swapRows right pivot) := by
  have cancellation := SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_swapRows left
    (SquareMatrix.Inverse.PivotedScaledInverse.swapRows right pivot) pivot
  simpa only [SquareMatrix.Inverse.PivotedScaledInverse.swapRows_involutive] using cancellation

/-- Move an inner row transposition from the right factor to the columns of the left factor. -/
theorem mul_swapRows_right {size : Nat}
    (left right : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Multiplication.mul left (SquareMatrix.Inverse.PivotedScaledInverse.swapRows right pivot) =
      SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns left pivot) right :=
  (SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_left left right pivot).symm

/-- A column transposition of the right factor transposes the same columns of the product. -/
theorem mul_swapColumns_right {size : Nat}
    (left right : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Multiplication.mul left (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns right pivot) =
      SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Multiplication.mul left right) pivot := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Multiplication.mul_apply, SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Multiplication.mul_apply]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply]

/-- A row transposition of the left factor transposes the same rows of the product. -/
theorem mul_swapRows_left {size : Nat}
    (left right : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (pivot : Fin (size + 1)) :
    SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.PivotedScaledInverse.swapRows left pivot) right =
      SquareMatrix.Inverse.PivotedScaledInverse.swapRows (SquareMatrix.Multiplication.mul left right) pivot := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Multiplication.mul_apply, SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Multiplication.mul_apply]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply]

/-- Matching row and column transpositions preserve a scalar identity matrix.

Equal retained coordinates remain equal after the same injective transposition.
Distinct coordinates remain distinct, so the same diagonal scalar is selected. -/
theorem swapRows_swapColumns_scaleIdentity {size : Nat}
    (scalar : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows
        (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
          (SquareMatrix.Multiplication.scaleIdentity scalar) pivot) pivot =
      SquareMatrix.Multiplication.scaleIdentity scalar := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Multiplication.scaleIdentity_apply, SquareMatrix.Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rewrite [if_pos (Eq.refl _), if_pos (Eq.refl _)]
    exact Eq.refl _
  · rewrite [if_neg equal]
    rewrite [if_neg (fun swappedEqual =>
      equal (SquareMatrix.Inverse.PivotedScaledInverse.swapZero_injective pivot swappedEqual))]
    exact Eq.refl _

/-- Matching column and row transpositions preserve a scalar identity matrix.

The same injective transposition preserves the retained equality test for
the two finite coordinates, leaving every diagonal and off-diagonal entry intact. -/
theorem swapColumns_swapRows_scaleIdentity {size : Nat}
    (scalar : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (pivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
        (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
          (SquareMatrix.Multiplication.scaleIdentity scalar) pivot) pivot =
      SquareMatrix.Multiplication.scaleIdentity scalar := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
    SquareMatrix.Multiplication.scaleIdentity_apply, SquareMatrix.Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rewrite [if_pos (Eq.refl _), if_pos (Eq.refl _)]
    exact Eq.refl _
  · rewrite [if_neg equal]
    rewrite [if_neg (fun swappedEqual =>
      equal (SquareMatrix.Inverse.PivotedScaledInverse.swapZero_injective pivot swappedEqual))]
    exact Eq.refl _

/-- Move one displayed entry to the upper-left corner. -/
@[expose] def pivotMatrix {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1) :=
  SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Inverse.PivotedScaledInverse.swapRows matrix
    rowPivot) columnPivot

/-! ## Constructive left-kernel completeness -/

/-- A finite square matrix has trivial displayed left kernel.  This
formulation is deliberately pointwise: both the vector and every vanishing
column are finite structural data. -/
@[expose] def LeftKernelTrivial {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) : Prop :=
  forall vector : Data.Vector SquareMatrix.Inverse.PivotedScaledInverse.Gaussian size,
    (forall column,
      SquareMatrix.Multiplication.vectorMatrix vector matrix column = 0) ->
      forall row, vector row = 0

/-- Moving a displayed matrix entry to the upper-left corner preserves
triviality of the finite left kernel. -/
theorem leftKernelTrivial_pivotMatrix {size : Nat}
    {matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)} (trivial :
      SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix)
    (rowPivot columnPivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
      matrix rowPivot columnPivot) := by
  intro vector kernel row
  let unpivoted := Data.Vector.Basic.vectorOfFn fun index =>
    vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index)
  have unpivotedKernel : forall column,
      SquareMatrix.Multiplication.vectorMatrix unpivoted matrix column = 0 := by
    intro column
    have pivotKernel := kernel (SquareMatrix.Inverse.PivotedScaledInverse.swapZero columnPivot column)
    rw [SquareMatrix.Multiplication.vectorMatrix_apply] at pivotKernel
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun index => vector index *
        matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) column)
      (fun index => by
        unfold SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
        rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
          SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
          SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive])]
      at pivotKernel
    rw [SquareMatrix.Multiplication.vectorMatrix_apply]
    have sumZero : FiniteSum.Fin.sumFin
        (fun index => vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) * matrix index column)
          =
          0 := by
      calc
      FiniteSum.Fin.sumFin
          (fun index => vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) * matrix index
            column) =
          FiniteSum.Fin.sumFin
            (fun index =>
              (fun source => vector source *
                matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot source) column)
                  (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index)) := by
            apply FiniteSum.Fin.sumFin_congr
            intro index
            change vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) * matrix index column =
              vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) *
                matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot
                  (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index)) column
            rw [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive]
      _ = FiniteSum.Fin.sumFin
            (fun index => vector index *
              matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) column) :=
          by
            let values := fun source => vector source *
              matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot source) column
            change FiniteSum.Fin.sumFin (fun index =>
                values (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index)) =
              FiniteSum.Fin.sumFin values
            exact SquareMatrix.Inverse.PivotedScaledInverse.sumFin_swapZero rowPivot values
      _ = 0 := pivotKernel
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun index =>
        vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) * matrix index column)
      (fun index => by
        rw [show unpivoted index = vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot index) by
          unfold unpivoted
          exact Data.Vector.Basic.vectorOfFn_apply _ _])]
    exact sumZero
  have zero := trivial unpivoted unpivotedKernel (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot row)
  rw [show unpivoted (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot row) =
      vector (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot
        (SquareMatrix.Inverse.PivotedScaledInverse.swapZero rowPivot row)) by
        exact Data.Vector.Basic.vectorOfFn_apply _ _] at zero
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapZero_involutive]
    at zero
  exact zero

set_option genInjectivity false in
/-- A retained nonzero vector coordinate or pointwise vanishing certificate.

Both outcomes refer to the original bounded coordinate function. Success
retains its exact index and nonzero evidence; failure certifies every original entry. -/
private inductive NonzeroVectorResult (count : Nat)
    (values : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain a bounded vector index and the nonvanishing of its original entry. -/ | found (index : Fin count) (nonzero
    : values index ≠ 0)
  /-- Certify that every original vector entry is zero. -/ | allZero (zero : forall index, values index = 0)

constructive_injectivity NonzeroVectorResult

/-- Scan the bounded Gaussian coordinates for a nonzero entry.

The finite recursion retains the first successful index or certifies complete pointwise vanishing. -/
private def nonzeroVectorSearch (count : Nat)
    (values : Fin count -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.NonzeroVectorResult count values := by
  cases count with
  | zero =>
      exact .allZero fun index => Fin.elim0 index
  | succ count =>
      by_cases headZero : values 0 = 0
      · cases Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.nonzeroVectorSearch count
          (fun index => values index.succ) with
        | found index nonzero => exact .found index.succ nonzero
        | allZero tailZero =>
            exact .allZero fun index =>
              Data.Fin.cases_induction
                (by change values 0 = 0; exact headZero)
                (fun tail => tailZero tail) index
      · exact .found 0 headZero

set_option genInjectivity false in
/-- A retained nonzero matrix entry or pointwise vanishing certificate.

Both outcomes refer to the original bounded row and column inputs. Success
retains both original indices; failure certifies every original matrix entry. -/
private inductive NonzeroMatrixResult (rowCount columnCount : Nat)
    (matrix : Fin rowCount -> Fin columnCount -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) where
  /-- Retain bounded matrix indices and the nonvanishing of their original entry. -/ | found (row : Fin rowCount)
    (column : Fin columnCount)
      (nonzero : matrix row column ≠ 0)
  /-- Certify that every original matrix entry is zero. -/ | allZero (zero : forall row column, matrix row column = 0)

constructive_injectivity NonzeroMatrixResult

/-- Scan the bounded Gaussian matrix in row order for a nonzero entry.

The result retains both original indices or a pointwise zero certificate for the entire matrix. -/
private def nonzeroMatrixSearch (rowCount columnCount : Nat)
    (matrix : Fin rowCount -> Fin columnCount -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.NonzeroMatrixResult rowCount
      columnCount matrix := by
  cases rowCount with
  | zero =>
      exact .allZero fun row => Fin.elim0 row
  | succ rowCount =>
      cases Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.nonzeroVectorSearch
        columnCount (matrix 0) with
      | found column nonzero => exact .found 0 column nonzero
      | allZero headZero =>
          cases Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.nonzeroMatrixSearch
            rowCount columnCount
              (fun row => matrix row.succ) with
          | found row column nonzero =>
              exact .found row.succ column nonzero
          | allZero tailZero =>
              exact .allZero fun row =>
                Data.Fin.cases_induction
                  (by change ∀ column, matrix 0 column = 0; exact headZero)
                  (fun tail => tailZero tail) row

/-- A nonempty matrix with trivial left kernel contains a displayed nonzero
entry.  The witness is found by explicit structural search over its two
finite index dimensions. -/
theorem exists_nonzero_entry_of_leftKernelTrivial {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (trivial :
      SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix) :
    exists row column, matrix row column ≠ 0 := by
  cases LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.nonzeroMatrixSearch (size + 1) (size + 1)
      (fun row column => matrix row column) with
  | found row column nonzero => exact ⟨row, column, nonzero⟩
  | allZero allZero =>
    let selected := Data.Vector.Basic.vectorOfFn fun row =>
      if row = (0 : Fin (size + 1)) then (1 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) else 0
    have selectedKernel : forall column,
        SquareMatrix.Multiplication.vectorMatrix selected matrix column = 0 := by
      intro column
      rw [SquareMatrix.Multiplication.vectorMatrix_apply]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun _ => (0 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)) (fun row => by
          rw [allZero row column, Data.Gaussian.Basic.mul_zero])]
      exact FiniteSum.Fin.sumFin_zero
    have selectedZero := trivial selected selectedKernel 0
    change (if (0 : Fin (size + 1)) = 0 then (1 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) else 0) = 0
      at selectedZero
    exact (one_ne_zero selectedZero).elim

/-- Triviality of the left kernel descends to the Schur matrix at a nonzero pivot.

The retained tail vector is lifted with its original column pairing. Its
finite product vanishes by the Schur identity, and the original nonzero head
then forces every original tail coordinate to vanish. -/
theorem leftKernelTrivial_schur_of_head_nonzero {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (trivial :
      SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix)
    (headNonzero : SquareMatrix.Blocks.head matrix ≠ 0) :
    SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial (SquareMatrix.Schur.schur matrix) := by
  intro vector kernel row
  let columnPairing := Dot.dot vector
    (SquareMatrix.Blocks.leftColumn matrix)
  let lifted : Data.Vector SquareMatrix.Inverse.PivotedScaledInverse.Gaussian (size + 1) :=
    Data.Vector.Basic.vectorOfFn fun index =>
      Data.Fin.cases (-columnPairing)
        (fun tail => SquareMatrix.Blocks.head matrix * vector tail) index
  have lifted_zero : lifted 0 = -columnPairing := by
    unfold lifted
    rewrite [Data.Vector.Basic.vectorOfFn_apply]
    change Data.Fin.cases (-columnPairing)
      (fun tail => SquareMatrix.Blocks.head matrix * vector tail)
      (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = -columnPairing
    exact Data.Fin.cases_zero _ _
  have lifted_succ (index : Fin size) :
      lifted index.succ =
        SquareMatrix.Blocks.head matrix * vector index := by
    unfold lifted
    rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.cases_succ]
    exact Eq.refl _
  have liftedKernel : forall column,
      SquareMatrix.Multiplication.vectorMatrix lifted matrix column = 0 := by
    intro column
    refine Data.Fin.cases_induction ?_ (fun tailColumn => ?_) column
    · change SquareMatrix.Multiplication.vectorMatrix lifted matrix
        (0 : Fin (size + 1)) = 0
      rw [SquareMatrix.Multiplication.vectorMatrix_apply,
        FiniteSum.Fin.sumFin_succ]
      rw [lifted_zero]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun index => SquareMatrix.Blocks.head matrix *
          vector index * matrix index.succ 0)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 0 +
            FiniteSum.Fin.sumFin (fun index =>
              matrix 0 0 * vector index * matrix index.succ 0) =
            -columnPairing * SquareMatrix.Blocks.head matrix +
              FiniteSum.Fin.sumFin (fun index =>
                SquareMatrix.Blocks.head matrix * vector index *
                  SquareMatrix.Blocks.leftColumn matrix index) := by
          change -columnPairing * SquareMatrix.Blocks.head matrix +
              FiniteSum.Fin.sumFin (fun index =>
                SquareMatrix.Blocks.head matrix * vector index *
                  matrix index.succ 0) = _
          apply congrArg (fun total : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian =>
            -columnPairing * SquareMatrix.Blocks.head matrix + total)
          apply FiniteSum.Fin.sumFin_congr
          intro index
          rw [SquareMatrix.Blocks.leftColumn_apply]
        _ = 0 := by
          rw [FiniteSum.Fin.sumFin_congr
            (right := fun index => SquareMatrix.Blocks.head matrix *
              (vector index *
                SquareMatrix.Blocks.leftColumn matrix index))
            (fun _ => by ring1)]
          rw [FiniteSum.Fin.sumFin_mul_left]
          unfold columnPairing Dot.dot
          ring1
    · rw [SquareMatrix.Multiplication.vectorMatrix_apply,
        FiniteSum.Fin.sumFin_succ]
      rw [lifted_zero]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun index => SquareMatrix.Blocks.head matrix *
          vector index * matrix index.succ tailColumn.succ)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 tailColumn.succ +
            FiniteSum.Fin.sumFin (fun index =>
              SquareMatrix.Blocks.head matrix * vector index *
                matrix index.succ tailColumn.succ) =
            -columnPairing *
                SquareMatrix.Blocks.topRow matrix tailColumn +
              FiniteSum.Fin.sumFin (fun index =>
                SquareMatrix.Blocks.head matrix * vector index *
                  SquareMatrix.Blocks.tail matrix index
                    tailColumn) := by
          rw [show matrix 0 tailColumn.succ =
              SquareMatrix.Blocks.topRow matrix tailColumn by
            exact (SquareMatrix.Blocks.topRow_apply
              matrix tailColumn).symm]
          apply congrArg (fun total : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian =>
            -columnPairing *
              SquareMatrix.Blocks.topRow matrix tailColumn + total)
          apply FiniteSum.Fin.sumFin_congr
          intro index
          rw [SquareMatrix.Blocks.tail_apply]
        _ = SquareMatrix.Blocks.head matrix *
                SquareMatrix.Multiplication.vectorMatrix vector
                  (SquareMatrix.Blocks.tail matrix) tailColumn -
              Dot.dot vector
                  (SquareMatrix.Blocks.leftColumn matrix) *
                SquareMatrix.Blocks.topRow matrix tailColumn := by
          rw [SquareMatrix.Multiplication.vectorMatrix_apply]
          rw [FiniteSum.Fin.sumFin_congr
            (right := fun index =>
              SquareMatrix.Blocks.head matrix *
                (vector index *
                  SquareMatrix.Blocks.tail matrix index tailColumn))
            (fun _ => by ring1)]
          rw [FiniteSum.Fin.sumFin_mul_left]
          unfold columnPairing
          ring1
        _ = SquareMatrix.Multiplication.vectorMatrix vector
              (SquareMatrix.Schur.schur matrix) tailColumn := by
          exact (SquareMatrix.Schur.vectorMatrix_schur
            vector matrix tailColumn).symm
        _ = 0 := kernel tailColumn
  have productZero := trivial lifted liftedKernel row.succ
  rw [show lifted row.succ =
      SquareMatrix.Blocks.head matrix * vector row by
        exact Data.Vector.Basic.vectorOfFn_apply _ _] at productZero
  by_cases vectorZero : vector row = 0
  · exact vectorZero
  · exact (Data.Gaussian.Field.mul_ne_zero_direct
      headNonzero vectorZero productZero).elim

/-- Transport a scaled inverse of a row/column-pivoted matrix back to the
original matrix. -/
@[expose] def unpivotScaledInverse {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse
      (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot)) :
    SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix where
  scalar := inverse.scalar
  inverse := SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
    inverse.inverse columnPivot) rowPivot
  left_identity := by
    have pivotLeft := inverse.left_identity
    unfold SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix at pivotLeft
    rw [SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_right] at pivotLeft
    have uncolumned := congrArg
      (fun value : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1) =>
        SquareMatrix.Inverse.PivotedScaledInverse.swapColumns value columnPivot)
      pivotLeft
    simp only [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_involutive]
      at uncolumned
    calc
      SquareMatrix.Multiplication.mul
          (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
            inverse.inverse columnPivot) rowPivot)
            matrix =
          SquareMatrix.Multiplication.mul
            (SquareMatrix.Inverse.PivotedScaledInverse.swapRows inverse.inverse columnPivot)
              (SquareMatrix.Inverse.PivotedScaledInverse.swapRows matrix rowPivot) :=
        SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_left _ _ _
      _ = SquareMatrix.Inverse.PivotedScaledInverse.swapRows
            (SquareMatrix.Multiplication.mul inverse.inverse
              (SquareMatrix.Inverse.PivotedScaledInverse.swapRows matrix rowPivot)) columnPivot :=
        SquareMatrix.Inverse.PivotedScaledInverse.mul_swapRows_left _ _ _
      _ = SquareMatrix.Inverse.PivotedScaledInverse.swapRows
            (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
              (SquareMatrix.Multiplication.scaleIdentity inverse.scalar)
                columnPivot) columnPivot := by
        rw [uncolumned]
      _ = SquareMatrix.Multiplication.scaleIdentity inverse.scalar :=
        SquareMatrix.Inverse.PivotedScaledInverse.swapRows_swapColumns_scaleIdentity _ _
  right_identity := by
    have pivotRight := inverse.right_identity
    unfold SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix at pivotRight
    rw [SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_left,
      SquareMatrix.Inverse.PivotedScaledInverse.mul_swapRows_left] at pivotRight
    have unrowed := congrArg
      (fun value : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1) =>
        SquareMatrix.Inverse.PivotedScaledInverse.swapRows value rowPivot) pivotRight
    simp only [SquareMatrix.Inverse.PivotedScaledInverse.swapRows_involutive]
      at unrowed
    calc
      SquareMatrix.Multiplication.mul matrix
          (SquareMatrix.Inverse.PivotedScaledInverse.swapColumns (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
            inverse.inverse columnPivot) rowPivot) =
          SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
            (SquareMatrix.Multiplication.mul matrix
              (SquareMatrix.Inverse.PivotedScaledInverse.swapRows inverse.inverse columnPivot)) rowPivot :=
        SquareMatrix.Inverse.PivotedScaledInverse.mul_swapColumns_right _ _ _
      _ = SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
            (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
              (SquareMatrix.Multiplication.scaleIdentity inverse.scalar)
                rowPivot) rowPivot := by
        rw [unrowed]
      _ = SquareMatrix.Multiplication.scaleIdentity inverse.scalar :=
        SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_swapRows_scaleIdentity _ _

/-- Undoing the row and column pivots preserves the retained inverse scalar. -/
@[simp] theorem unpivotScaledInverse_scalar {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse
      (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot)) :
    (SquareMatrix.Inverse.PivotedScaledInverse.unpivotScaledInverse matrix rowPivot columnPivot inverse).scalar =
      inverse.scalar := rfl

/-! ## Finite aggregation of scaled inverses -/

/-- Entrywise finite weighted sum of square matrices. -/
@[expose] def weightedMatrix {count size : Nat} (weights : Fin count →
  SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)
    (matrices : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Square size) :
      SquareMatrix.Inverse.PivotedScaledInverse.Square size :=
  SquareMatrix.matrixOfFn fun row column =>
    FiniteSum.Fin.sumFin fun index =>
      weights index * matrices index row column

/-- Read the weighted matrix at one entry as the finite sum of weighted original entries. -/
@[simp] theorem weightedMatrix_apply {count size : Nat}
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (matrices : Fin count →
      SquareMatrix.Inverse.PivotedScaledInverse.Square size)
    (row column : Fin size) :
    SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights matrices row column =
      FiniteSum.Fin.sumFin fun index =>
        weights index * matrices index row column :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Right multiplication distributes over a finite weighted sum of Gaussian matrices. -/
theorem mul_weightedMatrix_left {count size : Nat}
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (matrices : Fin count →
      SquareMatrix.Inverse.PivotedScaledInverse.Square size)
    (right : SquareMatrix.Inverse.PivotedScaledInverse.Square size) :
    SquareMatrix.Multiplication.mul (SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights matrices) right =
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
        (fun index => SquareMatrix.Multiplication.mul
          (matrices index) right) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Multiplication.mul_apply, SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      FiniteSum.Fin.sumFin fun index =>
        (weights index * matrices index row middle) * right middle column)
    (fun middle => by
      rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
      exact (FiniteSum.Fin.sumFin_mul_right
        (fun index => weights index * matrices index row middle)
          (right middle column)).symm)]
  rw [FiniteSum.Fin.sumFin_swap]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [SquareMatrix.Multiplication.mul_apply]
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  ring1

/-- Left multiplication distributes over a finite weighted sum of Gaussian matrices. -/
theorem mul_weightedMatrix_right {count size : Nat}
    (left : SquareMatrix.Inverse.PivotedScaledInverse.Square size) (weights : Fin count →
      SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)
    (matrices : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Square size) :
    SquareMatrix.Multiplication.mul left (SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights matrices) =
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
        (fun index => SquareMatrix.Multiplication.mul left
          (matrices index)) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Multiplication.mul_apply, SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      FiniteSum.Fin.sumFin fun index =>
        weights index * (left row middle * matrices index middle column))
    (fun middle => by
      rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
      rw [← FiniteSum.Fin.sumFin_mul_left]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      ring1)]
  rw [FiniteSum.Fin.sumFin_swap]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [SquareMatrix.Multiplication.mul_apply]
  rw [← FiniteSum.Fin.sumFin_mul_left]

/-- A weighted sum of scalar identities is the identity with the corresponding weighted scalar sum. -/
theorem weightedMatrix_scaleIdentity {count size : Nat}
    (weights scalars : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
        (fun index => (SquareMatrix.Multiplication.scaleIdentity
          (scalars index) : SquareMatrix.Inverse.PivotedScaledInverse.Square size)) =
      SquareMatrix.Multiplication.scaleIdentity
        (FiniteSum.Fin.sumFin fun index =>
          weights index * scalars index) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply,
    SquareMatrix.Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [SquareMatrix.Multiplication.scaleIdentity_apply, if_pos rfl]
  · rw [if_neg equal]
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun _ => (0 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)) (fun index => by
        rw [SquareMatrix.Multiplication.scaleIdentity_apply, if_neg equal,
          Data.Gaussian.Basic.mul_zero])]
    exact FiniteSum.Fin.sumFin_zero

/-- Any finite weighted sum of scaled inverses is another scaled inverse.
This algebraic closure is what permits all pivot branches to be retained
without making a discontinuous pivot choice. -/
@[expose] def aggregateScaledInverse {count size : Nat} {matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size}
    (branches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix)
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
      SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix where
  scalar := FiniteSum.Fin.sumFin fun index =>
    weights index * (branches index).scalar
  inverse := SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights fun index => (branches index).inverse
  left_identity := by
    rw [SquareMatrix.Inverse.PivotedScaledInverse.mul_weightedMatrix_left]
    calc
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
          (fun index => SquareMatrix.Multiplication.mul
            (branches index).inverse matrix) =
          SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
            (fun index => (SquareMatrix.Multiplication.scaleIdentity
              (branches index).scalar : SquareMatrix.Inverse.PivotedScaledInverse.Square size)) := by
        apply SquareMatrix.matrix_ext
        intro row column
        rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply,
          SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
        apply FiniteSum.Fin.sumFin_congr
        intro index
        rw [SquareMatrix.matrix_eq_at
          (branches index).left_identity row column]
      _ = SquareMatrix.Multiplication.scaleIdentity
            (FiniteSum.Fin.sumFin fun index =>
              weights index * (branches index).scalar) :=
        SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)
  right_identity := by
    rw [SquareMatrix.Inverse.PivotedScaledInverse.mul_weightedMatrix_right]
    calc
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
          (fun index => SquareMatrix.Multiplication.mul matrix
            (branches index).inverse) =
          SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix weights
            (fun index => (SquareMatrix.Multiplication.scaleIdentity
              (branches index).scalar : SquareMatrix.Inverse.PivotedScaledInverse.Square size)) := by
        apply SquareMatrix.matrix_ext
        intro row column
        rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply,
          SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
        apply FiniteSum.Fin.sumFin_congr
        intro index
        rw [SquareMatrix.matrix_eq_at
          (branches index).right_identity row column]
      _ = SquareMatrix.Multiplication.scaleIdentity
            (FiniteSum.Fin.sumFin fun index =>
              weights index * (branches index).scalar) :=
        SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)

/-- The aggregate inverse scalar is the finite weighted sum of the retained branch scalars. -/
@[simp] theorem aggregateScaledInverse_scalar {count size : Nat}
    {matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size} (branches : Fin count →
      SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix)
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse branches weights).scalar =
      FiniteSum.Fin.sumFin fun index =>
        weights index * (branches index).scalar := rfl

/-- Pointwise rational inequalities are preserved by the finite indexed sum. -/
theorem coordinateSum_mono {count : Nat}
    (left right : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Coordinate)
    (entry_le : forall index, left index <= right index) :
    FiniteSum.Fin.sumFin left <=
      FiniteSum.Fin.sumFin right := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ,
        FiniteSum.Fin.sumFin_succ]
      exact add_le_add (entry_le 0)
        (inductionHypothesis (fun index => left index.succ)
          (fun index => right index.succ)
          (fun index => entry_le index.succ))

/-- A nonnegative finite rational sum is positive when one retained summand is positive. -/
theorem coordinateSum_positive_of_index {count : Nat}
    (values : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Coordinate) (selected : Fin count)
    (nonnegative : forall index, 0 <= values index)
    (positive : 0 < values selected) :
    0 < FiniteSum.Fin.sumFin values := by
  have selected_le_sum :
      values selected <= FiniteSum.Fin.sumFin values := by
    calc
      values selected =
          FiniteSum.Fin.sumFin (fun index =>
            if index = selected then values index else 0) :=
        (FiniteSum.Fin.sumFin_ite_eq selected values).symm
      _ <= FiniteSum.Fin.sumFin values :=
        SquareMatrix.Inverse.PivotedScaledInverse.coordinateSum_mono _ _ (fun index => by
          by_cases equal : index = selected
          · rw [if_pos equal]
          · rw [if_neg equal]
            exact nonnegative index)
  exact positive.trans_le selected_le_sum

/-- Taking the real part commutes with the finite Gaussian sum. -/
theorem sumFin_re {count : Nat} (values : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    (FiniteSum.Fin.sumFin values).re =
      FiniteSum.Fin.sumFin (fun index => (values index).re) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ,
        FiniteSum.Fin.sumFin_succ,
        Data.Gaussian.Basic.add_re,
        inductionHypothesis (fun index => values index.succ)]

/-- The real part of a conjugate product with itself is the Gaussian squared norm. -/
theorem conj_mul_self_re (value : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    (Data.Gaussian.Basic.conj value * value).re = Data.Gaussian.Norm.Basic.normSq value := by
  simp only [Data.Gaussian.Basic.conj, Data.Gaussian.Basic.mul_re, Data.Gaussian.Norm.Basic.normSq]
  ring1

/-- A successful finite pivot branch cannot be cancelled by the other
branches: conjugate weighting makes the aggregate scalar's real coordinate a
sum of squared norms. -/
theorem aggregateConjugate_scalar_nonzero_of_branch {count size : Nat}
    {matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size} (branches : Fin count →
      SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix)
    (selected : Fin count) (selectedNonzero : (branches selected).scalar ≠ 0) :
    (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse branches
      (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar ≠ 0 := by
  have realIdentity :
      (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse branches
        (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re =
        FiniteSum.Fin.sumFin fun index =>
          Data.Gaussian.Norm.Basic.normSq (branches index).scalar := by
    rw [SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse_scalar,
      SquareMatrix.Inverse.PivotedScaledInverse.sumFin_re]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    exact SquareMatrix.Inverse.PivotedScaledInverse.conj_mul_self_re (branches index).scalar
  have realPositive :
      0 < FiniteSum.Fin.sumFin fun index =>
        Data.Gaussian.Norm.Basic.normSq (branches index).scalar :=
    SquareMatrix.Inverse.PivotedScaledInverse.coordinateSum_positive_of_index _ selected
      (fun index => Data.Gaussian.Norm.Basic.normSq_nonneg (branches index).scalar)
      (Data.Gaussian.Norm.Basic.normSq_pos selectedNonzero)
  intro aggregateZero
  have zeroReal := congrArg Data.Gaussian.Basic.re aggregateZero
  change (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse branches
    (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re = 0 at zeroReal
  rw [realIdentity] at zeroReal
  change FiniteSum.Fin.sumFin
      (fun index => Data.Gaussian.Norm.Basic.normSq (branches index).scalar) = 0 at zeroReal
  rw [zeroReal]
    at realPositive
  exact lt_irrefl 0 realPositive

/-! ## Pivot-complete exact recursion -/

/-- One exact pivot branch, parameterized by the recursively computed scaled
inverse of its Schur matrix. -/
@[expose] def pivotBranch {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse
      (SquareMatrix.Schur.schur
        (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot))) :
          SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix :=
  let pivoted := SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot
  SquareMatrix.Inverse.PivotedScaledInverse.unpivotScaledInverse matrix rowPivot columnPivot
    (SquareMatrix.Inverse.Scaled.Block.extendScaledInverse pivoted smaller)

/-- All row/column pivot branches of the fraction-free recursion are retained.
Each finite aggregation uses conjugate scalar weights, so its new scalar is a
sum of Gaussian norm squares rather than a cancellation-prone sum. -/
@[expose] def completeScaledInverse : {size : Nat} ->
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) ->
      SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix
  | 0, matrix => SquareMatrix.Inverse.Scaled.Compute.scaledInverse matrix
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch matrix rowPivot columnPivot
          (Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.completeScaledInverse
            (SquareMatrix.Schur.schur
              (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse (branch rowPivot)
          (fun columnPivot => Data.Gaussian.Basic.conj (branch rowPivot columnPivot).scalar)
      SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse rowBranch
        (fun rowPivot => Data.Gaussian.Basic.conj (rowBranch rowPivot).scalar)

/-- Compute the exact scaled inverse branch for one retained row-column pivot.

The recursive inverse of that pivoted Schur complement is extended and transported back to the original matrix. -/
@[expose] def completeExactBranch {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix :=
  SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch matrix rowPivot columnPivot
    (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
      (SquareMatrix.Schur.schur
        (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot)))

/-- Aggregate all column-pivot branches for one retained row using conjugate scalar weights.

The result remains a scaled inverse of the same original matrix. -/
@[expose] def completeExactRow {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix :=
  SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse
    (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix rowPivot)
    (fun columnPivot =>
      Data.Gaussian.Basic.conj (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix rowPivot
        columnPivot).scalar)

/-- At positive dimension, the complete inverse is the conjugate-weighted aggregate of its row branches. -/
theorem completeScaledInverse_succ {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix =
      SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse
        (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow matrix)
        (fun rowPivot => Data.Gaussian.Basic.conj (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow
          matrix rowPivot).scalar) := rfl

/-- The complete inverse times its original matrix is its retained scalar identity. -/
theorem completeScaledInverse_left_identity {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) :
    SquareMatrix.Multiplication.mul
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).inverse matrix =
      SquareMatrix.Multiplication.scaleIdentity
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar :=
  (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).left_identity

/-- The original matrix times its complete inverse is its retained scalar identity. -/
theorem completeScaledInverse_right_identity {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) :
    SquareMatrix.Multiplication.mul matrix
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).inverse =
      SquareMatrix.Multiplication.scaleIdentity
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar :=
  (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).right_identity

/-- A Gaussian sum over one coordinate equals that coordinate. -/
private theorem sumFin_one (values : Fin 1 -> SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) :
    FiniteSum.Fin.sumFin values = values 0 := by
  rw [FiniteSum.Fin.sumFin_succ]
  change values 0 + 0 = values 0
  ring1

/-- The sole pivot branch in dimension one has scalar equal to the original matrix entry. -/
private theorem completeExactBranch_one_scalar (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square 1) :
    (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix 0 0).scalar = matrix 0 0 := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch
    SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch
  rw [SquareMatrix.Inverse.PivotedScaledInverse.unpivotScaledInverse_scalar]
  change SquareMatrix.Blocks.head (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix 0 0) * 1 =
    matrix 0 0
  unfold SquareMatrix.Blocks.head SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
  rw [SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply, SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero]
  ring1

/-- In dimension one the pivot-complete recursion has just one row and one
column branch.  Its two conjugate aggregations therefore expose the fourth
power construction explicitly. -/
theorem completeScaledInverse_one_scalar (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square 1) :
    (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar =
      Data.Gaussian.Basic.conj (Data.Gaussian.Basic.conj (matrix 0 0) * matrix 0 0) *
        (Data.Gaussian.Basic.conj (matrix 0 0) * matrix 0 0) := by
  rw [SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_succ,
    SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse_scalar,
    LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.sumFin_one]
  unfold SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow
  rw [SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse_scalar,
    LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.sumFin_one]
  rw [LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.completeExactBranch_one_scalar]

/-- Consequently the squared norm of the dimension-one canonical scalar is
the fourth power of the squared norm of the sole matrix entry. -/
theorem normSq_completeScaledInverse_one_scalar (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square 1) :
    Data.Gaussian.Norm.Basic.normSq (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
      matrix).scalar =
      Data.Gaussian.Norm.Basic.normSq (matrix 0 0) ^ 4 := by
  rw [SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_one_scalar]
  repeat' rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_conj]
  ring1

/-! ## Synchronized geometric recursion -/

/-- A Gaussian approximation with retained geometric movement and boundedness estimates. -/
abbrev GeometricApproximation :=
  Approximation.Gaussian.Geometric.GeometricApproximation
/-- A finite square matrix of Gaussian geometric approximations. -/
abbrev GeometricMatrix (size : Nat) :=
  Approximation.Matrix.GeometricMatrix size
/-- A retained approximate scalar and square inverse matrix of the supplied dimension. -/
abbrev ScaledInverseApproximation (size : Nat) :=
  Approximation.Matrix.ScaledInverseApproximation size

/-- Conjugation preserves a geometric sample stream and its retained estimates.

Every sample is conjugated at the same original index. The original movement
allowance and center bound remain unchanged because conjugation preserves
the squared Gaussian norm. -/
@[expose] def geometricConj (source : SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation) :
    SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation where
  sample := fun index => Data.Gaussian.Basic.conj (source.sample index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have difference :
        Data.Gaussian.Basic.conj (source.sample later) - Data.Gaussian.Basic.conj (source.sample
          earlier) =
          Data.Gaussian.Basic.conj (source.sample later - source.sample earlier) := by
      apply Data.Gaussian.Basic.ext
      · change (source.sample later).re - (source.sample earlier).re =
          (source.sample later - source.sample earlier).re
        rewrite [Data.Gaussian.Basic.sub_re]
        exact Eq.refl _
      · change -(source.sample later).im - -(source.sample earlier).im =
          -((source.sample later - source.sample earlier).im)
        rewrite [Data.Gaussian.Basic.sub_im]
        ring1
    rw [difference, Data.Gaussian.Norm.Basic.normSq_conj]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_conj]
    exact source.sample_bounded index

/-- Sampling geometric conjugation gives the conjugate of the original sample. -/
@[simp] theorem geometricConj_sample (source : SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation)
    (index : Nat) :
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricConj source).sample index = Data.Gaussian.Basic.conj
      (source.sample index) := rfl

/-- Exchange the leading row with the displayed row of a geometric matrix.

Each entry retains its original approximation program and certificates. -/
@[expose] def geometricSwapRows {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size +
  1))
    (pivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1) :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot row) column

/-- Exchange the leading column with the displayed column of a geometric matrix.

Each entry retains its original approximation program and certificates. -/
@[expose] def geometricSwapColumns {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1) :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix row (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot column)

/-- Read a row-swapped geometric matrix at its transposed original row index. -/
@[simp] theorem geometricSwapRows_apply {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapRows matrix pivot row column =
      matrix (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot row) column :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Read a column-swapped geometric matrix at its transposed original column index. -/
@[simp] theorem geometricSwapColumns_apply {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapColumns matrix pivot row column =
      matrix row (SquareMatrix.Inverse.PivotedScaledInverse.swapZero pivot column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Move the displayed geometric matrix entry to the leading row and column. -/
@[expose] def geometricPivotMatrix {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1) :=
  SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapColumns
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapRows matrix rowPivot) columnPivot

/-- Undo a geometric inverse pivot by exchanging the opposite row and column indices. -/
@[expose] def geometricUnpivotInverse {size : Nat}
    (inverse : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1) :=
  SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapColumns
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapRows inverse columnPivot) rowPivot

/-- Entrywise synchronized weighted sum. -/
@[expose] def geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation)
    (matrices : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size) :
      SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    Approximation.Gaussian.Geometric.GeometricApproximation.sum
      fun index =>
        Approximation.Gaussian.Geometric.GeometricApproximation.mul
          (weights index) (matrices index row column)

/-- Read one entry of the synchronized weighted matrix sum. -/
@[simp] theorem geometricWeightedMatrix_apply {count size : Nat}
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation)
    (matrices : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size)
    (row column : Fin size) :
    SquareMatrix.Inverse.PivotedScaledInverse.geometricWeightedMatrix weights matrices row column =
      Approximation.Gaussian.Geometric.GeometricApproximation.sum
        fun index =>
          Approximation.Gaussian.Geometric.GeometricApproximation.mul
            (weights index) (matrices index row column) :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Aggregate retained inverse approximations with the supplied synchronized weights.

The scalar and inverse entries use the same finite branch indices and weight programs. -/
@[expose] def geometricAggregate {count size : Nat}
    (branches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size)
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation) :
    SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size where
  scalar := Approximation.Gaussian.Geometric.GeometricApproximation.sum
    fun index =>
      Approximation.Gaussian.Geometric.GeometricApproximation.mul
        (weights index) (branches index).scalar
  inverse := SquareMatrix.Inverse.PivotedScaledInverse.geometricWeightedMatrix weights
    fun index => (branches index).inverse

/-- One synchronized pivot branch, parameterized by the recursively computed
Schur approximation. -/
@[expose] def geometricPivotBranch {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size) :
    SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation (size + 1) :=
  let pivoted := SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot
  { scalar :=
      Approximation.Gaussian.Geometric.GeometricApproximation.mul
        (pivoted 0 0) smaller.scalar
    inverse := SquareMatrix.Inverse.PivotedScaledInverse.geometricUnpivotInverse
      (Approximation.Matrix.blockInverse pivoted smaller)
        rowPivot columnPivot }

/-- The synchronized all-pivots recursion mirrors `completeScaledInverse`
exactly at every sample index. -/
@[expose] def completeApproximation : {size : Nat} ->
    SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size ->
      SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size
  | 0, _matrix =>
      { scalar :=
          Approximation.Gaussian.Geometric.GeometricApproximation.exact 1
        inverse := SquareMatrix.matrixOfFn fun row =>
          Fin.elim0 row }
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotBranch matrix rowPivot columnPivot
          (Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.completeApproximation
            (Approximation.Matrix.schur
              (SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate (branch rowPivot)
          (fun columnPivot =>
            SquareMatrix.Inverse.PivotedScaledInverse.geometricConj (branch rowPivot columnPivot).scalar)
      SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate rowBranch
        (fun rowPivot => SquareMatrix.Inverse.PivotedScaledInverse.geometricConj (rowBranch rowPivot).scalar)

/-- Any successful recursive row/column pivot proves the complete scalar
nonzero; all other branches can only add squared-norm contributions. -/
theorem completeScaledInverse_scalar_nonzero_of_branch {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (branchNonzero :
      (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0) :
    (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar ≠ 0 := by
  have rowNonzero : (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow matrix rowPivot).scalar ≠ 0 :=
    SquareMatrix.Inverse.PivotedScaledInverse.aggregateConjugate_scalar_nonzero_of_branch
      (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix rowPivot) columnPivot branchNonzero
  rw [SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_succ]
  exact SquareMatrix.Inverse.PivotedScaledInverse.aggregateConjugate_scalar_nonzero_of_branch
    (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow matrix) rowPivot rowNonzero

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse in
/-- The pivot-complete fraction-free construction is complete for finite
Gaussian matrices: a trivial displayed left kernel constructively produces a
nonzero canonical scalar.  The proof searches the bounded entry table for a
pivot, descends to its Schur matrix, and retains that successful branch in the
conjugate-weighted aggregate. -/
theorem completeScaledInverse_scalar_nonzero_of_leftKernelTrivial :
    {size : Nat} -> (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size) ->
      SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial matrix ->
      (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse matrix).scalar ≠ 0
  | 0, matrix, _trivial => by
      change (1 : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) ≠ 0
      decide
  | size + 1, matrix, trivial => by
      rcases exists_nonzero_entry_of_leftKernelTrivial matrix trivial with
        ⟨rowPivot, columnPivot, pivotNonzero⟩
      let pivoted := SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix matrix rowPivot columnPivot
      have pivotedTrivial : SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial pivoted := by
        simpa only [pivoted] using
          SquareMatrix.Inverse.PivotedScaledInverse.leftKernelTrivial_pivotMatrix trivial rowPivot columnPivot
      have headNonzero : SquareMatrix.Blocks.head pivoted ≠ 0 := by
        simpa only [pivoted, SquareMatrix.Blocks.head,
          SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix,
            SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply,
            SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply,
            SquareMatrix.Inverse.PivotedScaledInverse.swapZero_zero] using
          pivotNonzero
      have smallerTrivial : SquareMatrix.Inverse.PivotedScaledInverse.LeftKernelTrivial
          (SquareMatrix.Schur.schur pivoted) :=
        SquareMatrix.Inverse.PivotedScaledInverse.leftKernelTrivial_schur_of_head_nonzero pivoted pivotedTrivial
          headNonzero
      have smallerNonzero :
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            (SquareMatrix.Schur.schur pivoted)).scalar ≠ 0 :=

          completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
          (SquareMatrix.Schur.schur pivoted) smallerTrivial
      have branchNonzero :
          (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0 := by
        change SquareMatrix.Blocks.head pivoted *
            (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
              (SquareMatrix.Schur.schur pivoted)).scalar ≠ 0
        exact Data.Gaussian.Field.mul_ne_zero_direct
          headNonzero smallerNonzero
      exact SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_scalar_nonzero_of_branch matrix rowPivot
        columnPivot branchNonzero

/-- The smallest matrix rejected by the fixed-pivot recursion is accepted by
the complete construction.  This executable regression is the row-swap
matrix `[[0,1],[1,0]]`. -/
@[expose] def twoByTwoSwap : SquareMatrix.Inverse.PivotedScaledInverse.Square 2 :=
  SquareMatrix.Inverse.PivotedScaledInverse.swapRows (SquareMatrix.Multiplication.identity :
    SquareMatrix.Inverse.PivotedScaledInverse.Square 2) 1

/-- The fixed-pivot scaled inverse has zero scalar on the two-coordinate swap matrix. -/
theorem twoByTwoSwap_fixedScalar_zero :
    (SquareMatrix.Inverse.Scaled.Compute.scaledInverse SquareMatrix.Inverse.PivotedScaledInverse.twoByTwoSwap).scalar =
      0 := by
  decide

/-- The complete pivot construction has nonzero scalar on the two-coordinate swap matrix. -/
theorem twoByTwoSwap_completeScalar_nonzero :
    (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
      SquareMatrix.Inverse.PivotedScaledInverse.twoByTwoSwap).scalar ≠ 0 := by decide

/-- Compute one synchronized row-column pivot branch and its recursive Schur approximation.

The retained pivot indices determine the transport back to the original matrix coordinates. -/
@[expose] def completeGeometricBranch {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation (size + 1) :=
  SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotBranch matrix rowPivot columnPivot
    (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation
      (Approximation.Matrix.schur
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot)))

/-- Aggregate the synchronized column branches for one retained row with conjugate scalar weights. -/
@[expose] def completeGeometricRow {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot : Fin (size + 1)) : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation (size + 1) :=
  SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate
    (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot)
    (fun columnPivot =>
      SquareMatrix.Inverse.PivotedScaledInverse.geometricConj
        (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot columnPivot).scalar)

/-- At positive dimension, the complete approximation aggregates its synchronized row branches. -/
theorem completeApproximation_succ {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation matrix =
      SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate
        (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix)
        (fun rowPivot =>
          SquareMatrix.Inverse.PivotedScaledInverse.geometricConj
            (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix rowPivot).scalar) := rfl

/-- Sampling commutes with the displayed geometric row transposition.

Every finite entry uses the same original sample index and transposed row.
Scalar readback therefore identifies the two structural matrices. -/
@[simp] theorem sampleMatrix_geometricSwapRows {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapRows matrix pivot) index =
      SquareMatrix.Inverse.PivotedScaledInverse.swapRows
        (Approximation.Matrix.sampleMatrix matrix index)
          pivot := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapRows_apply,
      SquareMatrix.Inverse.PivotedScaledInverse.swapRows_apply, Approximation.Matrix.sampleMatrix_apply]
  exact Eq.refl _

/-- Sampling commutes with the displayed geometric column transposition.

Every finite entry uses the same original sample index and transposed column.
Scalar readback therefore identifies the two structural matrices. -/
@[simp] theorem sampleMatrix_geometricSwapColumns {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapColumns matrix pivot) index =
      SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
        (Approximation.Matrix.sampleMatrix matrix index)
          pivot := by
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.geometricSwapColumns_apply,
      SquareMatrix.Inverse.PivotedScaledInverse.swapColumns_apply, Approximation.Matrix.sampleMatrix_apply]
  exact Eq.refl _

/-- Sampling the geometric pivot matrix gives the same pivot of the sampled matrix. -/
@[simp] theorem sampleMatrix_geometricPivotMatrix {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot) index =
      SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
        (Approximation.Matrix.sampleMatrix matrix index)
          rowPivot columnPivot := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix
    SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
  rw [SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricSwapColumns,
    SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricSwapRows]

/-- Sampling commutes with the row-column transport that undoes the inverse pivot. -/
@[simp] theorem sampleMatrix_geometricUnpivotInverse {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricUnpivotInverse matrix rowPivot columnPivot) index =
      SquareMatrix.Inverse.PivotedScaledInverse.swapColumns
        (SquareMatrix.Inverse.PivotedScaledInverse.swapRows
          (Approximation.Matrix.sampleMatrix matrix index)
            columnPivot) rowPivot := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.geometricUnpivotInverse
  rw [SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricSwapColumns,
    SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricSwapRows]

/-- Sampling a synchronized weighted matrix sum gives the weighted sum of its samples. -/
@[simp] theorem sampleMatrix_geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation)
    (matrices : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricWeightedMatrix weights matrices) index =
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          Approximation.Matrix.sampleMatrix
            (matrices branch) index) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [Approximation.Matrix.sampleMatrix_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.geometricWeightedMatrix_apply,
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply,
    Approximation.Gaussian.Geometric.GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro branch
  rw [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample,
    Approximation.Matrix.sampleMatrix_apply]

/-- Read the aggregate scalar sample as the weighted sum of branch scalar samples. -/
@[simp] theorem geometricAggregate_scalar_sample {count size : Nat}
    (branches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size)
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation) (index : Nat) :
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate branches weights).scalar.sample index =
      FiniteSum.Fin.sumFin fun branch =>
        (weights branch).sample index * (branches branch).scalar.sample index := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate
  rw [Approximation.Gaussian.Geometric.GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro branch
  rw [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample]

/-- Read the aggregate inverse sample as the weighted sum of branch inverse samples. -/
@[simp] theorem geometricAggregate_inverse_sample {count size : Nat}
    (branches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size)
    (weights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate branches weights).inverse index =
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          Approximation.Matrix.sampleMatrix
            (branches branch).inverse index) := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate
  exact SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricWeightedMatrix weights
    (fun branch => (branches branch).inverse) index

/-- Retain exact scalar and inverse sample agreement through finite weighted aggregation.

All branch and weight equalities refer to the same supplied sample index. -/
theorem geometricAggregate_sample {count size : Nat}
    {matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square size}
    (geometricBranches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size)
    (exactBranches : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse matrix)
    (geometricWeights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.GeometricApproximation)
    (exactWeights : Fin count → SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (index : Nat)
    (scalarSamples : forall branch,
      (geometricBranches branch).scalar.sample index =
        (exactBranches branch).scalar)
    (inverseSamples : forall branch,
      Approximation.Matrix.sampleMatrix
          (geometricBranches branch).inverse index =
        (exactBranches branch).inverse)
    (weightSamples : forall branch,
      (geometricWeights branch).sample index = exactWeights branch) :
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate geometricBranches geometricWeights).scalar.sample
      index =
        (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse exactBranches exactWeights).scalar ∧
      Approximation.Matrix.sampleMatrix
          (SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate geometricBranches geometricWeights).inverse
            index =
        (SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse exactBranches exactWeights).inverse := by
  constructor
  · rw [SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate_scalar_sample,
      SquareMatrix.Inverse.PivotedScaledInverse.aggregateScaledInverse_scalar]
    apply FiniteSum.Fin.sumFin_congr
    intro branch
    rw [weightSamples branch, scalarSamples branch]
  · rw [SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate_inverse_sample]
    apply SquareMatrix.matrix_ext
    intro row column
    change
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix
          (fun branch => (geometricWeights branch).sample index)
          (fun branch =>
            Approximation.Matrix.sampleMatrix
              (geometricBranches branch).inverse index) row column =
        SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix exactWeights
          (fun branch => (exactBranches branch).inverse) row column
    rw [SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply,
      SquareMatrix.Inverse.PivotedScaledInverse.weightedMatrix_apply]
    apply FiniteSum.Fin.sumFin_congr
    intro branch
    rw [weightSamples branch]
    have entrySample := SquareMatrix.matrix_eq_at
      (inverseSamples branch) row column
    rw [entrySample]

/-! The raw block formula is separated from its identity proofs so sampling
can be checked entrywise without transporting a dependent proof object across
matrix extensional equality. -/

/-- Compute the fraction-free block inverse from its scalar and smaller matrix.

The original pivot, row, column and two product caches determine the corner
and edge entries. Owned finite dispatch selects those same cached values or
the original squared-pivot multiple of a trailing entry. -/
@[expose] def rawBlockInverse {size : Nat} (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (scalar : SquareMatrix.Inverse.PivotedScaledInverse.Gaussian) (inverse :
      SquareMatrix.Inverse.PivotedScaledInverse.Square size) : SquareMatrix.Inverse.PivotedScaledInverse.Square (size +
      1) :=
  let a := SquareMatrix.Blocks.head matrix
  let row := SquareMatrix.Blocks.topRow matrix
  let column := SquareMatrix.Blocks.leftColumn matrix
  let inverseColumn :=
    SquareMatrix.Multiplication.matrixVector inverse column
  let rowInverse := SquareMatrix.Multiplication.vectorMatrix row inverse
  let corner := scalar +
    Dot.dot row inverseColumn
  SquareMatrix.matrixOfFn fun i j => Data.Fin.cases
    (Data.Fin.cases corner (fun columnIndex => -a * rowInverse columnIndex) j)
    (fun rowIndex => Data.Fin.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => (a * a) * inverse rowIndex columnIndex) j) i

/-- Read a raw block-inverse entry at its original finite coordinates.

The leading corner, two edge products and trailing scaled entry use the
original scalar, inverse and cached row-column products of the construction. -/
@[simp] theorem rawBlockInverse_apply {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (scalar :
      SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)
    (inverse : SquareMatrix.Inverse.PivotedScaledInverse.Square size) (row column : Fin (size + 1)) :
    SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse matrix scalar inverse row column =
      Data.Fin.cases
        (Data.Fin.cases
          (scalar + Dot.dot
            (SquareMatrix.Blocks.topRow matrix)
            (SquareMatrix.Multiplication.matrixVector inverse
              (SquareMatrix.Blocks.leftColumn matrix)))
          (fun columnIndex =>
            -SquareMatrix.Blocks.head matrix *
              SquareMatrix.Multiplication.vectorMatrix
                (SquareMatrix.Blocks.topRow matrix) inverse
                  columnIndex) column)
        (fun rowIndex => Data.Fin.cases
          (-SquareMatrix.Blocks.head matrix *
            SquareMatrix.Multiplication.matrixVector inverse
              (SquareMatrix.Blocks.leftColumn matrix) rowIndex)
          (fun columnIndex =>
            (SquareMatrix.Blocks.head matrix *
              SquareMatrix.Blocks.head matrix) *
                inverse rowIndex columnIndex) column) row := by
  unfold SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse
  rewrite [SquareMatrix.matrixOfFn_apply]
  exact Eq.refl _

/-- The raw block formula equals the certified block inverse for its retained data.

The original scalar and inverse are read at the same finite block coordinates.
Direct finite case analysis compares the leading corner, edges and trailing
block without changing either executable construction. -/
@[simp] theorem rawBlockInverse_eq_blockInverse {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1))
    (smaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse (SquareMatrix.Schur.schur matrix)) :
    SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse matrix smaller.scalar smaller.inverse =
      SquareMatrix.Inverse.Scaled.Block.blockInverse matrix smaller := by
  apply SquareMatrix.matrix_ext
  intro row column
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_apply,
        SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
        Data.Fin.cases_zero, Data.Fin.cases_zero]
      exact Eq.refl _
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_apply,
        SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
        Data.Fin.cases_zero, Data.Fin.cases_succ]
      exact Eq.refl _
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_apply,
        SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
        Data.Fin.cases_succ, Data.Fin.cases_zero,
        Data.Fin.cases_succ, Data.Fin.cases_zero]
      exact Eq.refl _
    · rewrite [SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_apply,
        SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
        Data.Fin.cases_succ, Data.Fin.cases_succ,
        Data.Fin.cases_succ, Data.Fin.cases_succ]
      rewrite [pow_two]
      exact Eq.refl _

/-- Sampling the geometric block formula gives the raw exact block formula.

The original matrix, scalar and smaller inverse agree with their exact counterparts at the same supplied sample index.
-/
theorem geometricBlockInverse_sample {size : Nat}
    (geometricMatrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (smaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size) (index : Nat)
    (exactMatrix : SquareMatrix.Inverse.PivotedScaledInverse.Square (size + 1)) (exactScalar :
      SquareMatrix.Inverse.PivotedScaledInverse.Gaussian)
    (exactInverse : SquareMatrix.Inverse.PivotedScaledInverse.Square size)
    (matrixSample :
      Approximation.Matrix.sampleMatrix geometricMatrix index =
        exactMatrix)
    (scalarSample : smaller.scalar.sample index = exactScalar)
    (inverseSample :
      Approximation.Matrix.sampleMatrix smaller.inverse index =
        exactInverse) :
    Approximation.Matrix.sampleMatrix
        (Approximation.Matrix.blockInverse
          geometricMatrix smaller) index =
      SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse exactMatrix exactScalar exactInverse := by
  have rowSample :
      Approximation.Matrix.sampleVector
          (fun entry : Fin size => geometricMatrix 0 entry.succ) index =
        SquareMatrix.Blocks.topRow exactMatrix := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      SquareMatrix.Blocks.topRow_apply]
    have sampledEntry := SquareMatrix.matrix_eq_at
      matrixSample 0 entry.succ
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  have columnSample :
      Approximation.Matrix.sampleVector
          (fun entry : Fin size => geometricMatrix entry.succ 0) index =
        SquareMatrix.Blocks.leftColumn exactMatrix := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      SquareMatrix.Blocks.leftColumn_apply]
    have sampledEntry := SquareMatrix.matrix_eq_at
      matrixSample entry.succ 0
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  have inverseColumnSample :
      Approximation.Matrix.sampleVector
          (Approximation.Matrix.matrixVector smaller.inverse
            (fun entry : Fin size => geometricMatrix entry.succ 0)) index =
        SquareMatrix.Multiplication.matrixVector exactInverse
          (SquareMatrix.Blocks.leftColumn exactMatrix) := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      Approximation.Matrix.matrixVector_sample,
      inverseSample, columnSample]
  have rowInverseSample :
      Approximation.Matrix.sampleVector
          (Approximation.Matrix.vectorMatrix
            (fun entry : Fin size => geometricMatrix 0 entry.succ)
              smaller.inverse) index =
        SquareMatrix.Multiplication.vectorMatrix
          (SquareMatrix.Blocks.topRow exactMatrix)
            exactInverse := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      Approximation.Matrix.vectorMatrix_sample,
      inverseSample, rowSample]
  have headSample : (geometricMatrix 0 0).sample index =
      SquareMatrix.Blocks.head exactMatrix := by
    have sampledEntry := SquareMatrix.matrix_eq_at
      matrixSample 0 0
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  apply SquareMatrix.matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    Approximation.Matrix.blockInverse_apply,
    SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_apply]
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [Data.Fin.cases_zero, Data.Fin.cases_zero,
        Data.Fin.cases_zero, Data.Fin.cases_zero]
      rewrite [Approximation.Gaussian.Geometric.GeometricApproximation.add_sample,
        scalarSample, Approximation.Matrix.dot_sample, rowSample, inverseColumnSample]
      exact Eq.refl _
    · rewrite [Data.Fin.cases_zero, Data.Fin.cases_succ,
        Data.Fin.cases_zero, Data.Fin.cases_succ]
      rewrite [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample,
        Approximation.Gaussian.Geometric.GeometricApproximation.neg_sample, headSample]
      have entrySample := Data.Vector.Basic.vector_eq_at rowInverseSample columnIndex
      rewrite [Approximation.Matrix.sampleVector_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [Data.Fin.cases_succ, Data.Fin.cases_zero,
        Data.Fin.cases_succ, Data.Fin.cases_zero]
      rewrite [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample,
        Approximation.Gaussian.Geometric.GeometricApproximation.neg_sample, headSample]
      have entrySample := Data.Vector.Basic.vector_eq_at inverseColumnSample rowIndex
      rewrite [Approximation.Matrix.sampleVector_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _
    · rewrite [Data.Fin.cases_succ, Data.Fin.cases_succ,
        Data.Fin.cases_succ, Data.Fin.cases_succ]
      rewrite [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample,
        Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample, headSample]
      have entrySample := SquareMatrix.matrix_eq_at inverseSample rowIndex columnIndex
      rewrite [Approximation.Matrix.sampleMatrix_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _

/-- A synchronized pivot branch retains exact scalar and inverse sample agreement.

The smaller approximate and certified inverses are compared at the same sample index and original pivot coordinates. -/
theorem geometricPivotBranch_sample {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat)
    (smaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverseApproximation size)
    (exactSmaller : SquareMatrix.Inverse.PivotedScaledInverse.ScaledInverse
      (SquareMatrix.Schur.schur
        (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot)))
    (scalarSample : smaller.scalar.sample index = exactSmaller.scalar)
    (inverseSample :
      Approximation.Matrix.sampleMatrix smaller.inverse index =
        exactSmaller.inverse) :
    (SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotBranch matrix rowPivot columnPivot smaller).scalar.sample
          index =
        (SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).scalar ∧
      Approximation.Matrix.sampleMatrix
          (SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotBranch matrix rowPivot columnPivot smaller).inverse
            index =
        (SquareMatrix.Inverse.PivotedScaledInverse.pivotBranch
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).inverse := by
  let geometricPivot := SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot
  let exactMatrix :=
    Approximation.Matrix.sampleMatrix matrix index
  let exactPivot := SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix exactMatrix rowPivot columnPivot
  have pivotSample :
      Approximation.Matrix.sampleMatrix geometricPivot index =
        exactPivot :=
    SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricPivotMatrix matrix rowPivot columnPivot index
  have extendedInverseSample :
      Approximation.Matrix.sampleMatrix
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) index =
        (SquareMatrix.Inverse.Scaled.Block.extendScaledInverse
          exactPivot exactSmaller).inverse := by
    calc
      Approximation.Matrix.sampleMatrix
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) index =
          SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse exactPivot exactSmaller.scalar
            exactSmaller.inverse :=
        SquareMatrix.Inverse.PivotedScaledInverse.geometricBlockInverse_sample geometricPivot smaller index exactPivot
          exactSmaller.scalar exactSmaller.inverse pivotSample scalarSample
            inverseSample
      _ = (SquareMatrix.Inverse.Scaled.Block.extendScaledInverse
            exactPivot exactSmaller).inverse :=
        SquareMatrix.Inverse.PivotedScaledInverse.rawBlockInverse_eq_blockInverse exactPivot exactSmaller
  constructor
  · change
      (Approximation.Gaussian.Geometric.GeometricApproximation.mul
        (geometricPivot 0 0) smaller.scalar).sample index =
        (SquareMatrix.Inverse.Scaled.Block.extendScaledInverse
          exactPivot exactSmaller).scalar
    rw [Approximation.Gaussian.Geometric.GeometricApproximation.mul_sample]
    have pivotEntry := SquareMatrix.matrix_eq_at
      pivotSample 0 0
    rw [Approximation.Matrix.sampleMatrix_apply]
      at pivotEntry
    rw [pivotEntry, scalarSample]
    rfl
  · change
      Approximation.Matrix.sampleMatrix
        (SquareMatrix.Inverse.PivotedScaledInverse.geometricUnpivotInverse
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) rowPivot columnPivot) index = _
    rw [SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricUnpivotInverse, extendedInverseSample]
    rfl

/-- Every synchronized finite sample is exactly the pivot-complete scaled
inverse of the source matrix at that same sample index. -/
theorem completeApproximation_sample : forall {size : Nat}
    (matrix : SquareMatrix.Inverse.PivotedScaledInverse.GeometricMatrix size) (index : Nat),
    (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation matrix).scalar.sample index =
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
          (Approximation.Matrix.sampleMatrix matrix index)).scalar ∧
      Approximation.Matrix.sampleMatrix
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation matrix).inverse index =
        (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
          (Approximation.Matrix.sampleMatrix matrix index)).inverse
  | 0, _matrix, _index => by
      constructor
      · rfl
      · rfl
  | size + 1, matrix, index => by
      let exactMatrix :=
        Approximation.Matrix.sampleMatrix matrix index
      have branchSample : forall rowPivot columnPivot,
          (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot columnPivot).scalar.sample
                index =
              (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch exactMatrix rowPivot columnPivot).scalar ∧
            Approximation.Matrix.sampleMatrix
                (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot columnPivot).inverse
                  index =
              (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch exactMatrix rowPivot columnPivot).inverse
                := by
        intro rowPivot columnPivot
        let geometricPivot :=
          SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotMatrix matrix rowPivot columnPivot
        have recursive :=
          Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse.completeApproximation_sample
          (Approximation.Matrix.schur geometricPivot) index
        have pivotSample := SquareMatrix.Inverse.PivotedScaledInverse.sampleMatrix_geometricPivotMatrix matrix
          rowPivot columnPivot index
        rw [Approximation.Matrix.sampleMatrix_schur,
          pivotSample] at recursive
        exact SquareMatrix.Inverse.PivotedScaledInverse.geometricPivotBranch_sample matrix rowPivot columnPivot index
          (SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation
            (Approximation.Matrix.schur geometricPivot))
          (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
            (SquareMatrix.Schur.schur
              (SquareMatrix.Inverse.PivotedScaledInverse.pivotMatrix exactMatrix rowPivot columnPivot)))
          recursive.1 recursive.2
      have rowSample : forall rowPivot,
          (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix rowPivot).scalar.sample index =
                (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow exactMatrix rowPivot).scalar ∧
            Approximation.Matrix.sampleMatrix
                (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix rowPivot).inverse index =
              (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow exactMatrix rowPivot).inverse := by
        intro rowPivot
        apply SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate_sample
          (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot)
          (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch exactMatrix rowPivot)
          (fun columnPivot => SquareMatrix.Inverse.PivotedScaledInverse.geometricConj
            (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricBranch matrix rowPivot columnPivot).scalar)
          (fun columnPivot => Data.Gaussian.Basic.conj
            (SquareMatrix.Inverse.PivotedScaledInverse.completeExactBranch exactMatrix rowPivot columnPivot).scalar)
          index
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).1
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).2
        · intro columnPivot
          rw [SquareMatrix.Inverse.PivotedScaledInverse.geometricConj_sample,
            (branchSample rowPivot columnPivot).1]
      rw [SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_succ matrix,
        SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse_succ exactMatrix]
      exact SquareMatrix.Inverse.PivotedScaledInverse.geometricAggregate_sample
        (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix)
          (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow exactMatrix)
        (fun rowPivot =>
          SquareMatrix.Inverse.PivotedScaledInverse.geometricConj
            (SquareMatrix.Inverse.PivotedScaledInverse.completeGeometricRow matrix rowPivot).scalar)
        (fun rowPivot => Data.Gaussian.Basic.conj (SquareMatrix.Inverse.PivotedScaledInverse.completeExactRow
          exactMatrix rowPivot).scalar)
        index
        (fun rowPivot => (rowSample rowPivot).1)
        (fun rowPivot => (rowSample rowPivot).2)
        (fun rowPivot => by
          rw [SquareMatrix.Inverse.PivotedScaledInverse.geometricConj_sample, (rowSample rowPivot).1])

end

end Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
