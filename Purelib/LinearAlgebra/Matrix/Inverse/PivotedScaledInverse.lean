module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.LinearAlgebra.Matrix.Permutation
import Purelib.LinearAlgebra.Matrix.Pivot
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

open Purelib.Approximation.Gaussian.Geometric
open Purelib.Data.Gaussian.Norm

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
open Purelib.Data.Fin (swapZero swapZero_zero swapZero_pivot swapZero_of_ne
  swapZero_involutive swapZero_injective sumFin_swapZero)
open Purelib.LinearAlgebra.Matrix.Permutation
  (swapRows swapColumns swapRows_apply swapColumns_apply swapRows_involutive swapColumns_involutive
    mul_swapColumns_swapRows mul_swapColumns_left mul_swapRows_right mul_swapColumns_right mul_swapRows_left
    swapRows_swapColumns_scaleIdentity swapColumns_swapRows_scaleIdentity pivotMatrix)

public section

/-- The exact rational coordinate type. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A finite square structural matrix of Gaussian rationals. -/
abbrev Square (size : Nat) :=
  SquareMatrix Gaussian size
/-- A scaled inverse certificate for the retained Gaussian square matrix. -/
abbrev ScaledInverse {size : Nat} (matrix : Square size) :=
  Scaled.Basic.ScaledInverse matrix

open Purelib.Data.Gaussian.Basic.Canonical

/-! ## Constructive left-kernel completeness -/

/-- A finite square matrix has trivial displayed left kernel.  This
formulation is deliberately pointwise: both the vector and every vanishing
column are finite structural data. -/
@[expose] def LeftKernelTrivial {size : Nat} (matrix : Square size) : Prop :=
  forall vector : Data.Vector Gaussian size,
    (forall column,
      Multiplication.vectorMatrix vector matrix column = 0) ->
      forall row, vector row = 0

/-- Moving a displayed matrix entry to the upper-left corner preserves
triviality of the finite left kernel. -/
theorem leftKernelTrivial_pivotMatrix {size : Nat}
    {matrix : Square (size + 1)} (trivial :
      LeftKernelTrivial matrix)
    (rowPivot columnPivot : Fin (size + 1)) :
    LeftKernelTrivial (pivotMatrix
      matrix rowPivot columnPivot) := by
  intro vector kernel row
  let unpivoted := Data.Vector.Basic.vectorOfFn fun index =>
    vector (swapZero rowPivot index)
  have unpivotedKernel : forall column,
      Multiplication.vectorMatrix unpivoted matrix column = 0 := by
    intro column
    have pivotKernel := kernel (swapZero columnPivot column)
    rw [Multiplication.vectorMatrix_apply] at pivotKernel
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun index => vector index *
        matrix (swapZero rowPivot index) column)
      (fun index => by
        unfold pivotMatrix
        rw [swapColumns_apply,
          swapRows_apply,
          swapZero_involutive])]
      at pivotKernel
    rw [Multiplication.vectorMatrix_apply]
    have sumZero : FiniteSum.Fin.sumFin
        (fun index => vector (swapZero rowPivot index) * matrix index column)
          =
          0 := by
      calc
      FiniteSum.Fin.sumFin
          (fun index => vector (swapZero rowPivot index) * matrix index
            column) =
          FiniteSum.Fin.sumFin
            (fun index =>
              (fun source => vector source *
                matrix (swapZero rowPivot source) column)
                  (swapZero rowPivot index)) := by
            apply FiniteSum.Fin.sumFin_congr
            intro index
            change vector (swapZero rowPivot index) * matrix index column =
              vector (swapZero rowPivot index) *
                matrix (swapZero rowPivot
                  (swapZero rowPivot index)) column
            rw [swapZero_involutive]
      _ = FiniteSum.Fin.sumFin
            (fun index => vector index *
              matrix (swapZero rowPivot index) column) :=
          by
            let values := fun source => vector source *
              matrix (swapZero rowPivot source) column
            change FiniteSum.Fin.sumFin (fun index =>
                values (swapZero rowPivot index)) =
              FiniteSum.Fin.sumFin values
            exact sumFin_swapZero rowPivot values
      _ = 0 := pivotKernel
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun index =>
        vector (swapZero rowPivot index) * matrix index column)
      (fun index => by
        rw [show unpivoted index = vector (swapZero rowPivot index) by
          unfold unpivoted
          exact Data.Vector.Basic.vectorOfFn_apply _ _])]
    exact sumZero
  have zero := trivial unpivoted unpivotedKernel (swapZero rowPivot row)
  rw [show unpivoted (swapZero rowPivot row) =
      vector (swapZero rowPivot
        (swapZero rowPivot row)) by
        exact Data.Vector.Basic.vectorOfFn_apply _ _] at zero
  rw [swapZero_involutive]
    at zero
  exact zero

/-- A nonempty matrix with trivial left kernel contains a displayed nonzero
entry.  The witness is found by explicit structural search over its two
finite index dimensions. -/
theorem exists_nonzero_entry_of_leftKernelTrivial {size : Nat}
    (matrix : Square (size + 1)) (trivial :
      LeftKernelTrivial matrix) :
    exists row column, matrix row column ≠ 0 := by
  cases SquareMatrix.Pivot.scan (fun row column => matrix row column) with
  | found row column nonzero => exact ⟨row, column, nonzero⟩
  | zero allZero =>
    let selected := Data.Vector.Basic.vectorOfFn fun row =>
      if row = (0 : Fin (size + 1)) then (1 : Gaussian) else 0
    have selectedKernel : forall column,
        Multiplication.vectorMatrix selected matrix column = 0 := by
      intro column
      rw [Multiplication.vectorMatrix_apply]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun _ => (0 : Gaussian)) (fun row => by
          rw [allZero row column, Data.Gaussian.Basic.mul_zero])]
      exact FiniteSum.Fin.sumFin_zero
    have selectedZero := trivial selected selectedKernel 0
    change (if (0 : Fin (size + 1)) = 0 then (1 : Gaussian) else 0) = 0
      at selectedZero
    exact (one_ne_zero selectedZero).elim

/-- Triviality of the left kernel descends to the Schur matrix at a nonzero pivot.

The retained tail vector is lifted with its original column pairing. Its
finite product vanishes by the Schur identity, and the original nonzero head
then forces every original tail coordinate to vanish. -/
theorem leftKernelTrivial_schur_of_head_nonzero {size : Nat}
    (matrix : Square (size + 1)) (trivial :
      LeftKernelTrivial matrix)
    (headNonzero : Blocks.head matrix ≠ 0) :
    LeftKernelTrivial (Schur.schur matrix) := by
  intro vector kernel row
  let columnPairing := Dot.dot vector
    (Blocks.leftColumn matrix)
  let lifted : Data.Vector Gaussian (size + 1) :=
    Data.Vector.Basic.vectorOfFn fun index =>
      Data.Fin.cases (-columnPairing)
        (fun tail => Blocks.head matrix * vector tail) index
  have lifted_zero : lifted 0 = -columnPairing := by
    unfold lifted
    rewrite [Data.Vector.Basic.vectorOfFn_apply]
    change Data.Fin.cases (-columnPairing)
      (fun tail => Blocks.head matrix * vector tail)
      (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = -columnPairing
    exact Data.Fin.cases_zero _ _
  have lifted_succ (index : Fin size) :
      lifted index.succ =
        Blocks.head matrix * vector index := by
    unfold lifted
    rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.cases_succ]
    exact Eq.refl _
  have liftedKernel : forall column,
      Multiplication.vectorMatrix lifted matrix column = 0 := by
    intro column
    refine Data.Fin.cases_induction ?_ (fun tailColumn => ?_) column
    · change Multiplication.vectorMatrix lifted matrix
        (0 : Fin (size + 1)) = 0
      rw [Multiplication.vectorMatrix_apply,
        FiniteSum.Fin.sumFin_succ]
      rw [lifted_zero]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun index => Blocks.head matrix *
          vector index * matrix index.succ 0)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 0 +
            FiniteSum.Fin.sumFin (fun index =>
              matrix 0 0 * vector index * matrix index.succ 0) =
            -columnPairing * Blocks.head matrix +
              FiniteSum.Fin.sumFin (fun index =>
                Blocks.head matrix * vector index *
                  Blocks.leftColumn matrix index) := by
          change -columnPairing * Blocks.head matrix +
              FiniteSum.Fin.sumFin (fun index =>
                Blocks.head matrix * vector index *
                  matrix index.succ 0) = _
          apply congrArg (fun total : Gaussian =>
            -columnPairing * Blocks.head matrix + total)
          apply FiniteSum.Fin.sumFin_congr
          intro index
          rw [Blocks.leftColumn_apply]
        _ = 0 := by
          rw [FiniteSum.Fin.sumFin_congr
            (right := fun index => Blocks.head matrix *
              (vector index *
                Blocks.leftColumn matrix index))
            (fun _ => by ring1)]
          rw [FiniteSum.Fin.sumFin_mul_left]
          unfold columnPairing Dot.dot
          ring1
    · rw [Multiplication.vectorMatrix_apply,
        FiniteSum.Fin.sumFin_succ]
      rw [lifted_zero]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun index => Blocks.head matrix *
          vector index * matrix index.succ tailColumn.succ)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 tailColumn.succ +
            FiniteSum.Fin.sumFin (fun index =>
              Blocks.head matrix * vector index *
                matrix index.succ tailColumn.succ) =
            -columnPairing *
                Blocks.topRow matrix tailColumn +
              FiniteSum.Fin.sumFin (fun index =>
                Blocks.head matrix * vector index *
                  Blocks.tail matrix index
                    tailColumn) := by
          rw [show matrix 0 tailColumn.succ =
              Blocks.topRow matrix tailColumn by
            exact (Blocks.topRow_apply
              matrix tailColumn).symm]
          apply congrArg (fun total : Gaussian =>
            -columnPairing *
              Blocks.topRow matrix tailColumn + total)
          apply FiniteSum.Fin.sumFin_congr
          intro index
          rw [Blocks.tail_apply]
        _ = Blocks.head matrix *
                Multiplication.vectorMatrix vector
                  (Blocks.tail matrix) tailColumn -
              Dot.dot vector
                  (Blocks.leftColumn matrix) *
                Blocks.topRow matrix tailColumn := by
          rw [Multiplication.vectorMatrix_apply]
          rw [FiniteSum.Fin.sumFin_congr
            (right := fun index =>
              Blocks.head matrix *
                (vector index *
                  Blocks.tail matrix index tailColumn))
            (fun _ => by ring1)]
          rw [FiniteSum.Fin.sumFin_mul_left]
          unfold columnPairing
          ring1
        _ = Multiplication.vectorMatrix vector
              (Schur.schur matrix) tailColumn := by
          exact (Schur.vectorMatrix_schur
            vector matrix tailColumn).symm
        _ = 0 := kernel tailColumn
  have productZero := trivial lifted liftedKernel row.succ
  rw [show lifted row.succ =
      Blocks.head matrix * vector row by
        exact Data.Vector.Basic.vectorOfFn_apply _ _] at productZero
  by_cases vectorZero : vector row = 0
  · exact vectorZero
  · exact (Data.Gaussian.Field.mul_ne_zero_direct
      headNonzero vectorZero productZero).elim

/-- Transport a scaled inverse of a row/column-pivoted matrix back to the
original matrix. -/
@[expose] def unpivotScaledInverse {size : Nat} (matrix : Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : ScaledInverse
      (pivotMatrix matrix rowPivot columnPivot)) :
    ScaledInverse matrix where
  scalar := inverse.scalar
  inverse := swapColumns (swapRows
    inverse.inverse columnPivot) rowPivot
  left_identity := by
    have pivotLeft : SquareMatrix.Rectangular.mul inverse.inverse
        (swapColumns (swapRows matrix rowPivot) columnPivot) =
        Multiplication.scaleIdentity inverse.scalar := inverse.left_identity
    rw [mul_swapColumns_right] at pivotLeft
    have uncolumned := congrArg
      (fun value : Square (size + 1) =>
        swapColumns value columnPivot)
      pivotLeft
    simp only [swapColumns_involutive]
      at uncolumned
    calc
      SquareMatrix.Rectangular.mul
          (swapColumns (swapRows
            inverse.inverse columnPivot) rowPivot)
            matrix =
          SquareMatrix.Rectangular.mul
            (swapRows inverse.inverse columnPivot)
              (swapRows matrix rowPivot) :=
        mul_swapColumns_left _ _ _
      _ = swapRows
            (SquareMatrix.Rectangular.mul inverse.inverse
              (swapRows matrix rowPivot)) columnPivot :=
        mul_swapRows_left _ _ _
      _ = swapRows
            (swapColumns
              (Multiplication.scaleIdentity inverse.scalar)
                columnPivot) columnPivot := by
        rw [uncolumned]
      _ = Multiplication.scaleIdentity inverse.scalar :=
        swapRows_swapColumns_scaleIdentity _ _
  right_identity := by
    have pivotRight : SquareMatrix.Rectangular.mul
        (swapColumns (swapRows matrix rowPivot) columnPivot) inverse.inverse =
        Multiplication.scaleIdentity inverse.scalar := inverse.right_identity
    rw [mul_swapColumns_left,
      mul_swapRows_left] at pivotRight
    have unrowed := congrArg
      (fun value : Square (size + 1) =>
        swapRows value rowPivot) pivotRight
    simp only [swapRows_involutive]
      at unrowed
    calc
      SquareMatrix.Rectangular.mul matrix
          (swapColumns (swapRows
            inverse.inverse columnPivot) rowPivot) =
          swapColumns
            (SquareMatrix.Rectangular.mul matrix
              (swapRows inverse.inverse columnPivot)) rowPivot :=
        mul_swapColumns_right _ _ _
      _ = swapColumns
            (swapRows
              (Multiplication.scaleIdentity inverse.scalar)
                rowPivot) rowPivot := by
        rw [unrowed]
      _ = Multiplication.scaleIdentity inverse.scalar :=
        swapColumns_swapRows_scaleIdentity _ _

/-- Undoing the row and column pivots preserves the retained inverse scalar. -/
@[simp] theorem unpivotScaledInverse_scalar {size : Nat}
    (matrix : Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : ScaledInverse
      (pivotMatrix matrix rowPivot columnPivot)) :
    (unpivotScaledInverse matrix rowPivot columnPivot inverse).scalar =
      inverse.scalar := rfl

/-! ## Finite aggregation of scaled inverses -/

/-- Entrywise finite weighted sum of square matrices. -/
@[expose] def weightedMatrix {count size : Nat} (weights : Fin count →
  Gaussian)
    (matrices : Fin count → Square size) :
      Square size :=
  matrixOfFn fun row column =>
    FiniteSum.Fin.sumFin fun index =>
      weights index * matrices index row column

/-- Read the weighted matrix at one entry as the finite sum of weighted original entries. -/
@[simp] theorem weightedMatrix_apply {count size : Nat}
    (weights : Fin count → Gaussian) (matrices : Fin count →
      Square size)
    (row column : Fin size) :
    weightedMatrix weights matrices row column =
      FiniteSum.Fin.sumFin fun index =>
        weights index * matrices index row column :=
  matrixOfFn_apply _ _ _

/-- Right multiplication distributes over a finite weighted sum of Gaussian matrices. -/
theorem mul_weightedMatrix_left {count size : Nat}
    (weights : Fin count → Gaussian) (matrices : Fin count →
      Square size)
    (right : Square size) :
    Multiplication.mul (weightedMatrix weights matrices) right =
      weightedMatrix weights
        (fun index => Multiplication.mul
          (matrices index) right) := by
  apply matrix_ext
  intro row column
  rw [Multiplication.mul_apply, weightedMatrix_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      FiniteSum.Fin.sumFin fun index =>
        (weights index * matrices index row middle) * right middle column)
    (fun middle => by
      rw [weightedMatrix_apply]
      exact (FiniteSum.Fin.sumFin_mul_right
        (fun index => weights index * matrices index row middle)
          (right middle column)).symm)]
  rw [FiniteSum.Fin.sumFin_swap]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [Multiplication.mul_apply]
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  ring1

/-- Left multiplication distributes over a finite weighted sum of Gaussian matrices. -/
theorem mul_weightedMatrix_right {count size : Nat}
    (left : Square size) (weights : Fin count →
      Gaussian)
    (matrices : Fin count → Square size) :
    Multiplication.mul left (weightedMatrix weights matrices) =
      weightedMatrix weights
        (fun index => Multiplication.mul left
          (matrices index)) := by
  apply matrix_ext
  intro row column
  rw [Multiplication.mul_apply, weightedMatrix_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      FiniteSum.Fin.sumFin fun index =>
        weights index * (left row middle * matrices index middle column))
    (fun middle => by
      rw [weightedMatrix_apply]
      rw [← FiniteSum.Fin.sumFin_mul_left]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      ring1)]
  rw [FiniteSum.Fin.sumFin_swap]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [Multiplication.mul_apply]
  rw [← FiniteSum.Fin.sumFin_mul_left]

/-- A weighted sum of scalar identities is the identity with the corresponding weighted scalar sum. -/
theorem weightedMatrix_scaleIdentity {count size : Nat}
    (weights scalars : Fin count → Gaussian) :
    weightedMatrix weights
        (fun index => (Multiplication.scaleIdentity
          (scalars index) : Square size)) =
      Multiplication.scaleIdentity
        (FiniteSum.Fin.sumFin fun index =>
          weights index * scalars index) := by
  apply matrix_ext
  intro row column
  rw [weightedMatrix_apply,
    Multiplication.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [Multiplication.scaleIdentity_apply, if_pos rfl]
  · rw [if_neg equal]
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun _ => (0 : Gaussian)) (fun index => by
        rw [Multiplication.scaleIdentity_apply, if_neg equal,
          Data.Gaussian.Basic.mul_zero])]
    exact FiniteSum.Fin.sumFin_zero

/-- Any finite weighted sum of scaled inverses is another scaled inverse.
This algebraic closure is what permits all pivot branches to be retained
without making a discontinuous pivot choice. -/
@[expose] def aggregateScaledInverse {count size : Nat} {matrix : Square size}
    (branches : Fin count → ScaledInverse matrix)
    (weights : Fin count → Gaussian) :
      ScaledInverse matrix where
  scalar := FiniteSum.Fin.sumFin fun index =>
    weights index * (branches index).scalar
  inverse := weightedMatrix weights fun index => (branches index).inverse
  left_identity := by
    rw [mul_weightedMatrix_left]
    calc
      weightedMatrix weights
          (fun index => Multiplication.mul
            (branches index).inverse matrix) =
          weightedMatrix weights
            (fun index => (Multiplication.scaleIdentity
              (branches index).scalar : Square size)) := by
        apply matrix_ext
        intro row column
        rw [weightedMatrix_apply,
          weightedMatrix_apply]
        apply FiniteSum.Fin.sumFin_congr
        intro index
        rw [matrix_eq_at
          (branches index).left_identity row column]
      _ = Multiplication.scaleIdentity
            (FiniteSum.Fin.sumFin fun index =>
              weights index * (branches index).scalar) :=
        weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)
  right_identity := by
    rw [mul_weightedMatrix_right]
    calc
      weightedMatrix weights
          (fun index => Multiplication.mul matrix
            (branches index).inverse) =
          weightedMatrix weights
            (fun index => (Multiplication.scaleIdentity
              (branches index).scalar : Square size)) := by
        apply matrix_ext
        intro row column
        rw [weightedMatrix_apply,
          weightedMatrix_apply]
        apply FiniteSum.Fin.sumFin_congr
        intro index
        rw [matrix_eq_at
          (branches index).right_identity row column]
      _ = Multiplication.scaleIdentity
            (FiniteSum.Fin.sumFin fun index =>
              weights index * (branches index).scalar) :=
        weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)

/-- The aggregate inverse scalar is the finite weighted sum of the retained branch scalars. -/
@[simp] theorem aggregateScaledInverse_scalar {count size : Nat}
    {matrix : Square size} (branches : Fin count →
      ScaledInverse matrix)
    (weights : Fin count → Gaussian) :
    (aggregateScaledInverse branches weights).scalar =
      FiniteSum.Fin.sumFin fun index =>
        weights index * (branches index).scalar := rfl

/-- Pointwise rational inequalities are preserved by the finite indexed sum. -/
theorem coordinateSum_mono {count : Nat}
    (left right : Fin count → Coordinate)
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
    (values : Fin count → Coordinate) (selected : Fin count)
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
        coordinateSum_mono _ _ (fun index => by
          by_cases equal : index = selected
          · rw [if_pos equal]
          · rw [if_neg equal]
            exact nonnegative index)
  exact positive.trans_le selected_le_sum

/-- Taking the real part commutes with the finite Gaussian sum. -/
theorem sumFin_re {count : Nat} (values : Fin count → Gaussian) :
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
theorem conj_mul_self_re (value : Gaussian) :
    (Data.Gaussian.Basic.conj value * value).re = Basic.normSq value := by
  simp only [Data.Gaussian.Basic.conj, Data.Gaussian.Basic.mul_re, Basic.normSq]
  ring1

/-- A successful finite pivot branch cannot be cancelled by the other
branches: conjugate weighting makes the aggregate scalar's real coordinate a
sum of squared norms. -/
theorem aggregateConjugate_scalar_nonzero_of_branch {count size : Nat}
    {matrix : Square size} (branches : Fin count →
      ScaledInverse matrix)
    (selected : Fin count) (selectedNonzero : (branches selected).scalar ≠ 0) :
    (aggregateScaledInverse branches
      (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar ≠ 0 := by
  have realIdentity :
      (aggregateScaledInverse branches
        (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re =
        FiniteSum.Fin.sumFin fun index =>
          Basic.normSq (branches index).scalar := by
    rw [aggregateScaledInverse_scalar,
      sumFin_re]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    exact conj_mul_self_re (branches index).scalar
  have realPositive :
      0 < FiniteSum.Fin.sumFin fun index =>
        Basic.normSq (branches index).scalar :=
    coordinateSum_positive_of_index _ selected
      (fun index => Basic.normSq_nonneg (branches index).scalar)
      (Basic.normSq_pos selectedNonzero)
  intro aggregateZero
  have zeroReal := congrArg Data.Gaussian.Basic.re aggregateZero
  change (aggregateScaledInverse branches
    (fun index => Data.Gaussian.Basic.conj (branches index).scalar)).scalar.re = 0 at zeroReal
  rw [realIdentity] at zeroReal
  change FiniteSum.Fin.sumFin
      (fun index => Basic.normSq (branches index).scalar) = 0 at zeroReal
  rw [zeroReal]
    at realPositive
  exact lt_irrefl 0 realPositive

/-! ## Pivot-complete exact recursion -/

/-- One exact pivot branch, parameterized by the recursively computed scaled
inverse of its Schur matrix. -/
@[expose] def pivotBranch {size : Nat} (matrix : Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : ScaledInverse
      (Schur.schur
        (pivotMatrix matrix rowPivot columnPivot))) :
          ScaledInverse matrix :=
  let pivoted := pivotMatrix matrix rowPivot columnPivot
  unpivotScaledInverse matrix rowPivot columnPivot
    (Scaled.Block.extendScaledInverse pivoted smaller)

/-- All row/column pivot branches of the fraction-free recursion are retained.
Each finite aggregation uses conjugate scalar weights, so its new scalar is a
sum of Gaussian norm squares rather than a cancellation-prone sum. -/
@[expose] def completeScaledInverse : {size : Nat} ->
    (matrix : Square size) ->
      ScaledInverse matrix
  | 0, matrix => Scaled.Compute.scaledInverse matrix
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        pivotBranch matrix rowPivot columnPivot
          (PivotedScaledInverse.completeScaledInverse
            (Schur.schur
              (pivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        aggregateScaledInverse (branch rowPivot)
          (fun columnPivot => Data.Gaussian.Basic.conj (branch rowPivot columnPivot).scalar)
      aggregateScaledInverse rowBranch
        (fun rowPivot => Data.Gaussian.Basic.conj (rowBranch rowPivot).scalar)

/-- Compute the exact scaled inverse branch for one retained row-column pivot.

The recursive inverse of that pivoted Schur complement is extended and transported back to the original matrix. -/
@[expose] def completeExactBranch {size : Nat} (matrix : Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : ScaledInverse matrix :=
  pivotBranch matrix rowPivot columnPivot
    (completeScaledInverse
      (Schur.schur
        (pivotMatrix matrix rowPivot columnPivot)))

/-- Aggregate all column-pivot branches for one retained row using conjugate scalar weights.

The result remains a scaled inverse of the same original matrix. -/
@[expose] def completeExactRow {size : Nat} (matrix : Square (size + 1))
    (rowPivot : Fin (size + 1)) : ScaledInverse matrix :=
  aggregateScaledInverse
    (completeExactBranch matrix rowPivot)
    (fun columnPivot =>
      Data.Gaussian.Basic.conj (completeExactBranch matrix rowPivot
        columnPivot).scalar)

/-- At positive dimension, the complete inverse is the conjugate-weighted aggregate of its row branches. -/
theorem completeScaledInverse_succ {size : Nat}
    (matrix : Square (size + 1)) :
    completeScaledInverse matrix =
      aggregateScaledInverse
        (completeExactRow matrix)
        (fun rowPivot => Data.Gaussian.Basic.conj (completeExactRow
          matrix rowPivot).scalar) := rfl

/-- The complete inverse times its original matrix is its retained scalar identity. -/
theorem completeScaledInverse_left_identity {size : Nat}
    (matrix : Square size) :
    Multiplication.mul
        (completeScaledInverse matrix).inverse matrix =
      Multiplication.scaleIdentity
        (completeScaledInverse matrix).scalar :=
  (completeScaledInverse matrix).left_identity

/-- The original matrix times its complete inverse is its retained scalar identity. -/
theorem completeScaledInverse_right_identity {size : Nat}
    (matrix : Square size) :
    Multiplication.mul matrix
        (completeScaledInverse matrix).inverse =
      Multiplication.scaleIdentity
        (completeScaledInverse matrix).scalar :=
  (completeScaledInverse matrix).right_identity

/-- A Gaussian sum over one coordinate equals that coordinate. -/
private theorem sumFin_one (values : Fin 1 -> Gaussian) :
    FiniteSum.Fin.sumFin values = values 0 := by
  rw [FiniteSum.Fin.sumFin_succ]
  change values 0 + 0 = values 0
  ring1

/-- The sole pivot branch in dimension one has scalar equal to the original matrix entry. -/
private theorem completeExactBranch_one_scalar (matrix : Square 1) :
    (completeExactBranch matrix 0 0).scalar = matrix 0 0 := by
  unfold completeExactBranch
    pivotBranch
  rw [unpivotScaledInverse_scalar]
  change Blocks.head (pivotMatrix matrix 0 0) * 1 =
    matrix 0 0
  unfold Blocks.head pivotMatrix
  rw [swapColumns_apply,
    swapRows_apply, swapZero_zero]
  ring1

/-- In dimension one the pivot-complete recursion has just one row and one
column branch.  Its two conjugate aggregations therefore expose the fourth
power construction explicitly. -/
theorem completeScaledInverse_one_scalar (matrix : Square 1) :
    (completeScaledInverse matrix).scalar =
      Data.Gaussian.Basic.conj (Data.Gaussian.Basic.conj (matrix 0 0) * matrix 0 0) *
        (Data.Gaussian.Basic.conj (matrix 0 0) * matrix 0 0) := by
  rw [completeScaledInverse_succ,
    aggregateScaledInverse_scalar,
    sumFin_one]
  unfold completeExactRow
  rw [aggregateScaledInverse_scalar,
    sumFin_one]
  rw [completeExactBranch_one_scalar]

/-- Consequently the squared norm of the dimension-one canonical scalar is
the fourth power of the squared norm of the sole matrix entry. -/
theorem normSq_completeScaledInverse_one_scalar (matrix : Square 1) :
    Basic.normSq (completeScaledInverse
      matrix).scalar =
      Basic.normSq (matrix 0 0) ^ 4 := by
  rw [completeScaledInverse_one_scalar]
  repeat' rw [Basic.normSq_mul, Basic.normSq_conj]
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
@[expose] def geometricConj (source : GeometricApproximation) :
    GeometricApproximation where
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
    rw [difference, Basic.normSq_conj]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Basic.normSq_conj]
    exact source.sample_bounded index

/-- Sampling geometric conjugation gives the conjugate of the original sample. -/
@[simp] theorem geometricConj_sample (source : GeometricApproximation)
    (index : Nat) :
    (geometricConj source).sample index = Data.Gaussian.Basic.conj
      (source.sample index) := rfl

/-- Exchange the leading row with the displayed row of a geometric matrix.

Each entry retains its original approximation program and certificates. -/
@[expose] def geometricSwapRows {size : Nat} (matrix : GeometricMatrix (size +
  1))
    (pivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  matrixOfFn fun row column =>
    matrix (swapZero pivot row) column

/-- Exchange the leading column with the displayed column of a geometric matrix.

Each entry retains its original approximation program and certificates. -/
@[expose] def geometricSwapColumns {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  matrixOfFn fun row column =>
    matrix row (swapZero pivot column)

/-- Read a row-swapped geometric matrix at its transposed original row index. -/
@[simp] theorem geometricSwapRows_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    geometricSwapRows matrix pivot row column =
      matrix (swapZero pivot row) column :=
  matrixOfFn_apply _ _ _

/-- Read a column-swapped geometric matrix at its transposed original column index. -/
@[simp] theorem geometricSwapColumns_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    geometricSwapColumns matrix pivot row column =
      matrix row (swapZero pivot column) :=
  matrixOfFn_apply _ _ _

/-- Move the displayed geometric matrix entry to the leading row and column. -/
@[expose] def geometricPivotMatrix {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  geometricSwapColumns
    (geometricSwapRows matrix rowPivot) columnPivot

/-- Undo a geometric inverse pivot by exchanging the opposite row and column indices. -/
@[expose] def geometricUnpivotInverse {size : Nat}
    (inverse : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    GeometricMatrix (size + 1) :=
  geometricSwapColumns
    (geometricSwapRows inverse columnPivot) rowPivot

/-- Entrywise synchronized weighted sum. -/
@[expose] def geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size) :
      GeometricMatrix size :=
  matrixOfFn fun row column =>
    GeometricApproximation.sum
      fun index =>
        GeometricApproximation.mul
          (weights index) (matrices index row column)

/-- Read one entry of the synchronized weighted matrix sum. -/
@[simp] theorem geometricWeightedMatrix_apply {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size)
    (row column : Fin size) :
    geometricWeightedMatrix weights matrices row column =
      GeometricApproximation.sum
        fun index =>
          GeometricApproximation.mul
            (weights index) (matrices index row column) :=
  matrixOfFn_apply _ _ _

/-- Aggregate retained inverse approximations with the supplied synchronized weights.

The scalar and inverse entries use the same finite branch indices and weight programs. -/
@[expose] def geometricAggregate {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) :
    ScaledInverseApproximation size where
  scalar := GeometricApproximation.sum
    fun index =>
      GeometricApproximation.mul
        (weights index) (branches index).scalar
  inverse := geometricWeightedMatrix weights
    fun index => (branches index).inverse

/-- One synchronized pivot branch, parameterized by the recursively computed
Schur approximation. -/
@[expose] def geometricPivotBranch {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : ScaledInverseApproximation size) :
    ScaledInverseApproximation (size + 1) :=
  let pivoted := geometricPivotMatrix matrix rowPivot columnPivot
  { scalar :=
      GeometricApproximation.mul
        (pivoted 0 0) smaller.scalar
    inverse := geometricUnpivotInverse
      (Approximation.Matrix.blockInverse pivoted smaller)
        rowPivot columnPivot }

/-- The synchronized all-pivots recursion mirrors `completeScaledInverse`
exactly at every sample index. -/
@[expose] def completeApproximation : {size : Nat} ->
    GeometricMatrix size ->
      ScaledInverseApproximation size
  | 0, _matrix =>
      { scalar :=
          GeometricApproximation.exact 1
        inverse := matrixOfFn fun row =>
          Fin.elim0 row }
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        geometricPivotBranch matrix rowPivot columnPivot
          (PivotedScaledInverse.completeApproximation
            (Approximation.Matrix.schur
              (geometricPivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        geometricAggregate (branch rowPivot)
          (fun columnPivot =>
            geometricConj (branch rowPivot columnPivot).scalar)
      geometricAggregate rowBranch
        (fun rowPivot => geometricConj (rowBranch rowPivot).scalar)

/-- Any successful recursive row/column pivot proves the complete scalar
nonzero; all other branches can only add squared-norm contributions. -/
theorem completeScaledInverse_scalar_nonzero_of_branch {size : Nat}
    (matrix : Square (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (branchNonzero :
      (completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0) :
    (completeScaledInverse matrix).scalar ≠ 0 := by
  have rowNonzero : (completeExactRow matrix rowPivot).scalar ≠ 0 :=
    aggregateConjugate_scalar_nonzero_of_branch
      (completeExactBranch matrix rowPivot) columnPivot branchNonzero
  rw [completeScaledInverse_succ]
  exact aggregateConjugate_scalar_nonzero_of_branch
    (completeExactRow matrix) rowPivot rowNonzero

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse in
/-- The pivot-complete fraction-free construction is complete for finite
Gaussian matrices: a trivial displayed left kernel constructively produces a
nonzero canonical scalar.  The proof searches the bounded entry table for a
pivot, descends to its Schur matrix, and retains that successful branch in the
conjugate-weighted aggregate. -/
theorem completeScaledInverse_scalar_nonzero_of_leftKernelTrivial :
    {size : Nat} -> (matrix : Square size) ->
      LeftKernelTrivial matrix ->
      (completeScaledInverse matrix).scalar ≠ 0
  | 0, matrix, _trivial => by
      change (1 : Gaussian) ≠ 0
      decide
  | size + 1, matrix, trivial => by
      rcases exists_nonzero_entry_of_leftKernelTrivial matrix trivial with
        ⟨rowPivot, columnPivot, pivotNonzero⟩
      let pivoted := pivotMatrix matrix rowPivot columnPivot
      have pivotedTrivial : LeftKernelTrivial pivoted := by
        simpa only [pivoted] using
          leftKernelTrivial_pivotMatrix trivial rowPivot columnPivot
      have headNonzero : Blocks.head pivoted ≠ 0 := by
        simpa only [pivoted, Blocks.head,
          pivotMatrix,
            swapColumns_apply,
            swapRows_apply,
            swapZero_zero] using
          pivotNonzero
      have smallerTrivial : LeftKernelTrivial
          (Schur.schur pivoted) :=
        leftKernelTrivial_schur_of_head_nonzero pivoted pivotedTrivial
          headNonzero
      have smallerNonzero :
          (completeScaledInverse
            (Schur.schur pivoted)).scalar ≠ 0 :=

          completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
          (Schur.schur pivoted) smallerTrivial
      have branchNonzero :
          (completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0 := by
        change Blocks.head pivoted *
            (completeScaledInverse
              (Schur.schur pivoted)).scalar ≠ 0
        exact Data.Gaussian.Field.mul_ne_zero_direct
          headNonzero smallerNonzero
      exact completeScaledInverse_scalar_nonzero_of_branch matrix rowPivot
        columnPivot branchNonzero

/-- The smallest matrix rejected by the fixed-pivot recursion is accepted by
the complete construction.  This executable regression is the row-swap
matrix `[[0,1],[1,0]]`. -/
@[expose] def twoByTwoSwap : Square 2 :=
  swapRows (Multiplication.identity :
    Square 2) 1

/-- The fixed-pivot scaled inverse has zero scalar on the two-coordinate swap matrix. -/
theorem twoByTwoSwap_fixedScalar_zero :
    (Scaled.Compute.scaledInverse twoByTwoSwap).scalar =
      0 := by
  decide

/-- The complete pivot construction has nonzero scalar on the two-coordinate swap matrix. -/
theorem twoByTwoSwap_completeScalar_nonzero :
    (completeScaledInverse
      twoByTwoSwap).scalar ≠ 0 := by decide

/-- Compute one synchronized row-column pivot branch and its recursive Schur approximation.

The retained pivot indices determine the transport back to the original matrix coordinates. -/
@[expose] def completeGeometricBranch {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    ScaledInverseApproximation (size + 1) :=
  geometricPivotBranch matrix rowPivot columnPivot
    (completeApproximation
      (Approximation.Matrix.schur
        (geometricPivotMatrix matrix rowPivot columnPivot)))

/-- Aggregate the synchronized column branches for one retained row with conjugate scalar weights. -/
@[expose] def completeGeometricRow {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot : Fin (size + 1)) : ScaledInverseApproximation (size + 1) :=
  geometricAggregate
    (completeGeometricBranch matrix rowPivot)
    (fun columnPivot =>
      geometricConj
        (completeGeometricBranch matrix rowPivot columnPivot).scalar)

/-- At positive dimension, the complete approximation aggregates its synchronized row branches. -/
theorem completeApproximation_succ {size : Nat}
    (matrix : GeometricMatrix (size + 1)) :
    completeApproximation matrix =
      geometricAggregate
        (completeGeometricRow matrix)
        (fun rowPivot =>
          geometricConj
            (completeGeometricRow matrix rowPivot).scalar) := rfl

/-- Sampling commutes with the displayed geometric row transposition.

Every finite entry uses the same original sample index and transposed row.
Scalar readback therefore identifies the two structural matrices. -/
@[simp] theorem sampleMatrix_geometricSwapRows {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricSwapRows matrix pivot) index =
      swapRows
        (Approximation.Matrix.sampleMatrix matrix index)
          pivot := by
  apply matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    geometricSwapRows_apply,
      swapRows_apply, Approximation.Matrix.sampleMatrix_apply]
  exact Eq.refl _

/-- Sampling commutes with the displayed geometric column transposition.

Every finite entry uses the same original sample index and transposed column.
Scalar readback therefore identifies the two structural matrices. -/
@[simp] theorem sampleMatrix_geometricSwapColumns {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricSwapColumns matrix pivot) index =
      swapColumns
        (Approximation.Matrix.sampleMatrix matrix index)
          pivot := by
  apply matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    geometricSwapColumns_apply,
      swapColumns_apply, Approximation.Matrix.sampleMatrix_apply]
  exact Eq.refl _

/-- Sampling the geometric pivot matrix gives the same pivot of the sampled matrix. -/
@[simp] theorem sampleMatrix_geometricPivotMatrix {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricPivotMatrix matrix rowPivot columnPivot) index =
      pivotMatrix
        (Approximation.Matrix.sampleMatrix matrix index)
          rowPivot columnPivot := by
  unfold geometricPivotMatrix
    pivotMatrix
  rw [sampleMatrix_geometricSwapColumns,
    sampleMatrix_geometricSwapRows]

/-- Sampling commutes with the row-column transport that undoes the inverse pivot. -/
@[simp] theorem sampleMatrix_geometricUnpivotInverse {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricUnpivotInverse matrix rowPivot columnPivot) index =
      swapColumns
        (swapRows
          (Approximation.Matrix.sampleMatrix matrix index)
            columnPivot) rowPivot := by
  unfold geometricUnpivotInverse
  rw [sampleMatrix_geometricSwapColumns,
    sampleMatrix_geometricSwapRows]

/-- Sampling a synchronized weighted matrix sum gives the weighted sum of its samples. -/
@[simp] theorem sampleMatrix_geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricWeightedMatrix weights matrices) index =
      weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          Approximation.Matrix.sampleMatrix
            (matrices branch) index) := by
  apply matrix_ext
  intro row column
  rw [Approximation.Matrix.sampleMatrix_apply,
    geometricWeightedMatrix_apply,
      weightedMatrix_apply,
    GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro branch
  rw [GeometricApproximation.mul_sample,
    Approximation.Matrix.sampleMatrix_apply]

/-- Read the aggregate scalar sample as the weighted sum of branch scalar samples. -/
@[simp] theorem geometricAggregate_scalar_sample {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) (index : Nat) :
    (geometricAggregate branches weights).scalar.sample index =
      FiniteSum.Fin.sumFin fun branch =>
        (weights branch).sample index * (branches branch).scalar.sample index := by
  unfold geometricAggregate
  rw [GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro branch
  rw [GeometricApproximation.mul_sample]

/-- Read the aggregate inverse sample as the weighted sum of branch inverse samples. -/
@[simp] theorem geometricAggregate_inverse_sample {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) (index : Nat) :
    Approximation.Matrix.sampleMatrix
        (geometricAggregate branches weights).inverse index =
      weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          Approximation.Matrix.sampleMatrix
            (branches branch).inverse index) := by
  unfold geometricAggregate
  exact sampleMatrix_geometricWeightedMatrix weights
    (fun branch => (branches branch).inverse) index

/-- Retain exact scalar and inverse sample agreement through finite weighted aggregation.

All branch and weight equalities refer to the same supplied sample index. -/
theorem geometricAggregate_sample {count size : Nat}
    {matrix : Square size}
    (geometricBranches : Fin count → ScaledInverseApproximation size)
    (exactBranches : Fin count → ScaledInverse matrix)
    (geometricWeights : Fin count → GeometricApproximation)
    (exactWeights : Fin count → Gaussian) (index : Nat)
    (scalarSamples : forall branch,
      (geometricBranches branch).scalar.sample index =
        (exactBranches branch).scalar)
    (inverseSamples : forall branch,
      Approximation.Matrix.sampleMatrix
          (geometricBranches branch).inverse index =
        (exactBranches branch).inverse)
    (weightSamples : forall branch,
      (geometricWeights branch).sample index = exactWeights branch) :
    (geometricAggregate geometricBranches geometricWeights).scalar.sample
      index =
        (aggregateScaledInverse exactBranches exactWeights).scalar ∧
      Approximation.Matrix.sampleMatrix
          (geometricAggregate geometricBranches geometricWeights).inverse
            index =
        (aggregateScaledInverse exactBranches exactWeights).inverse := by
  constructor
  · rw [geometricAggregate_scalar_sample,
      aggregateScaledInverse_scalar]
    apply FiniteSum.Fin.sumFin_congr
    intro branch
    rw [weightSamples branch, scalarSamples branch]
  · rw [geometricAggregate_inverse_sample]
    apply matrix_ext
    intro row column
    change
      weightedMatrix
          (fun branch => (geometricWeights branch).sample index)
          (fun branch =>
            Approximation.Matrix.sampleMatrix
              (geometricBranches branch).inverse index) row column =
        weightedMatrix exactWeights
          (fun branch => (exactBranches branch).inverse) row column
    rw [weightedMatrix_apply,
      weightedMatrix_apply]
    apply FiniteSum.Fin.sumFin_congr
    intro branch
    rw [weightSamples branch]
    have entrySample := matrix_eq_at
      (inverseSamples branch) row column
    rw [entrySample]

/-! The raw block formula is separated from its identity proofs so sampling
can be checked entrywise without transporting a dependent proof object across
matrix extensional equality. -/

/-- Compute the fraction-free block inverse from its scalar and smaller matrix.

The original pivot, row, column and two product caches determine the corner
and edge entries. Owned finite dispatch selects those same cached values or
the original squared-pivot multiple of a trailing entry. -/
@[expose] def rawBlockInverse {size : Nat} (matrix : Square (size + 1))
    (scalar : Gaussian) (inverse :
      Square size) : Square (size +
      1) :=
  let a := Blocks.head matrix
  let row := Blocks.topRow matrix
  let column := Blocks.leftColumn matrix
  let inverseColumn :=
    Multiplication.matrixVector inverse column
  let rowInverse := Multiplication.vectorMatrix row inverse
  let corner := scalar +
    Dot.dot row inverseColumn
  matrixOfFn fun i j => Data.Fin.cases
    (Data.Fin.cases corner (fun columnIndex => -a * rowInverse columnIndex) j)
    (fun rowIndex => Data.Fin.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => (a * a) * inverse rowIndex columnIndex) j) i

/-- Read a raw block-inverse entry at its original finite coordinates.

The leading corner, two edge products and trailing scaled entry use the
original scalar, inverse and cached row-column products of the construction. -/
@[simp] theorem rawBlockInverse_apply {size : Nat}
    (matrix : Square (size + 1)) (scalar :
      Gaussian)
    (inverse : Square size) (row column : Fin (size + 1)) :
    rawBlockInverse matrix scalar inverse row column =
      Data.Fin.cases
        (Data.Fin.cases
          (scalar + Dot.dot
            (Blocks.topRow matrix)
            (Multiplication.matrixVector inverse
              (Blocks.leftColumn matrix)))
          (fun columnIndex =>
            -Blocks.head matrix *
              Multiplication.vectorMatrix
                (Blocks.topRow matrix) inverse
                  columnIndex) column)
        (fun rowIndex => Data.Fin.cases
          (-Blocks.head matrix *
            Multiplication.matrixVector inverse
              (Blocks.leftColumn matrix) rowIndex)
          (fun columnIndex =>
            (Blocks.head matrix *
              Blocks.head matrix) *
                inverse rowIndex columnIndex) column) row := by
  unfold rawBlockInverse
  rewrite [matrixOfFn_apply]
  exact Eq.refl _

/-- The raw block formula equals the certified block inverse for its retained data.

The original scalar and inverse are read at the same finite block coordinates.
Direct finite case analysis compares the leading corner, edges and trailing
block without changing either executable construction. -/
@[simp] theorem rawBlockInverse_eq_blockInverse {size : Nat}
    (matrix : Square (size + 1))
    (smaller : ScaledInverse (Schur.schur matrix)) :
    rawBlockInverse matrix smaller.scalar smaller.inverse =
      Scaled.Block.blockInverse matrix smaller := by
  apply matrix_ext
  intro row column
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [rawBlockInverse_apply,
        Scaled.Block.blockInverse_apply,
        Data.Fin.cases_zero, Data.Fin.cases_zero]
      exact Eq.refl _
    · rewrite [rawBlockInverse_apply,
        Scaled.Block.blockInverse_apply,
        Data.Fin.cases_zero, Data.Fin.cases_succ]
      exact Eq.refl _
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [rawBlockInverse_apply,
        Scaled.Block.blockInverse_apply,
        Data.Fin.cases_succ, Data.Fin.cases_zero,
        Data.Fin.cases_succ, Data.Fin.cases_zero]
      exact Eq.refl _
    · rewrite [rawBlockInverse_apply,
        Scaled.Block.blockInverse_apply,
        Data.Fin.cases_succ, Data.Fin.cases_succ,
        Data.Fin.cases_succ, Data.Fin.cases_succ]
      rewrite [pow_two]
      exact Eq.refl _

/-- Sampling the geometric block formula gives the raw exact block formula.

The original matrix, scalar and smaller inverse agree with their exact counterparts at the same supplied sample index.
-/
theorem geometricBlockInverse_sample {size : Nat}
    (geometricMatrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) (index : Nat)
    (exactMatrix : Square (size + 1)) (exactScalar :
      Gaussian)
    (exactInverse : Square size)
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
      rawBlockInverse exactMatrix exactScalar exactInverse := by
  have rowSample :
      Approximation.Matrix.sampleVector
          (fun entry : Fin size => geometricMatrix 0 entry.succ) index =
        Blocks.topRow exactMatrix := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      Blocks.topRow_apply]
    have sampledEntry := matrix_eq_at
      matrixSample 0 entry.succ
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  have columnSample :
      Approximation.Matrix.sampleVector
          (fun entry : Fin size => geometricMatrix entry.succ 0) index =
        Blocks.leftColumn exactMatrix := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      Blocks.leftColumn_apply]
    have sampledEntry := matrix_eq_at
      matrixSample entry.succ 0
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  have inverseColumnSample :
      Approximation.Matrix.sampleVector
          (Approximation.Matrix.matrixVector smaller.inverse
            (fun entry : Fin size => geometricMatrix entry.succ 0)) index =
        Multiplication.matrixVector exactInverse
          (Blocks.leftColumn exactMatrix) := by
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
        Multiplication.vectorMatrix
          (Blocks.topRow exactMatrix)
            exactInverse := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [Approximation.Matrix.sampleVector_apply,
      Approximation.Matrix.vectorMatrix_sample,
      inverseSample, rowSample]
  have headSample : (geometricMatrix 0 0).sample index =
      Blocks.head exactMatrix := by
    have sampledEntry := matrix_eq_at
      matrixSample 0 0
    rw [Approximation.Matrix.sampleMatrix_apply]

        at sampledEntry
    exact sampledEntry
  apply matrix_ext
  intro row column
  rewrite [Approximation.Matrix.sampleMatrix_apply,
    Approximation.Matrix.blockInverse_apply,
    rawBlockInverse_apply]
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [Data.Fin.cases_zero, Data.Fin.cases_zero,
        Data.Fin.cases_zero, Data.Fin.cases_zero]
      rewrite [GeometricApproximation.add_sample,
        scalarSample, Approximation.Matrix.dot_sample, rowSample, inverseColumnSample]
      exact Eq.refl _
    · rewrite [Data.Fin.cases_zero, Data.Fin.cases_succ,
        Data.Fin.cases_zero, Data.Fin.cases_succ]
      rewrite [GeometricApproximation.mul_sample,
        GeometricApproximation.neg_sample, headSample]
      have entrySample := Data.Vector.Basic.vector_eq_at rowInverseSample columnIndex
      rewrite [Approximation.Matrix.sampleVector_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rewrite [Data.Fin.cases_succ, Data.Fin.cases_zero,
        Data.Fin.cases_succ, Data.Fin.cases_zero]
      rewrite [GeometricApproximation.mul_sample,
        GeometricApproximation.neg_sample, headSample]
      have entrySample := Data.Vector.Basic.vector_eq_at inverseColumnSample rowIndex
      rewrite [Approximation.Matrix.sampleVector_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _
    · rewrite [Data.Fin.cases_succ, Data.Fin.cases_succ,
        Data.Fin.cases_succ, Data.Fin.cases_succ]
      rewrite [GeometricApproximation.mul_sample,
        GeometricApproximation.mul_sample, headSample]
      have entrySample := matrix_eq_at inverseSample rowIndex columnIndex
      rewrite [Approximation.Matrix.sampleMatrix_apply] at entrySample
      rewrite [entrySample]
      exact Eq.refl _

/-- A synchronized pivot branch retains exact scalar and inverse sample agreement.

The smaller approximate and certified inverses are compared at the same sample index and original pivot coordinates. -/
theorem geometricPivotBranch_sample {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat)
    (smaller : ScaledInverseApproximation size)
    (exactSmaller : ScaledInverse
      (Schur.schur
        (pivotMatrix
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot)))
    (scalarSample : smaller.scalar.sample index = exactSmaller.scalar)
    (inverseSample :
      Approximation.Matrix.sampleMatrix smaller.inverse index =
        exactSmaller.inverse) :
    (geometricPivotBranch matrix rowPivot columnPivot smaller).scalar.sample
          index =
        (pivotBranch
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).scalar ∧
      Approximation.Matrix.sampleMatrix
          (geometricPivotBranch matrix rowPivot columnPivot smaller).inverse
            index =
        (pivotBranch
          (Approximation.Matrix.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).inverse := by
  let geometricPivot := geometricPivotMatrix matrix rowPivot columnPivot
  let exactMatrix :=
    Approximation.Matrix.sampleMatrix matrix index
  let exactPivot := pivotMatrix exactMatrix rowPivot columnPivot
  have pivotSample :
      Approximation.Matrix.sampleMatrix geometricPivot index =
        exactPivot :=
    sampleMatrix_geometricPivotMatrix matrix rowPivot columnPivot index
  have extendedInverseSample :
      Approximation.Matrix.sampleMatrix
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) index =
        (Scaled.Block.extendScaledInverse
          exactPivot exactSmaller).inverse := by
    calc
      Approximation.Matrix.sampleMatrix
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) index =
          rawBlockInverse exactPivot exactSmaller.scalar
            exactSmaller.inverse :=
        geometricBlockInverse_sample geometricPivot smaller index exactPivot
          exactSmaller.scalar exactSmaller.inverse pivotSample scalarSample
            inverseSample
      _ = (Scaled.Block.extendScaledInverse
            exactPivot exactSmaller).inverse :=
        rawBlockInverse_eq_blockInverse exactPivot exactSmaller
  constructor
  · change
      (GeometricApproximation.mul
        (geometricPivot 0 0) smaller.scalar).sample index =
        (Scaled.Block.extendScaledInverse
          exactPivot exactSmaller).scalar
    rw [GeometricApproximation.mul_sample]
    have pivotEntry := matrix_eq_at
      pivotSample 0 0
    rw [Approximation.Matrix.sampleMatrix_apply]
      at pivotEntry
    rw [pivotEntry, scalarSample]
    rfl
  · change
      Approximation.Matrix.sampleMatrix
        (geometricUnpivotInverse
          (Approximation.Matrix.blockInverse
            geometricPivot smaller) rowPivot columnPivot) index = _
    rw [sampleMatrix_geometricUnpivotInverse, extendedInverseSample]
    rfl

/-- Every synchronized finite sample is exactly the pivot-complete scaled
inverse of the source matrix at that same sample index. -/
theorem completeApproximation_sample : forall {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat),
    (completeApproximation matrix).scalar.sample index =
        (completeScaledInverse
          (Approximation.Matrix.sampleMatrix matrix index)).scalar ∧
      Approximation.Matrix.sampleMatrix
          (completeApproximation matrix).inverse index =
        (completeScaledInverse
          (Approximation.Matrix.sampleMatrix matrix index)).inverse
  | 0, _matrix, _index => by
      constructor
      · rfl
      · rfl
  | size + 1, matrix, index => by
      let exactMatrix :=
        Approximation.Matrix.sampleMatrix matrix index
      have branchSample : forall rowPivot columnPivot,
          (completeGeometricBranch matrix rowPivot columnPivot).scalar.sample
                index =
              (completeExactBranch exactMatrix rowPivot columnPivot).scalar ∧
            Approximation.Matrix.sampleMatrix
                (completeGeometricBranch matrix rowPivot columnPivot).inverse
                  index =
              (completeExactBranch exactMatrix rowPivot columnPivot).inverse
                := by
        intro rowPivot columnPivot
        let geometricPivot :=
          geometricPivotMatrix matrix rowPivot columnPivot
        have recursive :=
          PivotedScaledInverse.completeApproximation_sample
          (Approximation.Matrix.schur geometricPivot) index
        have pivotSample := sampleMatrix_geometricPivotMatrix matrix
          rowPivot columnPivot index
        rw [Approximation.Matrix.sampleMatrix_schur,
          pivotSample] at recursive
        exact geometricPivotBranch_sample matrix rowPivot columnPivot index
          (completeApproximation
            (Approximation.Matrix.schur geometricPivot))
          (completeScaledInverse
            (Schur.schur
              (pivotMatrix exactMatrix rowPivot columnPivot)))
          recursive.1 recursive.2
      have rowSample : forall rowPivot,
          (completeGeometricRow matrix rowPivot).scalar.sample index =
                (completeExactRow exactMatrix rowPivot).scalar ∧
            Approximation.Matrix.sampleMatrix
                (completeGeometricRow matrix rowPivot).inverse index =
              (completeExactRow exactMatrix rowPivot).inverse := by
        intro rowPivot
        apply geometricAggregate_sample
          (completeGeometricBranch matrix rowPivot)
          (completeExactBranch exactMatrix rowPivot)
          (fun columnPivot => geometricConj
            (completeGeometricBranch matrix rowPivot columnPivot).scalar)
          (fun columnPivot => Data.Gaussian.Basic.conj
            (completeExactBranch exactMatrix rowPivot columnPivot).scalar)
          index
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).1
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).2
        · intro columnPivot
          rw [geometricConj_sample,
            (branchSample rowPivot columnPivot).1]
      rw [completeApproximation_succ matrix,
        completeScaledInverse_succ exactMatrix]
      exact geometricAggregate_sample
        (completeGeometricRow matrix)
          (completeExactRow exactMatrix)
        (fun rowPivot =>
          geometricConj
            (completeGeometricRow matrix rowPivot).scalar)
        (fun rowPivot => Data.Gaussian.Basic.conj (completeExactRow
          exactMatrix rowPivot).scalar)
        index
        (fun rowPivot => (rowSample rowPivot).1)
        (fun rowPivot => (rowSample rowPivot).2)
        (fun rowPivot => by
          rw [geometricConj_sample, (rowSample rowPivot).1])

end

end Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
