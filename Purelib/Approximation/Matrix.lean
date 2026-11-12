module

import Purelib.Data.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Schur
import Purelib.LinearAlgebra.Vector.Dot
import Init.Data.Fin.Basic
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra.Matrix.Inverse.Scaled

/-!
# Synchronized finite matrix approximations

This file provides a small constructive algebra of Gaussian-rational sample
streams whose error allowance is an explicit quarter-power schedule.  Unlike
wrapping an intermediate CCL name and sampling it again, these operations
preserve the same finite sample index through every polynomial operation.

The final construction mirrors the total division-free scaled-inverse
algorithm in `Purelib.LinearAlgebra`.  It therefore produces finite
approximations to the canonical scalar and adjugate of every finite named
matrix without making an invertibility decision or choosing a completed
value.
-/

namespace Purelib.Approximation

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Gaussian.Geometric
open Purelib.LinearAlgebra renaming Matrix -> ExactMatrix

public section
/-- The original finite matrix representation at the displayed entry type and dimension. -/
abbrev Matrix (value : Type) (size : Nat) :=
  ExactMatrix value size
namespace Matrix

/-- A finite coordinate function at the displayed entry type and dimension. -/
abbrev Vector (value : Type) (size : Nat) := Fin size -> value

/-- A finite square matrix of synchronized Gaussian approximations. -/
abbrev GeometricMatrix (size : Nat) := Matrix GeometricApproximation size

/-- Evaluate every entry of a synchronized matrix at one finite index. -/
@[expose] def sampleMatrix {size : Nat} (matrix : GeometricMatrix size)
    (index : Nat) : Matrix Data.Gaussian.Basic.Canonical size :=
  ExactMatrix.matrixOfFn fun row column =>
    (matrix row column).sample index

/-- Sampling a synchronized matrix reads the original entry at the same finite index. -/
@[simp] theorem sampleMatrix_apply {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) (row column : Fin size) :
    sampleMatrix matrix index row column =
      (matrix row column).sample index :=
  ExactMatrix.matrixOfFn_apply _ _ _

/-- The division-free Schur matrix, computed in synchronized approximation arithmetic. -/
@[expose] def schur {size : Nat} (matrix : GeometricMatrix (size + 1)) :
    GeometricMatrix size :=
  ExactMatrix.matrixOfFn fun row column =>
    GeometricApproximation.sub
      (GeometricApproximation.mul (matrix 0 0)
        (matrix row.succ column.succ))
      (GeometricApproximation.mul (matrix row.succ 0)
        (matrix 0 column.succ))

/-- Each synchronized Schur entry is the pivot times the trailing entry minus the matching column-row product. -/
@[simp] theorem schur_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1)) (row column : Fin size) :
    schur matrix row column =
      GeometricApproximation.sub
        (GeometricApproximation.mul (matrix 0 0)
          (matrix row.succ column.succ))
        (GeometricApproximation.mul (matrix row.succ 0)
          (matrix 0 column.succ)) :=
  ExactMatrix.matrixOfFn_apply _ _ _

/-- Sampling commutes with the synchronized division-free Schur construction.

Each finite entry retains the same pivot and matching row-column product.
Sampling their scalar multiplication and subtraction gives the Gaussian Schur
entry at the original sample index. -/
theorem sampleMatrix_schur {size : Nat}
    (matrix : GeometricMatrix (size + 1)) (index : Nat) :
    sampleMatrix (schur matrix) index =
      ExactMatrix.Schur.schur (sampleMatrix matrix index) := by
  apply ExactMatrix.matrix_ext
  intro row column
  rw [sampleMatrix_apply, schur_apply,
    ExactMatrix.Schur.schur_apply]
  rewrite [GeometricApproximation.sub_sample,
    GeometricApproximation.mul_sample, GeometricApproximation.mul_sample,
    ExactMatrix.Blocks.head,
    ExactMatrix.Blocks.tail_apply,
    ExactMatrix.Blocks.leftColumn_apply,
    ExactMatrix.Blocks.topRow_apply, sampleMatrix_apply,
    sampleMatrix_apply, sampleMatrix_apply,
    sampleMatrix_apply]
  exact Eq.refl _

/-- Matrix-vector multiplication in synchronized approximation arithmetic. -/
@[expose] def matrixVector {size : Nat} (matrix : GeometricMatrix size)
    (vector : Approximation.Matrix.Vector GeometricApproximation size) :
    Approximation.Matrix.Vector GeometricApproximation size := fun row =>
  GeometricApproximation.sum fun column =>
    GeometricApproximation.mul (matrix row column) (vector column)

/-- Vector-matrix multiplication in synchronized approximation arithmetic. -/
@[expose] def vectorMatrix {size : Nat} (vector : Approximation.Matrix.Vector GeometricApproximation
  size)
    (matrix : GeometricMatrix size) : Approximation.Matrix.Vector
      GeometricApproximation size :=
  fun column => GeometricApproximation.sum fun row =>
    GeometricApproximation.mul (vector row) (matrix row column)

/-- Dot product in synchronized approximation arithmetic. -/
@[expose] def dot {size : Nat} (left right : Approximation.Matrix.Vector GeometricApproximation size)
  :
    GeometricApproximation :=
  GeometricApproximation.sum fun index =>
    GeometricApproximation.mul (left index) (right index)

/-- Evaluate a synchronized vector at one finite index. -/
@[expose] def sampleVector {size : Nat} (vector : Approximation.Matrix.Vector GeometricApproximation
  size)
    (index : Nat) : Data.Vector Data.Gaussian.Basic.Canonical size :=
  Data.Vector.Basic.vectorOfFn fun entry =>
    (vector entry).sample index

/-- Sampling a synchronized vector reads the original coordinate at the same finite index. -/
@[simp] theorem sampleVector_apply {size : Nat}
    (vector : Approximation.Matrix.Vector GeometricApproximation size) (index : Nat)
    (entry : Fin size) :
    sampleVector vector index entry = (vector entry).sample index :=
  Data.Vector.Basic.vectorOfFn_apply _ _

/-- Sampling a synchronized matrix-vector product gives the same-index Gaussian product.

The finite sum keeps its original column indices. Each retained summand samples
the original matrix entry and vector coordinate before their scalar product. -/
@[simp] theorem matrixVector_sample {size : Nat}
    (matrix : GeometricMatrix size)
    (vector : Approximation.Matrix.Vector GeometricApproximation size) (index : Nat)
    (row : Fin size) :
    (matrixVector matrix vector row).sample index =
      ExactMatrix.Multiplication.matrixVector
        (sampleMatrix matrix index) (sampleVector vector index) row := by
  rw [ExactMatrix.Multiplication.matrixVector_apply]
  unfold matrixVector
  rw [GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rewrite [GeometricApproximation.mul_sample, sampleMatrix_apply,
    sampleVector_apply]
  exact Eq.refl _

/-- Sampling a synchronized vector-matrix product gives the same-index Gaussian product.

The finite sum keeps its original row indices. Each retained summand samples
the original vector coordinate and matrix entry before their scalar product. -/
@[simp] theorem vectorMatrix_sample {size : Nat}
    (vector : Approximation.Matrix.Vector GeometricApproximation size)
    (matrix : GeometricMatrix size) (index : Nat)
    (column : Fin size) :
    (vectorMatrix vector matrix column).sample index =
      ExactMatrix.Multiplication.vectorMatrix
        (sampleVector vector index) (sampleMatrix matrix index) column := by
  rw [ExactMatrix.Multiplication.vectorMatrix_apply]
  unfold vectorMatrix
  rw [GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rewrite [GeometricApproximation.mul_sample, sampleMatrix_apply,
    sampleVector_apply]
  exact Eq.refl _

open Purelib.LinearAlgebra.Vector in
/-- Sampling a synchronized dot product gives the dot product of the same-index samples.

The original finite coordinates index both vectors and their product summands.
Sampling commutes with the retained finite sum and each scalar multiplication. -/
@[simp] theorem dot_sample {size : Nat}
    (left right : Approximation.Matrix.Vector GeometricApproximation size) (index : Nat) :
    (dot left right).sample index =
      Dot.dot
        (sampleVector left index) (sampleVector right index) := by
  unfold dot Dot.dot
  rw [GeometricApproximation.sum_sample]
  apply FiniteSum.Fin.sumFin_congr
  intro entry
  rewrite [GeometricApproximation.mul_sample, sampleVector_apply,
    sampleVector_apply]
  exact Eq.refl _

set_option genInjectivity false in
/-- The synchronized scalar and matrix data of a fraction-free inverse.

The original geometric scalar and dimension-indexed matrix are retained together.
The record asserts no invertibility or completed matrix value. -/
structure ScaledInverseApproximation (size : Nat) where
  /-- The retained geometric approximation to the fraction-free scalar factor. -/ scalar :
    GeometricApproximation
  /-- The retained synchronized finite matrix approximation to the scaled inverse. -/ inverse :
    GeometricMatrix size

constructive_injectivity ScaledInverseApproximation

end Matrix

namespace Matrix.ScaledInverseApproximation.mk

end Matrix.ScaledInverseApproximation.mk

namespace Matrix

/-- Extend a synchronized fraction-free inverse by one leading row and column.

The original pivot, row, column, two matrix products and corner are retained as
local caches. Finite coordinate dispatch selects the same leading corner, two
edges or trailing block from those cached values. -/
@[expose] def blockInverse {size : Nat} (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) :
    GeometricMatrix (size + 1) :=
  let a := matrix 0 0
  let row : Approximation.Matrix.Vector GeometricApproximation size := fun column =>
    matrix 0 column.succ
  let column : Approximation.Matrix.Vector GeometricApproximation size := fun row =>
    matrix row.succ 0
  let inverseColumn := matrixVector smaller.inverse column
  let rowInverse := vectorMatrix row smaller.inverse
  let corner := GeometricApproximation.add smaller.scalar
    (dot row inverseColumn)
  ExactMatrix.matrixOfFn fun i j => Data.Fin.cases
    (Data.Fin.cases corner (fun columnIndex =>
      GeometricApproximation.mul (GeometricApproximation.neg a)
        (rowInverse columnIndex)) j)
    (fun rowIndex => Data.Fin.cases
      (GeometricApproximation.mul (GeometricApproximation.neg a)
        (inverseColumn rowIndex))
      (fun columnIndex =>
        GeometricApproximation.mul
          (GeometricApproximation.mul a a)
          (smaller.inverse rowIndex columnIndex)) j) i

/-- Read the synchronized block inverse by its leading corner, edges or trailing block.

The two original finite indices select their retained predecessor coordinates.
Each branch reads the same cached products and scalar factors as the block
construction. -/
@[simp] theorem blockInverse_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size)
    (row column : Fin (size + 1)) :
    blockInverse matrix smaller row column =
      Data.Fin.cases
        (Data.Fin.cases
          (GeometricApproximation.add smaller.scalar
            (dot (fun entry => matrix 0 entry.succ)
              (matrixVector smaller.inverse
                (fun entry => matrix entry.succ 0))))
          (fun columnIndex =>
            GeometricApproximation.mul
              (GeometricApproximation.neg (matrix 0 0))
              (vectorMatrix (fun entry => matrix 0 entry.succ)
                smaller.inverse columnIndex)) column)
        (fun rowIndex => Data.Fin.cases
          (GeometricApproximation.mul
            (GeometricApproximation.neg (matrix 0 0))
            (matrixVector smaller.inverse
              (fun entry => matrix entry.succ 0) rowIndex))
          (fun columnIndex =>
            GeometricApproximation.mul
              (GeometricApproximation.mul (matrix 0 0) (matrix 0 0))
              (smaller.inverse rowIndex columnIndex)) column) row := by
  unfold blockInverse
  rw [ExactMatrix.matrixOfFn_apply]

/-- The sampled synchronized block extension equals the exact Gaussian block inverse.

The supplied smaller scalar and entries agree with the exact data at the same
sample index. The original geometric and exact block constructions then select
the same four finite block values at each retained row and column. -/
theorem sampleMatrix_blockInverse {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) (index : Nat)
    (exactSmaller : Basic.ScaledInverse
      (ExactMatrix.Schur.schur (sampleMatrix matrix index)))
    (scalarSample : smaller.scalar.sample index = exactSmaller.scalar)
    (inverseSample : forall row column,
      (smaller.inverse row column).sample index =
        exactSmaller.inverse row column) :
    sampleMatrix (blockInverse matrix smaller) index =
      Block.blockInverse
        (sampleMatrix matrix index) exactSmaller := by
  have inverseMatrixSample :
      sampleMatrix smaller.inverse index = exactSmaller.inverse := by
    apply ExactMatrix.matrix_ext
    intro row column
    rw [sampleMatrix_apply, inverseSample]
  have rowSample :
      sampleVector (fun entry : Fin size => matrix 0 entry.succ) index =
        ExactMatrix.Blocks.topRow
          (sampleMatrix matrix index) := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [sampleVector_apply,
      ExactMatrix.Blocks.topRow_apply, sampleMatrix_apply]
  have columnSample :
      sampleVector (fun entry : Fin size => matrix entry.succ 0) index =
        ExactMatrix.Blocks.leftColumn
          (sampleMatrix matrix index) := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [sampleVector_apply,
      ExactMatrix.Blocks.leftColumn_apply, sampleMatrix_apply]
  have inverseColumnSample :
      sampleVector
          (matrixVector smaller.inverse
            (fun entry : Fin size => matrix entry.succ 0)) index =
        ExactMatrix.Multiplication.matrixVector exactSmaller.inverse
          (ExactMatrix.Blocks.leftColumn
            (sampleMatrix matrix index)) := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [sampleVector_apply, matrixVector_sample,
      inverseMatrixSample, columnSample]
  have rowInverseSample :
      sampleVector
          (vectorMatrix (fun entry : Fin size => matrix 0 entry.succ)
            smaller.inverse) index =
        ExactMatrix.Multiplication.vectorMatrix
          (ExactMatrix.Blocks.topRow
            (sampleMatrix matrix index)) exactSmaller.inverse := by
    apply Data.Vector.Basic.vector_ext
    intro entry
    rw [sampleVector_apply, vectorMatrix_sample,
      inverseMatrixSample, rowSample]
  apply ExactMatrix.matrix_ext
  intro row column
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rw [sampleMatrix_apply, blockInverse_apply,
        Block.blockInverse_apply]
      rewrite [Data.Fin.cases_zero, Data.Fin.cases_zero,
        Data.Fin.cases_zero, Data.Fin.cases_zero]
      rw [GeometricApproximation.add_sample, scalarSample, dot_sample,
        rowSample, inverseColumnSample]
    · rw [sampleMatrix_apply, blockInverse_apply,
        Block.blockInverse_apply]
      rewrite [Data.Fin.cases_zero, Data.Fin.cases_succ,
        Data.Fin.cases_zero, Data.Fin.cases_succ]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [GeometricApproximation.neg_sample,
        ExactMatrix.Blocks.head, sampleMatrix_apply]
      have entrySample := Data.Vector.Basic.vector_eq_at
        rowInverseSample columnIndex
      rw [sampleVector_apply] at entrySample
      rw [entrySample]
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · rw [sampleMatrix_apply, blockInverse_apply,
        Block.blockInverse_apply]
      rewrite [Data.Fin.cases_succ, Data.Fin.cases_zero,
        Data.Fin.cases_succ, Data.Fin.cases_zero]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [GeometricApproximation.neg_sample,
        ExactMatrix.Blocks.head, sampleMatrix_apply]
      have entrySample := Data.Vector.Basic.vector_eq_at
        inverseColumnSample rowIndex
      rw [sampleVector_apply] at entrySample
      rw [entrySample]
    · rw [sampleMatrix_apply, blockInverse_apply,
        Block.blockInverse_apply]
      rewrite [Data.Fin.cases_succ, Data.Fin.cases_succ,
        Data.Fin.cases_succ, Data.Fin.cases_succ]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [ExactMatrix.Blocks.head, sampleMatrix_apply,
        inverseSample, pow_two]

/-- Construct the synchronized fraction-free inverse by finite matrix-size recursion.

The empty matrix retains its exact unit scalar. Each successor step recursively
uses the original synchronized Schur matrix and passes that retained smaller
result to the same division-free block extension. -/
@[expose] def scaledInverse : {size : Nat} -> GeometricMatrix size ->
    ScaledInverseApproximation size
  | 0, _ =>
      { scalar := GeometricApproximation.exact 1
        inverse := ExactMatrix.matrixOfFn fun row =>
          Fin.elim0 row }
  | _size + 1, matrix =>
      let smaller := scaledInverse (schur matrix)
      { scalar := GeometricApproximation.mul (matrix 0 0) smaller.scalar
        inverse := blockInverse matrix smaller }

/-- Sampling the synchronized recursion gives the canonical same-index scaled inverse.

Structural induction follows the original matrix dimension. Each successor step
uses the retained smaller Schur result and the scalar and entry sampling laws
for the same block extension, without an invertibility assumption. -/
theorem scaledInverse_sample : forall {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat),
    ((scaledInverse matrix).scalar.sample index =
        (Compute.scaledInverse
          (sampleMatrix matrix index)).scalar) ∧
      sampleMatrix (scaledInverse matrix).inverse index =
        (Compute.scaledInverse
          (sampleMatrix matrix index)).inverse
  | 0, matrix, index => by
      constructor
      · rfl
      · apply ExactMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
  | size + 1, matrix, index => by
      let smaller := scaledInverse (schur matrix)
      let exactSmaller := Compute.scaledInverse
        (ExactMatrix.Schur.schur (sampleMatrix matrix index))
      have smallerSample := scaledInverse_sample (schur matrix) index
      rw [sampleMatrix_schur] at smallerSample
      constructor
      · change
          (GeometricApproximation.mul
              (matrix 0 0) smaller.scalar).sample index =
            (Block.extendScaledInverse
              (sampleMatrix matrix index) exactSmaller).scalar
        rw [GeometricApproximation.mul_sample]
        change (matrix 0 0).sample index * smaller.scalar.sample index =
          ExactMatrix.Blocks.head
              (sampleMatrix matrix index) * exactSmaller.scalar
        rw [smallerSample.1]
        rfl
      · change sampleMatrix (blockInverse matrix smaller) index =
          (Block.extendScaledInverse
            (sampleMatrix matrix index) exactSmaller).inverse
        change sampleMatrix (blockInverse matrix smaller) index =
          Block.blockInverse
            (sampleMatrix matrix index) exactSmaller
        apply sampleMatrix_blockInverse matrix smaller index exactSmaller
          smallerSample.1
        intro row column
        have entrySample := ExactMatrix.matrix_eq_at
          smallerSample.2 row column
        rewrite [sampleMatrix_apply] at entrySample
        exact entrySample

/-- The synchronized scalar sample equals the canonical Gaussian fraction-free scalar at the same source index. -/
theorem scaledInverse_scalar_sample {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) :
    (scaledInverse matrix).scalar.sample index =
      (Compute.scaledInverse
        (sampleMatrix matrix index)).scalar :=
  (scaledInverse_sample matrix index).1

/-- Each synchronized inverse entry sample equals the canonical same-index inverse entry.

Read the retained row and column from the matrix equality for the synchronized
recursion. Both entries use the same finite indices and source sample. -/
theorem scaledInverse_inverse_sample {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) (row column : Fin size) :
    ((scaledInverse matrix).inverse row column).sample index =
      (Compute.scaledInverse
        (sampleMatrix matrix index)).inverse row column :=
  by
    have entrySample := ExactMatrix.matrix_eq_at
      (scaledInverse_sample matrix index).2 row column
    rewrite [sampleMatrix_apply] at entrySample
    exact entrySample

end Matrix

end

section

namespace Matrix

/-- The exact two-by-two synchronized Gaussian approximation matrix type. -/
public abbrev GeometricMatrix2 := GeometricMatrix 2

end Matrix

end
end Purelib.Approximation
