module
import Purelib.Data.Fin
import Purelib.Algebra.Field.Embedding
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Map

import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.PolynomialMatrix.Map

/-!
# Coefficient maps for polynomial-valued matrix recursion

An injective explicit-field embedding commutes with every finite sum, Schur
complement, block-inverse clause, and the complete fraction-free scaled
inverse recursion.  The proofs are pointwise finite-matrix calculations.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Map

open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.Polynomial
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Map

public section
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {K L : Type*}
  [ExplicitField K] [DecidableEq K]
  [ExplicitField L] [DecidableEq L]

/-- Mapping coefficients through a field embedding commutes with the Schur complement.

The embedding preserves subtraction and multiplication in each displayed
entry. The pivot, tail, leading row and leading column retain their original
finite coordinates under entrywise mapping. -/
theorem map_schur (embedding : Algebra.Field.Embedding K L)
    (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
    mapMatrix embedding (PolynomialMatrix.Basic.schur matrix) =
      PolynomialMatrix.Basic.schur (mapMatrix embedding matrix) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  unfold PolynomialMatrix.Basic.schur
  rw [SquareMatrix.matrixOfFn_apply,
    SquareMatrix.matrixOfFn_apply]
  unfold PolynomialMatrix.Basic.head PolynomialMatrix.Basic.tail PolynomialMatrix.Basic.leftColumn
    PolynomialMatrix.Basic.topRow
  rw [
    SquareMatrix.matrixOfFn_apply,
    SquareMatrix.matrixOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    mapMatrix_apply, mapMatrix_apply, mapMatrix_apply, mapMatrix_apply]
  unfold mapPolynomial
  rw [Dense.Map.map_sub,
    Dense.Map.map_mul,
    Dense.Map.map_mul]

/-- Mapping coefficients commutes with polynomial matrix-vector multiplication.

The same field embedding maps both original inputs. It preserves every
pointwise product and the finite row sum, yielding the mapped structural
vector at each retained coordinate. -/
theorem map_matrixVector
    (embedding : Algebra.Field.Embedding K L)
    (matrix : PolynomialMatrix.Basic.Matrix K n) (vector : PolynomialMatrix.Basic.Vector K n) :
    mapVector embedding (PolynomialMatrix.Basic.matrixVector matrix vector) =
      PolynomialMatrix.Basic.matrixVector (mapMatrix embedding matrix) (mapVector embedding vector) := by
  apply Data.Vector.Basic.vector_ext
  intro row
  simp only [mapVector_apply, PolynomialMatrix.Basic.matrixVector,
    Data.Vector.Basic.vectorOfFn_apply]
  simpa only [mapMatrix_row] using map_dot embedding (matrix row) vector

/-- Mapping coefficients commutes with polynomial row-vector multiplication.

The same field embedding maps both original inputs. Each retained column
keeps its original ordered dot product, whose scalar products and finite sum
commute with the embedding. -/
theorem map_vectorMatrix
    (embedding : Algebra.Field.Embedding K L)
    (vector : PolynomialMatrix.Basic.Vector K n) (matrix : PolynomialMatrix.Basic.Matrix K n) :
    mapVector embedding (PolynomialMatrix.Basic.vectorMatrix vector matrix) =
      PolynomialMatrix.Basic.vectorMatrix (mapVector embedding vector) (mapMatrix embedding matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rw [mapVector_apply]
  unfold PolynomialMatrix.Basic.vectorMatrix
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply]
  rw [map_dot]
  apply congrArg (PolynomialMatrix.Basic.dot (mapVector embedding vector))
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [mapVector_apply, Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply, mapMatrix_apply]

/-- Mapping coefficients commutes with the symbolic block inverse formula.

The supplied smaller data agree under the same field embedding in both scalar and matrix components. -/
theorem map_blockInverse
    (embedding : Algebra.Field.Embedding K L)
    (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (smaller : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n)
    (smallerMapped : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData L n)
    (scalarEqual : mapPolynomial embedding smaller.scalar =
      smallerMapped.scalar)
    (inverseEqual : mapMatrix embedding smaller.inverse =
      smallerMapped.inverse) :
    mapMatrix embedding (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix smaller) =
      PolynomialMatrix.Inverse.Scaled.Block.blockInverse (mapMatrix embedding matrix) smallerMapped := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  unfold PolynomialMatrix.Inverse.Scaled.Block.blockInverse
  rw [SquareMatrix.matrixOfFn_apply,
    SquareMatrix.matrixOfFn_apply]
  rw [← scalarEqual, ← inverseEqual]
  rw [map_head, map_topRow, map_leftColumn]
  have matrixVectorEqual := map_matrixVector embedding
    smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix)
  have vectorMatrixEqual := map_vectorMatrix embedding
    (PolynomialMatrix.Basic.topRow matrix) smaller.inverse
  have dotEqual := map_dot embedding (PolynomialMatrix.Basic.topRow matrix)
    (PolynomialMatrix.Basic.matrixVector smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix))
  refine Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun column => ?_) column
    · simp only [Data.Fin.cases_zero]
      change mapPolynomial embedding
          (smaller.scalar + PolynomialMatrix.Basic.dot (PolynomialMatrix.Basic.topRow matrix)
            (PolynomialMatrix.Basic.matrixVector smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix))) = _
      unfold mapPolynomial
      rw [Dense.Map.map_add]
      change mapPolynomial embedding smaller.scalar +
          mapPolynomial embedding
            (PolynomialMatrix.Basic.dot (PolynomialMatrix.Basic.topRow matrix)
              (PolynomialMatrix.Basic.matrixVector smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix))) = _
      rw [dotEqual, matrixVectorEqual]
      rfl
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      change mapPolynomial embedding
          (-PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.vectorMatrix (PolynomialMatrix.Basic.topRow
            matrix)
            smaller.inverse column) = _
      unfold mapPolynomial
      rw [Dense.Map.map_mul,
        Dense.Map.map_neg]
      apply congrArg (fun value =>
        -mapPolynomial embedding (PolynomialMatrix.Basic.head matrix) * value)
      simpa only [mapPolynomial, mapVector_apply] using
        Data.Vector.Basic.vector_eq_at
          vectorMatrixEqual column
  · refine Data.Fin.cases_induction ?_ (fun column => ?_) column
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      change mapPolynomial embedding
          (-PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.matrixVector smaller.inverse
            (PolynomialMatrix.Basic.leftColumn matrix) row) = _
      unfold mapPolynomial
      rw [Dense.Map.map_mul,
        Dense.Map.map_neg]
      apply congrArg (fun value =>
        -mapPolynomial embedding (PolynomialMatrix.Basic.head matrix) * value)
      simpa only [mapPolynomial, mapVector_apply] using
        Data.Vector.Basic.vector_eq_at
          matrixVectorEqual row
    · simp only [Data.Fin.cases_succ]
      change mapPolynomial embedding
          ((PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.head matrix) *
            smaller.inverse row column) = _
      unfold mapPolynomial
      rw [Dense.Map.map_mul,
        Dense.Map.map_mul]
      rewrite [mapMatrix_apply]
      exact Eq.refl _

/-- Mapping coefficients commutes with the complete fraction-free polynomial inverse recursion.

Both the retained scalar and inverse matrix agree under the same supplied field embedding. -/
theorem map_scaledInverseData
    (embedding : Algebra.Field.Embedding K L) :
    ∀ (n : Nat) (matrix : PolynomialMatrix.Basic.Matrix K n),
      mapPolynomial embedding (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix).scalar =
          (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n (mapMatrix embedding matrix)).scalar ∧
        mapMatrix embedding (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix).inverse =
          (PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n (mapMatrix embedding matrix)).inverse
  | 0, _ => by
      constructor
      · exact Dense.Map.map_constant embedding 1
          |>.trans (congrArg Dense.Basic.DensePolynomial.constant embedding.map_one)
      · apply SquareMatrix.matrix_ext
        intro index
        exact Fin.elim0 index
  | n + 1, matrix => by
      let smaller := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n (PolynomialMatrix.Basic.schur matrix)
      let mappedSmaller := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n
        (PolynomialMatrix.Basic.schur (mapMatrix embedding matrix))
      have recursive := map_scaledInverseData embedding n (PolynomialMatrix.Basic.schur matrix)
      have schurEqual := map_schur embedding matrix
      have scalarEqual : mapPolynomial embedding smaller.scalar =
          mappedSmaller.scalar := by
        dsimp only [smaller, mappedSmaller]
        rw [← schurEqual]
        exact recursive.1
      have inverseEqual : mapMatrix embedding smaller.inverse =
          mappedSmaller.inverse := by
        dsimp only [smaller, mappedSmaller]
        rw [← schurEqual]
        exact recursive.2
      constructor
      · dsimp only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData]
        unfold mapPolynomial at scalarEqual ⊢
        rw [Polynomial.Dense.Map.map_mul, scalarEqual]
        change mapPolynomial embedding (PolynomialMatrix.Basic.head matrix) * mappedSmaller.scalar =
          PolynomialMatrix.Basic.head (mapMatrix embedding matrix) * mappedSmaller.scalar
        rw [map_head]
      · dsimp only [PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData]
        exact map_blockInverse embedding matrix smaller mappedSmaller
          scalarEqual inverseEqual

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Map
