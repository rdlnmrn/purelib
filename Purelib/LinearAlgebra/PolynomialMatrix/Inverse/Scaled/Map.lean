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
theorem map_schur (embedding : Embedding K L)
    (matrix : Basic.Matrix K (n + 1)) :
    mapMatrix embedding (Basic.schur matrix) =
      Basic.schur (mapMatrix embedding matrix) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  unfold Basic.schur
  rw [SquareMatrix.matrixOfFn_apply,
    SquareMatrix.matrixOfFn_apply]
  unfold Basic.head Basic.tail Basic.leftColumn
    Basic.topRow
  rw [
    SquareMatrix.matrixOfFn_apply,
    SquareMatrix.matrixOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    mapMatrix_apply, mapMatrix_apply, mapMatrix_apply, mapMatrix_apply]
  unfold mapPolynomial
  rw [(Dense.Map.map_sub embedding.toFun embedding.map_zero embedding.injective embedding.map_add embedding.map_neg),
    (Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add embedding.map_mul),
    (Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add embedding.map_mul)]

/-- Mapping coefficients commutes with polynomial matrix-vector multiplication.

The same field embedding maps both original inputs. It preserves every
pointwise product and the finite row sum, yielding the mapped structural
vector at each retained coordinate. -/
theorem map_matrixVector
    (embedding : Embedding K L)
    (matrix : Basic.Matrix K n) (vector : Basic.Vector K n) :
    mapVector embedding (Basic.matrixVector matrix vector) =
      Basic.matrixVector (mapMatrix embedding matrix) (mapVector embedding vector) := by
  apply Data.Vector.Basic.vector_ext
  intro row
  simp only [mapVector_apply, Basic.matrixVector,
    Data.Vector.Basic.vectorOfFn_apply]
  simpa only [mapMatrix_row] using map_dot embedding (matrix row) vector

/-- Mapping coefficients commutes with polynomial row-vector multiplication.

The same field embedding maps both original inputs. Each retained column
keeps its original ordered dot product, whose scalar products and finite sum
commute with the embedding. -/
theorem map_vectorMatrix
    (embedding : Embedding K L)
    (vector : Basic.Vector K n) (matrix : Basic.Matrix K n) :
    mapVector embedding (Basic.vectorMatrix vector matrix) =
      Basic.vectorMatrix (mapVector embedding vector) (mapMatrix embedding matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rw [mapVector_apply]
  unfold Basic.vectorMatrix
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply]
  rw [map_dot]
  apply congrArg (Basic.dot (mapVector embedding vector))
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [mapVector_apply, Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply, mapMatrix_apply]

/-- Mapping coefficients commutes with the symbolic block inverse formula.

The supplied smaller data agree under the same field embedding in both scalar and matrix components. -/
theorem map_blockInverse
    (embedding : Embedding K L)
    (matrix : Basic.Matrix K (n + 1))
    (smaller : Basic.ScaledInverseData K n)
    (smallerMapped : Basic.ScaledInverseData L n)
    (scalarEqual : mapPolynomial embedding smaller.scalar =
      smallerMapped.scalar)
    (inverseEqual : mapMatrix embedding smaller.inverse =
      smallerMapped.inverse) :
    mapMatrix embedding (Block.blockInverse matrix smaller) =
      Block.blockInverse (mapMatrix embedding matrix) smallerMapped := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [mapMatrix_apply]
  rw [Block.blockInverse_apply,
    Block.blockInverse_apply]
  rw [← scalarEqual, ← inverseEqual]
  rw [map_head, map_topRow, map_leftColumn]
  have matrixVectorEqual := map_matrixVector embedding
    smaller.inverse (Basic.leftColumn matrix)
  have vectorMatrixEqual := map_vectorMatrix embedding
    (Basic.topRow matrix) smaller.inverse
  have dotEqual := map_dot embedding (Basic.topRow matrix)
    (Basic.matrixVector smaller.inverse (Basic.leftColumn matrix))
  refine Data.Fin.cases_induction ?_ (fun row => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun column => ?_) column
    · simp only [Data.Fin.cases_zero]
      change mapPolynomial embedding
          (smaller.scalar + Basic.dot (Basic.topRow matrix)
            (Basic.matrixVector smaller.inverse (Basic.leftColumn matrix))) = _
      unfold mapPolynomial
      rw [(Dense.Map.map_add embedding.toFun embedding.map_zero embedding.injective embedding.map_add)]
      change mapPolynomial embedding smaller.scalar +
          mapPolynomial embedding
            (Basic.dot (Basic.topRow matrix)
              (Basic.matrixVector smaller.inverse (Basic.leftColumn matrix))) = _
      rw [dotEqual, matrixVectorEqual]
      rfl
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      change mapPolynomial embedding
          (-Basic.head matrix * Basic.vectorMatrix (Basic.topRow
            matrix)
            smaller.inverse column) = _
      unfold mapPolynomial
      rw [(Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add
        embedding.map_mul),
        (Dense.Map.map_neg embedding.toFun embedding.map_zero embedding.injective embedding.map_neg)]
      apply congrArg (fun value =>
        -mapPolynomial embedding (Basic.head matrix) * value)
      simpa only [mapPolynomial, mapVector_apply] using
        Data.Vector.Basic.vector_eq_at
          vectorMatrixEqual column
  · refine Data.Fin.cases_induction ?_ (fun column => ?_) column
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      change mapPolynomial embedding
          (-Basic.head matrix * Basic.matrixVector smaller.inverse
            (Basic.leftColumn matrix) row) = _
      unfold mapPolynomial
      rw [(Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add
        embedding.map_mul),
        (Dense.Map.map_neg embedding.toFun embedding.map_zero embedding.injective embedding.map_neg)]
      apply congrArg (fun value =>
        -mapPolynomial embedding (Basic.head matrix) * value)
      simpa only [mapPolynomial, mapVector_apply] using
        Data.Vector.Basic.vector_eq_at
          matrixVectorEqual row
    · simp only [Data.Fin.cases_succ]
      change mapPolynomial embedding
          ((Basic.head matrix * Basic.head matrix) *
            smaller.inverse row column) = _
      unfold mapPolynomial
      rw [(Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add
        embedding.map_mul),
        (Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add embedding.map_mul)]
      rewrite [mapMatrix_apply]
      exact Eq.refl _

/-- Mapping coefficients commutes with the complete fraction-free polynomial inverse recursion.

Both the retained scalar and inverse matrix agree under the same supplied field embedding. -/
theorem map_scaledInverseData
    (embedding : Embedding K L) :
    ∀ (n : Nat) (matrix : Basic.Matrix K n),
      mapPolynomial embedding (Compute.scaledInverseData n matrix).scalar =
          (Compute.scaledInverseData n (mapMatrix embedding matrix)).scalar ∧
        mapMatrix embedding (Compute.scaledInverseData n matrix).inverse =
          (Compute.scaledInverseData n (mapMatrix embedding matrix)).inverse
  | 0, _ => by
      constructor
      · exact (Dense.Map.map_constant embedding.toFun) 1
          |>.trans (congrArg Dense.Basic.DensePolynomial.constant embedding.map_one)
      · apply SquareMatrix.matrix_ext
        intro index
        exact Fin.elim0 index
  | n + 1, matrix => by
      let smaller := Compute.scaledInverseData n (Basic.schur matrix)
      let mappedSmaller := Compute.scaledInverseData n
        (Basic.schur (mapMatrix embedding matrix))
      have recursive := map_scaledInverseData embedding n (Basic.schur matrix)
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
      · dsimp only [Compute.scaledInverseData]
        unfold mapPolynomial at scalarEqual ⊢
        rw [(Dense.Map.map_mul embedding.toFun embedding.map_zero embedding.injective embedding.map_add
          embedding.map_mul), scalarEqual]
        change mapPolynomial embedding (Basic.head matrix) * mappedSmaller.scalar =
          Basic.head (mapMatrix embedding matrix) * mappedSmaller.scalar
        rw [map_head]
      · dsimp only [Compute.scaledInverseData]
        exact map_blockInverse embedding matrix smaller mappedSmaller
          scalarEqual inverseEqual

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Map
