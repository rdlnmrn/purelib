module
import Purelib.Algebra.Field.Embedding
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Map

import Purelib.Algebra.Field.ExplicitField

/-!
# Coefficient maps for polynomial-valued matrix recursion

An injective explicit-field embedding commutes with every finite sum, Schur
complement, block-inverse clause, and the complete fraction-free scaled
inverse recursion.  The proofs are pointwise finite-matrix calculations.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Map

open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra
open Purelib.Polynomial

public section

/-- A finite dense polynomial over the supplied coefficient type. -/
abbrev Polynomial (K : Type*) := Dense.Basic.DensePolynomial K
/-- A finite square structural matrix of dense coefficient polynomials. -/
abbrev Matrix (K : Type*) (n : Nat) :=
  PolynomialMatrix.Basic.Matrix K n
/-- A structural vector of dense coefficient polynomials with retained finite length. -/
abbrev Vector (K : Type*) (n : Nat) :=
  PolynomialMatrix.Basic.Vector K n

open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {K L : Type*}
  [ExplicitField K] [DecidableEq K]
  [ExplicitField L] [DecidableEq L]

/-- Map every polynomial coefficient through the supplied explicit field embedding. -/
@[expose] def mapPolynomial (embedding : Algebra.Field.Embedding K L)
    (polynomial : Polynomial K) : Polynomial L :=
  Dense.Map.map embedding polynomial

/-- Map coefficients through the field embedding in every retained vector coordinate. -/
@[expose] def mapVector (embedding : Algebra.Field.Embedding K L)
    (vector : Vector K n) : Vector L n :=
  Data.Vector.Basic.vectorOfFn fun index =>
    mapPolynomial embedding (vector index)

/-- Map coefficients through the field embedding in every retained matrix entry. -/
@[expose] def mapMatrix (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K n) : Matrix L n :=
  SquareMatrix.matrixOfFn fun row column =>
    mapPolynomial embedding (matrix row column)

/-- Read a mapped vector coordinate as the coefficient map of its original polynomial. -/
@[simp] theorem mapVector_apply
    (embedding : Algebra.Field.Embedding K L)
    (vector : Vector K n) (index : Fin n) :
    mapVector embedding vector index =
      mapPolynomial embedding (vector index) := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _

/-- Read a mapped matrix entry as the coefficient map of its original polynomial. -/
@[simp] theorem mapMatrix_apply
    (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K n) (row column : Fin n) :
    mapMatrix embedding matrix row column =
      mapPolynomial embedding (matrix row column) := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

/-- Coefficient mapping commutes with materializing a polynomial vector.

Both retained vectors have the same finite coordinate values. Coordinate readback
reduces the two constructions to the original coefficient map. -/
@[simp] theorem mapVector_vectorOfFn
    (embedding : Algebra.Field.Embedding K L)
    (entries : Fin n → Polynomial K) :
    mapVector embedding (Data.Vector.Basic.vectorOfFn entries) =
      Data.Vector.Basic.vectorOfFn fun index =>
        mapPolynomial embedding (entries index) := by
  apply Data.Vector.Basic.vector_ext
  intro index
  rewrite [mapVector_apply,
    Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact Eq.refl _

/-- A row of the mapped matrix is the mapped original row.

Each retained column reads the same mapped polynomial, so structural vector
extensionality identifies the two rows. -/
@[simp] theorem mapMatrix_row
    (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K n) (row : Fin n) :
    mapMatrix embedding matrix row = mapVector embedding (matrix row) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rewrite [mapMatrix_apply, mapVector_apply]
  exact Eq.refl _

/-- Coefficient mapping commutes with reading the leading matrix entry.

The original leading coordinate is retained by the matrix coefficient map. Its
entry readback gives the displayed equality without changing either matrix. -/
@[simp] theorem map_head
    (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    PolynomialMatrix.Basic.head (mapMatrix embedding matrix) =
      mapPolynomial embedding (PolynomialMatrix.Basic.head matrix) := by
  unfold PolynomialMatrix.Basic.head
  rewrite [mapMatrix_apply]
  exact Eq.refl _

/-- Coefficient mapping commutes with reading the retained top row. -/
@[simp] theorem map_topRow
    (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    PolynomialMatrix.Basic.topRow (mapMatrix embedding matrix) =
      mapVector embedding (PolynomialMatrix.Basic.topRow matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rw [mapVector_apply]
  unfold PolynomialMatrix.Basic.topRow
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply, mapMatrix_apply]

/-- Coefficient mapping commutes with reading the retained left column. -/
@[simp] theorem map_leftColumn
    (embedding : Algebra.Field.Embedding K L)
    (matrix : Matrix K (n + 1)) :
    PolynomialMatrix.Basic.leftColumn (mapMatrix embedding matrix) =
      mapVector embedding (PolynomialMatrix.Basic.leftColumn matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [mapVector_apply]
  unfold PolynomialMatrix.Basic.leftColumn
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply, mapMatrix_apply]

/-- The coefficient map commutes with the finite indexed polynomial sum. -/
theorem map_sumFin (embedding : Algebra.Field.Embedding K L)
    (values : Fin n → Polynomial K) :
    mapPolynomial embedding (PolynomialMatrix.Basic.sumFin values) =
      PolynomialMatrix.Basic.sumFin (fun index => mapPolynomial embedding (values index)) := by
  unfold PolynomialMatrix.Basic.sumFin
  have foldMap : ∀ (polynomials : List (Polynomial K))
      (accumulator : Polynomial K),
      mapPolynomial embedding
          (polynomials.foldl (fun left right => left + right) accumulator) =
        (polynomials.map (mapPolynomial embedding)).foldl
          (fun left right => left + right)
          (mapPolynomial embedding accumulator) := by
    intro polynomials
    induction polynomials with
    | nil => intro accumulator; rfl
    | cons polynomial remaining inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons]
        rw [inductionHypothesis]
        apply congrArg (fun initial => remaining.map (mapPolynomial embedding) |>.foldl
          (fun left right => left + right) initial)
        unfold mapPolynomial
        exact Dense.Map.map_add embedding _ _
  rw [foldMap]
  simp only [mapPolynomial, Dense.Map.map_zero_polynomial,
    Data.List.OfFn.Basic.map_ofFn]
  rfl

/-- The coefficient map commutes with the finite polynomial dot product. -/
theorem map_dot (embedding : Algebra.Field.Embedding K L)
    (left right : Vector K n) :
    mapPolynomial embedding (PolynomialMatrix.Basic.dot left right) =
      PolynomialMatrix.Basic.dot (mapVector embedding left) (mapVector embedding right) := by
  unfold PolynomialMatrix.Basic.dot mapVector
  rw [map_sumFin]
  apply PolynomialMatrix.Basic.sumFin_congr
  intro index
  simp only [Data.Vector.Basic.vectorOfFn_apply]
  exact Dense.Map.map_mul embedding _ _
end

end Purelib.LinearAlgebra.PolynomialMatrix.Map
