module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.LinearAlgebra.Matrix.Schur
public import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.Vector.Dot
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs

open Purelib.Polynomial.Dense.Basic

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Evaluation

open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Vector
open Purelib.Polynomial
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Evaluate every polynomial of a structural vector at one supplied coefficient value. -/
@[expose] def evalVector (t : K) (vector : Basic.Vector K n) :
    Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun i => (vector i).eval t

/-- Evaluate every polynomial entry of a structural square matrix at one supplied coefficient value. -/
@[expose] def evalMatrix (t : K) (matrix : Basic.Matrix K n) :
    SquareMatrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    (matrix row column).eval t

omit [DecidableEq K] in
/-- Read an evaluated vector coordinate as evaluation of its original polynomial. -/
@[simp] theorem evalVector_apply (t : K) (vector : Basic.Vector K n)
    (index : Fin n) :
    evalVector t vector index = (vector index).eval t := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _

omit [DecidableEq K] in
/-- Read an evaluated matrix entry as evaluation of its original polynomial. -/
@[simp] theorem evalMatrix_apply (t : K) (matrix : Basic.Matrix K n)
    (row column : Fin n) :
    evalMatrix t matrix row column = (matrix row column).eval t := by
  exact SquareMatrix.matrixOfFn_apply _ _ _

omit [DecidableEq K] in
/-- Evaluation commutes with materializing a vector from a polynomial entry function.

The original finite entry function and the evaluated structural vector read
the same scalar at each retained coordinate. -/
@[simp] theorem evalVector_vectorOfFn (t : K)
    (entries : Fin n → Basic.Polynomial K) :
    evalVector t (Data.Vector.Basic.vectorOfFn entries) =
      Data.Vector.Basic.vectorOfFn fun index =>
        (entries index).eval t := by
  apply Data.Vector.Basic.vector_ext
  intro index
  rewrite [evalVector_apply,
    Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact Eq.refl _

omit [DecidableEq K] in
/-- A row of the evaluated matrix is the evaluated original row.

Each retained column reads the same polynomial evaluation. Structural vector
extensionality identifies the two rows without changing the underlying matrix. -/
@[simp] theorem evalMatrix_row (t : K) (matrix : Basic.Matrix K n)
    (row : Fin n) :
    evalMatrix t matrix row = evalVector t (matrix row) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rewrite [evalMatrix_apply, evalVector_apply]
  exact Eq.refl _

omit [DecidableEq K] in
/-- Evaluation commutes with reading the leading matrix entry.

The leading coordinate is retained by entrywise evaluation. Reading that
coordinate reduces both sides to the original scalar evaluation. -/
@[simp] theorem eval_head (t : K) (matrix : Basic.Matrix K (n + 1)) :
    SquareMatrix.Blocks.head (evalMatrix t matrix) =
      (Basic.head matrix).eval t := by
  unfold SquareMatrix.Blocks.head Basic.head
  rewrite [evalMatrix_apply]
  exact Eq.refl _

omit [DecidableEq K] in
/-- Evaluation commutes with deleting the leading entry of the top row. -/
@[simp] theorem eval_topRow (t : K) (matrix : Basic.Matrix K (n + 1)) :
    SquareMatrix.Blocks.topRow (evalMatrix t matrix) =
      evalVector t (Basic.topRow matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rw [SquareMatrix.Blocks.topRow_apply, evalMatrix_apply,
    evalVector_apply, Basic.topRow_apply]

omit [DecidableEq K] in
/-- Evaluation commutes with deleting the leading entry of the left column. -/
@[simp] theorem eval_leftColumn (t : K) (matrix : Basic.Matrix K (n + 1)) :
    SquareMatrix.Blocks.leftColumn (evalMatrix t matrix) =
      evalVector t (Basic.leftColumn matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [SquareMatrix.Blocks.leftColumn_apply, evalMatrix_apply,
    evalVector_apply, Basic.leftColumn_apply]

-- `DecidableEq K` is inherited from the surrounding section but is not used
-- here; omitting it prevents the unused-section-variable linter warning.
omit [DecidableEq K] in
/-- Evaluation sends a polynomial scalar identity to the evaluated scalar identity.

The same finite row and column indices determine diagonal membership on both
sides. Evaluation sends the retained diagonal polynomial to its scalar value
and every off-diagonal zero polynomial to zero. -/
theorem eval_scaleIdentity (t : K) (a : Basic.Polynomial K) :
    evalMatrix t (Basic.scaleIdentity (n := n) a) =
      SquareMatrix.Multiplication.scaleIdentity (a.eval t) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply]
  unfold Basic.scaleIdentity
  rw [SquareMatrix.matrixOfFn_apply]
  unfold SquareMatrix.Multiplication.scaleIdentity
  rw [SquareMatrix.matrixOfFn_apply]
  by_cases equal : row = column
  · rw [if_pos equal, if_pos equal]
  · rw [if_neg equal, if_neg equal, DensePolynomial.eval_zero]

/-- Polynomial evaluation commutes with the finite indexed sum.

The original finite index table materializes the same ordered summands.
Evaluation preserves the zero accumulator and each addition in the retained
list fold, so no summand or coordinate is replaced. -/
theorem eval_sumFin (t : K) (values : Fin n → Basic.Polynomial K) :
    (Basic.sumFin values).eval t =
      FiniteSum.Fin.sumFin (fun i => (values i).eval t) := by
  have foldEvaluation (polynomials : List (Basic.Polynomial K))
      (accumulator : Basic.Polynomial K) :
      (polynomials.foldl (fun a b => a + b) accumulator).eval t =
        (polynomials.map (fun p => p.eval t)).foldl
          (fun a b => a + b) (accumulator.eval t) := by
    induction polynomials generalizing accumulator with
    | nil => rfl
    | cons polynomial remaining inductionHypothesis =>
        rw [List.foldl_cons, List.map_cons, List.foldl_cons,
          inductionHypothesis, DensePolynomial.eval_add]
  unfold Basic.sumFin FiniteSum.Fin.sumFin
  rw [foldEvaluation]
  rw [DensePolynomial.eval_zero]
  rw [Data.List.OfFn.Basic.map_ofFn]
  change (List.ofFn fun i => (values i).eval t).foldl
      (fun a b => a + b) 0 =
    (List.ofFn fun i => (values i).eval t).foldl
      (fun a b => a + b) 0
  rfl

/-- Polynomial evaluation commutes with the finite vector dot product.

Pointwise multiplicative evaluation transports each original summand, and
the finite sum certificate retains the same ordered index table. -/
theorem eval_dot (t : K) (left right : Basic.Vector K n) :
    (Basic.dot left right).eval t =
      Dot.dot (evalVector t left)
        (evalVector t right) := by
  unfold Basic.dot Dot.dot
  rw [eval_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro i
  rewrite [DensePolynomial.eval_mul,
    evalVector_apply, evalVector_apply]
  exact Eq.refl _

/-- Evaluation of a polynomial matrix product is the product of the evaluated matrices.

The entry equation follows from the retained row and column dot product.
Each finite summand reads the same evaluated original matrix entries. -/
theorem eval_matrixMul (t : K) (left right : Basic.Matrix K n) :
    evalMatrix t (Basic.mul left right) =
      SquareMatrix.Multiplication.mul
        (evalMatrix t left) (evalMatrix t right) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply]
  unfold Basic.mul
  rw [SquareMatrix.matrixOfFn_apply,
    SquareMatrix.Multiplication.mul_apply]
  rw [eval_dot]
  unfold Dot.dot
  apply FiniteSum.Fin.sumFin_congr
  intro middle
  rewrite [evalVector_apply,
    evalVector_apply, evalMatrix_apply,
    evalMatrix_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact Eq.refl _

/-- Evaluation commutes with polynomial matrix-vector multiplication.

The original matrix and vector retain their finite dimensions and coordinates.
Evaluation preserves each row's scalar products and finite sum, so the
resulting structural vector agrees coordinate by coordinate. -/
theorem eval_matrixVector (t : K) (matrix : Basic.Matrix K n)
    (vector : Basic.Vector K n) :
    evalVector t (Basic.matrixVector matrix vector) =
      SquareMatrix.Multiplication.matrixVector
        (evalMatrix t matrix) (evalVector t vector) := by
  apply Data.Vector.Basic.vector_ext
  intro row
  simp only [evalVector_apply, Basic.matrixVector,
    SquareMatrix.Multiplication.matrixVector,
    Data.Vector.Basic.vectorOfFn_apply]
  simpa only [evalMatrix_row] using eval_dot t (matrix row)
    vector

/-- Evaluation commutes with polynomial row-vector multiplication.

The original vector and matrix retain their finite dimensions and coordinates.
Evaluation preserves each column's scalar products and finite sum, yielding
the same displayed vector as multiplication of the evaluated inputs. -/
theorem eval_vectorMatrix (t : K) (vector : Basic.Vector K n)
    (matrix : Basic.Matrix K n) :
    evalVector t (Basic.vectorMatrix vector matrix) =
      SquareMatrix.Multiplication.vectorMatrix
        (evalVector t vector) (evalMatrix t matrix) := by
  apply Data.Vector.Basic.vector_ext
  intro column
  rw [evalVector_apply, Basic.vectorMatrix,
    Data.Vector.Basic.vectorOfFn_apply,
    SquareMatrix.Multiplication.vectorMatrix,
    Data.Vector.Basic.vectorOfFn_apply, eval_dot]
  apply congrArg (Dot.dot (evalVector t vector))
  apply Data.Vector.Basic.vector_ext
  intro row
  rw [evalVector_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply,
    evalMatrix_apply]

/-- Evaluation commutes with the fraction-free polynomial Schur complement.

The pivot, retained tail and leading row and column use the same finite
coordinates. Evaluation preserves the two products and their difference
in each Schur entry. -/
theorem eval_schur (t : K) (matrix : Basic.Matrix K (n + 1)) :
    evalMatrix t (Basic.schur matrix) =
      SquareMatrix.Schur.schur (evalMatrix t matrix) := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply, Basic.schur_apply,
    DensePolynomial.eval_sub, DensePolynomial.eval_mul,
    DensePolynomial.eval_mul, SquareMatrix.Schur.schur_apply,
    Basic.head, SquareMatrix.Blocks.head,
    Basic.tail_apply, SquareMatrix.Blocks.tail_apply,
    Basic.leftColumn_apply, SquareMatrix.Blocks.leftColumn_apply,
    Basic.topRow_apply, SquareMatrix.Blocks.topRow_apply,
    evalMatrix_apply, evalMatrix_apply,
      evalMatrix_apply, evalMatrix_apply]
end

end Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
