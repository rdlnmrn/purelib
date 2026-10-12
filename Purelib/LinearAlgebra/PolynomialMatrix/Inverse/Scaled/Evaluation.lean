module
import Purelib.Data.Fin
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Block
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Schur
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation

open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Vector
open Purelib.Polynomial
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Evaluating the symbolic block formula gives the corresponding certified scalar block inverse.

The supplied smaller certificate uses the evaluated Schur matrix and agrees with both retained symbolic components. -/
theorem eval_blockInverse (t : K) (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (smaller : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n)
    (certificate : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse
      (SquareMatrix.Schur.schur (PolynomialMatrix.Evaluation.evalMatrix t matrix)))
    (scalarEqual : certificate.scalar = smaller.scalar.eval t)
    (inverseEqual : certificate.inverse = PolynomialMatrix.Evaluation.evalMatrix t smaller.inverse) :
    PolynomialMatrix.Evaluation.evalMatrix t (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix smaller) =
      SquareMatrix.Inverse.Scaled.Block.blockInverse (PolynomialMatrix.Evaluation.evalMatrix t matrix)
        certificate := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [PolynomialMatrix.Evaluation.evalMatrix_apply, PolynomialMatrix.Inverse.Scaled.Block.blockInverse_apply,
    SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
    scalarEqual, inverseEqual]
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · simp only [Data.Fin.cases_zero]
      rw [Dense.Basic.DensePolynomial.eval_add, PolynomialMatrix.Evaluation.eval_dot,
        PolynomialMatrix.Evaluation.eval_matrixVector,
        PolynomialMatrix.Evaluation.eval_topRow, PolynomialMatrix.Evaluation.eval_leftColumn]
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_neg,
        PolynomialMatrix.Evaluation.eval_head]
      apply congrArg (fun value => -((PolynomialMatrix.Basic.head matrix).eval t) * value)
      have evaluated := Data.Vector.Basic.vector_eq_at
        (PolynomialMatrix.Evaluation.eval_vectorMatrix t (PolynomialMatrix.Basic.topRow matrix) smaller.inverse)
          columnIndex
      rw [PolynomialMatrix.Evaluation.evalVector_apply] at evaluated
      rw [PolynomialMatrix.Evaluation.eval_topRow]
      exact evaluated
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_neg,
        PolynomialMatrix.Evaluation.eval_head]
      apply congrArg (fun value => -((PolynomialMatrix.Basic.head matrix).eval t) * value)
      have evaluated := Data.Vector.Basic.vector_eq_at
        (PolynomialMatrix.Evaluation.eval_matrixVector t smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix))
          rowIndex
      rw [PolynomialMatrix.Evaluation.evalVector_apply] at evaluated
      rw [PolynomialMatrix.Evaluation.eval_leftColumn]
      exact evaluated
    · simp only [Data.Fin.cases_succ]
      rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_mul,
        PolynomialMatrix.Evaluation.eval_head, PolynomialMatrix.Evaluation.evalMatrix_apply]
      ring1

/-- Every specialization of the symbolic recursion satisfies both scaled-inverse identities.

The original finite recursion supplies the scalar polynomial and inverse
matrix. Evaluating them at the same coefficient value gives left and right
products equal to the identity scaled by that evaluated scalar; no nonzero
scalar hypothesis is required. -/
theorem scaledInverseData_spec (t : K) :
    ∀ (n : Nat) (matrix : PolynomialMatrix.Basic.Matrix K n),
      let data := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix
      SquareMatrix.Multiplication.mul (PolynomialMatrix.Evaluation.evalMatrix t data.inverse)
          (PolynomialMatrix.Evaluation.evalMatrix t matrix) =
          SquareMatrix.Multiplication.scaleIdentity (data.scalar.eval t) ∧
        SquareMatrix.Multiplication.mul (PolynomialMatrix.Evaluation.evalMatrix t matrix)
          (PolynomialMatrix.Evaluation.evalMatrix t data.inverse) =
          SquareMatrix.Multiplication.scaleIdentity (data.scalar.eval t)
  | 0, matrix => by
      constructor
      · apply SquareMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
      · apply SquareMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
  | n + 1, matrix => by
      let smallerData := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n (PolynomialMatrix.Basic.schur
        matrix)
      have smallerSpecification :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation.scaledInverseData_spec t n
          (PolynomialMatrix.Basic.schur matrix)
      let smallerCertificate :
          SquareMatrix.Inverse.Scaled.Basic.ScaledInverse
            (SquareMatrix.Schur.schur (PolynomialMatrix.Evaluation.evalMatrix t matrix)) :=
        { scalar := smallerData.scalar.eval t
          inverse := PolynomialMatrix.Evaluation.evalMatrix t smallerData.inverse
          left_identity := by
            rw [← PolynomialMatrix.Evaluation.eval_schur]
            exact smallerSpecification.1
          right_identity := by
            rw [← PolynomialMatrix.Evaluation.eval_schur]
            exact smallerSpecification.2 }
      have blockEvaluation :
          PolynomialMatrix.Evaluation.evalMatrix t (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix
            smallerData) =
            SquareMatrix.Inverse.Scaled.Block.blockInverse
              (PolynomialMatrix.Evaluation.evalMatrix t matrix) smallerCertificate :=
        PolynomialMatrix.Inverse.Scaled.Evaluation.eval_blockInverse t matrix smallerData smallerCertificate rfl rfl
      change
        SquareMatrix.Multiplication.mul
            (PolynomialMatrix.Evaluation.evalMatrix t (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix
              smallerData))
            (PolynomialMatrix.Evaluation.evalMatrix t matrix) =
            SquareMatrix.Multiplication.scaleIdentity
              ((PolynomialMatrix.Basic.head matrix * smallerData.scalar).eval t) ∧
          SquareMatrix.Multiplication.mul (PolynomialMatrix.Evaluation.evalMatrix t matrix)
            (PolynomialMatrix.Evaluation.evalMatrix t (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix
              smallerData)) =
            SquareMatrix.Multiplication.scaleIdentity
              ((PolynomialMatrix.Basic.head matrix * smallerData.scalar).eval t)
      rw [Dense.Basic.DensePolynomial.eval_mul]
      rw [blockEvaluation]
      exact
        ⟨by
            simpa only [PolynomialMatrix.Evaluation.eval_head] using
              SquareMatrix.Inverse.Scaled.Block.blockInverse_mul
                (PolynomialMatrix.Evaluation.evalMatrix t matrix) smallerCertificate,
          by
            simpa only [PolynomialMatrix.Evaluation.eval_head] using
              SquareMatrix.Inverse.Scaled.Block.mul_blockInverse
                (PolynomialMatrix.Evaluation.evalMatrix t matrix) smallerCertificate⟩

/-- Package evaluated symbolic data as a two-sided scaled-inverse certificate.

The original recursion is evaluated once at the supplied scalar. The result
retains its evaluated scalar and matrix together with the two multiplication
certificates, without choosing a different inverse or requiring division. -/
@[expose] def evaluatedScaledInverse (t : K) (matrix : PolynomialMatrix.Basic.Matrix K n) :
    SquareMatrix.Inverse.Scaled.Basic.ScaledInverse (PolynomialMatrix.Evaluation.evalMatrix t matrix) :=
  let data := PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix
  let specification := PolynomialMatrix.Inverse.Scaled.Evaluation.scaledInverseData_spec t n matrix
  { scalar := data.scalar.eval t
    inverse := PolynomialMatrix.Evaluation.evalMatrix t data.inverse
    left_identity := specification.1
    right_identity := specification.2 }

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
