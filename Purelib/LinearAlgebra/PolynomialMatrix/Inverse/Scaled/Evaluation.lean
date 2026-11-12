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

open Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
open Purelib.Polynomial.Dense.Basic

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
theorem eval_blockInverse (t : K) (matrix : Basic.Matrix K (n + 1))
    (smaller : Basic.ScaledInverseData K n)
    (certificate : ScaledInverse
      (SquareMatrix.Schur.schur (Evaluation.evalMatrix t matrix)))
    (scalarEqual : certificate.scalar = smaller.scalar.eval t)
    (inverseEqual : certificate.inverse = Evaluation.evalMatrix t smaller.inverse) :
    Evaluation.evalMatrix t (Block.blockInverse matrix smaller) =
      SquareMatrix.Inverse.Scaled.Block.blockInverse (Evaluation.evalMatrix t matrix)
        certificate := by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [Evaluation.evalMatrix_apply, Block.blockInverse_apply,
    SquareMatrix.Inverse.Scaled.Block.blockInverse_apply,
    scalarEqual, inverseEqual]
  refine Data.Fin.cases_induction ?_ (fun rowIndex => ?_) row
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · simp only [Data.Fin.cases_zero]
      rw [DensePolynomial.eval_add, Evaluation.eval_dot,
        Evaluation.eval_matrixVector,
        Evaluation.eval_topRow, Evaluation.eval_leftColumn]
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      rw [DensePolynomial.eval_mul, DensePolynomial.eval_neg,
        Evaluation.eval_head]
      apply congrArg (fun value => -((Basic.head matrix).eval t) * value)
      have evaluated := Data.Vector.Basic.vector_eq_at
        (Evaluation.eval_vectorMatrix t (Basic.topRow matrix) smaller.inverse)
          columnIndex
      rw [Evaluation.evalVector_apply] at evaluated
      rw [Evaluation.eval_topRow]
      exact evaluated
  · refine Data.Fin.cases_induction ?_ (fun columnIndex => ?_) column
    · simp only [Data.Fin.cases_zero, Data.Fin.cases_succ]
      rw [DensePolynomial.eval_mul, DensePolynomial.eval_neg,
        Evaluation.eval_head]
      apply congrArg (fun value => -((Basic.head matrix).eval t) * value)
      have evaluated := Data.Vector.Basic.vector_eq_at
        (Evaluation.eval_matrixVector t smaller.inverse (Basic.leftColumn matrix))
          rowIndex
      rw [Evaluation.evalVector_apply] at evaluated
      rw [Evaluation.eval_leftColumn]
      exact evaluated
    · simp only [Data.Fin.cases_succ]
      rw [DensePolynomial.eval_mul, DensePolynomial.eval_mul,
        Evaluation.eval_head, Evaluation.evalMatrix_apply]
      ring1

/-- Every specialization of the symbolic recursion satisfies both scaled-inverse identities.

The original finite recursion supplies the scalar polynomial and inverse
matrix. Evaluating them at the same coefficient value gives left and right
products equal to the identity scaled by that evaluated scalar; no nonzero
scalar hypothesis is required. -/
theorem scaledInverseData_spec (t : K) :
    ∀ (n : Nat) (matrix : Basic.Matrix K n),
      let data := Compute.scaledInverseData n matrix
      SquareMatrix.Multiplication.mul (Evaluation.evalMatrix t data.inverse)
          (Evaluation.evalMatrix t matrix) =
          SquareMatrix.Multiplication.scaleIdentity (data.scalar.eval t) ∧
        SquareMatrix.Multiplication.mul (Evaluation.evalMatrix t matrix)
          (Evaluation.evalMatrix t data.inverse) =
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
      let smallerData := Compute.scaledInverseData n (Basic.schur
        matrix)
      have smallerSpecification :=
        Evaluation.scaledInverseData_spec t n
          (Basic.schur matrix)
      let smallerCertificate :
          ScaledInverse
            (SquareMatrix.Schur.schur (Evaluation.evalMatrix t matrix)) :=
        { scalar := smallerData.scalar.eval t
          inverse := Evaluation.evalMatrix t smallerData.inverse
          left_identity := by
            rw [← Evaluation.eval_schur]
            exact smallerSpecification.1
          right_identity := by
            rw [← Evaluation.eval_schur]
            exact smallerSpecification.2 }
      have blockEvaluation :
          Evaluation.evalMatrix t (Block.blockInverse matrix
            smallerData) =
            SquareMatrix.Inverse.Scaled.Block.blockInverse
              (Evaluation.evalMatrix t matrix) smallerCertificate :=
        eval_blockInverse t matrix smallerData smallerCertificate rfl rfl
      change
        SquareMatrix.Multiplication.mul
            (Evaluation.evalMatrix t (Block.blockInverse matrix
              smallerData))
            (Evaluation.evalMatrix t matrix) =
            SquareMatrix.Multiplication.scaleIdentity
              ((Basic.head matrix * smallerData.scalar).eval t) ∧
          SquareMatrix.Multiplication.mul (Evaluation.evalMatrix t matrix)
            (Evaluation.evalMatrix t (Block.blockInverse matrix
              smallerData)) =
            SquareMatrix.Multiplication.scaleIdentity
              ((Basic.head matrix * smallerData.scalar).eval t)
      rw [DensePolynomial.eval_mul]
      rw [blockEvaluation]
      exact
        ⟨by
            simpa only [Evaluation.eval_head] using
              SquareMatrix.Inverse.Scaled.Block.blockInverse_mul
                (Evaluation.evalMatrix t matrix) smallerCertificate,
          by
            simpa only [Evaluation.eval_head] using
              SquareMatrix.Inverse.Scaled.Block.mul_blockInverse
                (Evaluation.evalMatrix t matrix) smallerCertificate⟩

/-- Package evaluated symbolic data as a two-sided scaled-inverse certificate.

The original recursion is evaluated once at the supplied scalar. The result
retains its evaluated scalar and matrix together with the two multiplication
certificates, without choosing a different inverse or requiring division. -/
@[expose] def evaluatedScaledInverse (t : K) (matrix : Basic.Matrix K n) :
    ScaledInverse (Evaluation.evalMatrix t matrix) :=
  let data := Compute.scaledInverseData n matrix
  let specification := scaledInverseData_spec t n matrix
  { scalar := data.scalar.eval t
    inverse := Evaluation.evalMatrix t data.inverse
    left_identity := specification.1
    right_identity := specification.2 }

end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
