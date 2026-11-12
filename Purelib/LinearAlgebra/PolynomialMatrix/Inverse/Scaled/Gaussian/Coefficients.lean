module
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Coefficients

/-- Equality of polynomial matrices means that every normalized coefficient
difference is the zero polynomial. -/
abbrev PolynomialMatrixIdentity {n :
  Nat}
    (left right : Basic.GaussianMatrix n) : Prop :=
  Inverse.Scaled.Coefficients.PolynomialMatrixIdentity left right

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
open Purelib.Polynomial in
/-- The fraction-free symbolic recursion returns a two-sided scaled inverse
as an identity of finite coefficient polynomials. -/
theorem
  scaledInverseData_coefficientIdentity
  (matrix : Basic.GaussianMatrix n) :
    let data :=
      Compute.scaledInverseData n matrix
    PolynomialMatrixIdentity
        (Basic.mul data.inverse matrix)
        (Basic.scaleIdentity data.scalar) ∧
      PolynomialMatrixIdentity
        (Basic.mul matrix data.inverse)
        (Basic.scaleIdentity data.scalar) := by
  dsimp only
  constructor
  · intro row column
    apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro point _
    have identity :=
      (Evaluation.scaledInverseData_spec
        point n matrix).1
    calc
      (Basic.mul
          (Compute.scaledInverseData n matrix).inverse
          matrix row column).eval point =
          (SquareMatrix.Multiplication.mul
            (Evaluation.evalMatrix point
              (Compute.scaledInverseData
                n matrix).inverse)
            (Evaluation.evalMatrix point matrix))
              row column := by
                simpa only [
                  Evaluation.evalMatrix_apply] using
                  SquareMatrix.matrix_eq_at
                    (Evaluation.eval_matrixMul point
                      (Compute.scaledInverseData
                        n matrix).inverse matrix) row column
      _ = (SquareMatrix.Multiplication.scaleIdentity
          ((Compute.scaledInverseData
            n matrix).scalar.eval point)) row column :=
        SquareMatrix.matrix_eq_at identity row column
      _ = (Basic.scaleIdentity
          (Compute.scaledInverseData
            n matrix).scalar row column).eval point :=
        by
          simpa only [
            Evaluation.evalMatrix_apply] using
            (SquareMatrix.matrix_eq_at
              (Evaluation.eval_scaleIdentity point
                (Compute.scaledInverseData
                  n matrix).scalar) row column).symm
  · intro row column
    apply Dense.Gaussian.NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro point _
    have identity :=
      (Evaluation.scaledInverseData_spec
        point n matrix).2
    calc
      (Basic.mul matrix
          (Compute.scaledInverseData n matrix).inverse
          row column).eval point =
          (SquareMatrix.Multiplication.mul
            (Evaluation.evalMatrix point matrix)
            (Evaluation.evalMatrix point
              (Compute.scaledInverseData
                n matrix).inverse)) row column := by
              simpa only [
                Evaluation.evalMatrix_apply] using
                SquareMatrix.matrix_eq_at
                  (Evaluation.eval_matrixMul point matrix
                    (Compute.scaledInverseData
                      n matrix).inverse) row column
      _ = (SquareMatrix.Multiplication.scaleIdentity
          ((Compute.scaledInverseData
            n matrix).scalar.eval point)) row column :=
        SquareMatrix.matrix_eq_at identity row column
      _ = (Basic.scaleIdentity
          (Compute.scaledInverseData
            n matrix).scalar row column).eval point :=
        by
          simpa only [
            Evaluation.evalMatrix_apply] using
            (SquareMatrix.matrix_eq_at
              (Evaluation.eval_scaleIdentity point
                (Compute.scaledInverseData
                  n matrix).scalar) row column).symm
end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Coefficients

end
