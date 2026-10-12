module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Basic

open Purelib.Data

open Purelib.Polynomial

section
/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Arithmetic

/-- Coefficientwise addition after finite left padding and normalization. -/
def add (left right : Basic.GaussianCanonical.CoefficientPolynomial)
  : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.add left right

/-- Gaussian evaluation sends normalized coefficientwise addition to scalar addition. -/
theorem eval_add (left right :
  Basic.GaussianCanonical.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.eval (Dense.Gaussian.Arithmetic.add left right) point = Dense.Gaussian.Evaluation.eval
      left point + Dense.Gaussian.Evaluation.eval right point :=
  Dense.Basic.DensePolynomial.eval_add left right point

/-- The single-slot shift evaluation law, proved by direct list recursion so
that it does not pass through the generic `List.foldl_append`/`LawfulMonad`
extensionality route. -/
public theorem eval_shift_one (polynomial :
  Basic.GaussianCanonical.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial.shift 1 polynomial).eval point =
      polynomial.eval point * point := by
  rw [Dense.Basic.DensePolynomial.shift]
  split
  · rename_i polynomialZero
    rw [Dense.Basic.DensePolynomial.eval_zero,
      Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero
        polynomialZero,
      zero_mul]
  · change Dense.Gaussian.Evaluation.evalCoeffs point (polynomial.normalize.coeffs ++ [0]) =
      polynomial.eval point * point
    rw [Dense.Gaussian.Evaluation.evalCoeffs_append_zero]
    change polynomial.normalize.eval point * point =
      polynomial.eval point * point
    exact congrArg (fun value : Gaussian.Basic.Canonical => value * point)
      (Dense.Basic.DensePolynomial.eval_normalize
        polynomial point)

end Purelib.Polynomial.Dense.Gaussian.Arithmetic

end
