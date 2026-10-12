module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.GaussianCanonical (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplication

/-- The product of two nonzero Gaussian polynomials is nonzero. -/
theorem product_isZero_false {p q :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false :=
  DensePolynomial.isZero_mul_eq_false hp hq
end Purelib.Polynomial.Dense.Gaussian.Multiplication

end

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplication

/-- Finite Horner multiplication followed by normalization at each clause. -/
def mul (left right :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial
    Gaussian.Basic.Canonical) :=
  DensePolynomial.mulPolynomial left right

/-- Exchange the final two factors in an associated Gaussian product. -/
private theorem gaussian_mul_swap_middle
    (first second third : Gaussian.Basic.Canonical) :
    (first * second) * third = (first * third) * second := by
  calc
    (first * second) * third = first * (second * third) :=
      Canonical.mul_assoc first second third
    _ = first * (third * second) := by
      rw [Canonical.mul_comm second third]
    _ = (first * third) * second :=
      (Canonical.mul_assoc first third second).symm

/-- Right multiplication distributes over Gaussian addition. -/
private theorem gaussian_add_mul
    (first second factor : Gaussian.Basic.Canonical) :
    (first + second) * factor = first * factor + second * factor := by
  calc
    (first + second) * factor = factor * (first + second) :=
      Canonical.mul_comm (first + second) factor
    _ = factor * first + factor * second :=
      Canonical.left_distrib factor first second
    _ = first * factor + second * factor := by
      rw [Canonical.mul_comm factor first,
        Canonical.mul_comm factor second]

/-- Evaluation commutes with the coefficient-fold multiplication algorithm from any polynomial accumulator. -/
private theorem eval_mul_fold (point : Gaussian.Basic.Canonical)
  (right : CoefficientPolynomial) :
    forall (coefficients : List Gaussian.Basic.Canonical) (accumulator :
      CoefficientPolynomial),
      (coefficients.foldl
          (fun value coefficient =>
            DensePolynomial.shift 1 value +
              DensePolynomial.scale
                coefficient right)
          accumulator).eval point =
        coefficients.foldl
          (fun value coefficient =>
            value * point + coefficient * right.eval point)
          (accumulator.eval point)
  | [], _ => rfl
  | coefficient :: coefficients, accumulator => by
      simp only [List.foldl_cons]
      rw [eval_mul_fold point right coefficients,
        DensePolynomial.eval_add,
        Purelib.Polynomial.Dense.Gaussian.Arithmetic.eval_shift_one,
        DensePolynomial.eval_scale]

/-- A common Gaussian scalar factors out of a finite Horner fold with scaled initial value. -/
private theorem foldl_scaled_horner
    (point scale : Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical)
    (accumulator : Gaussian.Basic.Canonical) :
    coefficients.foldl
        (fun value coefficient => value * point + coefficient * scale)
        (accumulator * scale) =
      coefficients.foldl
          (fun value coefficient => value * point + coefficient)
          accumulator * scale := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      have step :
          accumulator * scale * point + coefficient * scale =
            (accumulator * point + coefficient) * scale := by
        calc
          accumulator * scale * point + coefficient * scale =
              accumulator * point * scale + coefficient * scale := by
            rw [gaussian_mul_swap_middle accumulator scale point]
          _ = (accumulator * point + coefficient) * scale :=
            (gaussian_add_mul (accumulator * point) coefficient scale).symm
      rw [step]
      exact inductionHypothesis (accumulator * point + coefficient)

/-- Finite Gaussian polynomial multiplication evaluates to the product of the input evaluations. -/
theorem eval_mul (left right :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Evaluation.eval (mul left right) point = Dense.Gaussian.Evaluation.eval
      left point * Dense.Gaussian.Evaluation.eval right point := by
  unfold Dense.Gaussian.Evaluation.eval mul DensePolynomial.mulPolynomial
  rw [eval_mul_fold]
  change left.coeffs.foldl
      (fun value coefficient =>
        value * point + coefficient * Dense.Gaussian.Evaluation.eval right point) 0 =
    Dense.Gaussian.Evaluation.eval left point * Dense.Gaussian.Evaluation.eval right point
  simpa only [zero_mul, Dense.Gaussian.Evaluation.eval,
    DensePolynomial.eval,
    DensePolynomial.evalCoeffs] using
      foldl_scaled_horner point (Dense.Gaussian.Evaluation.eval right point) left.coeffs 0
end Purelib.Polynomial.Dense.Gaussian.Multiplication

end
