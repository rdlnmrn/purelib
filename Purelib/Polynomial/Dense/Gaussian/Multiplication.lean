module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Data.Bool.Decide
import Purelib.Tactic.Ring
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
  Basic.CanonicalCoefficients.CoefficientPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false :=
  DensePolynomial.isZero_mul_eq_false hp hq

/-- Cancel a nonzero Gaussian polynomial from an all-input product identity.

The finite coefficient-sized probe grid certifies that the product of the
factor and the coefficient difference is zero. Nonzero-product preservation
then forces the same difference to be zero, including at roots of the factor.
-/
theorem cancel_left_eval
    {factor left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (factorNonzero : factor.isZero = false)
    (identity : ∀ point : Canonical,
      factor.eval point * left.eval point = factor.eval point * right.eval point) :
    ∀ point : Canonical, left.eval point = right.eval point := by
  have productZero : (factor * (left - right)).isZero = true := by
    apply Extensionality.isZero_of_eval_eq_zero
    intro point
    rewrite [DensePolynomial.eval_mul, DensePolynomial.eval_sub]
    calc
      factor.eval point * (left.eval point - right.eval point) =
          factor.eval point * left.eval point - factor.eval point * right.eval point := by ring1
      _ = 0 := by rewrite [identity point]; exact sub_self _
  have differenceZero : (left - right).isZero = true := by
    by_cases zero : (left - right).isZero = true
    · exact zero
    · have nonzero := product_isZero_false factorNonzero
        (Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true _ zero)
      rewrite [nonzero] at productZero
      exact Bool.noConfusion productZero
  intro point
  have zero := DensePolynomial.eval_eq_zero_of_isZero differenceZero point
  rewrite [DensePolynomial.eval_sub] at zero
  calc
    left.eval point = (left.eval point - right.eval point) + right.eval point := by ring1
    _ = right.eval point := by rewrite [zero, zero_add]; rfl

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
  CoefficientPolynomial) : (DensePolynomial
    Canonical) :=
  DensePolynomial.mulPolynomial left right

/-- Exchange the final two factors in an associated Gaussian product. -/
private theorem gaussian_mul_swap_middle
    (first second third : Canonical) :
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
    (first second factor : Canonical) :
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
private theorem eval_mul_fold (point : Canonical)
  (right : CoefficientPolynomial) :
    forall (coefficients : List Canonical) (accumulator :
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
        Arithmetic.eval_shift_one,
        DensePolynomial.eval_scale]

/-- A common Gaussian scalar factors out of a finite Horner fold with scaled initial value. -/
private theorem foldl_scaled_horner
    (point scale : Canonical) (coefficients : List Canonical)
    (accumulator : Canonical) :
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
  CoefficientPolynomial) (point : Canonical) :
    Evaluation.eval (mul left right) point = Evaluation.eval
      left point * Evaluation.eval right point := by
  unfold Evaluation.eval mul DensePolynomial.mulPolynomial
  rw [eval_mul_fold]
  change left.coeffs.foldl
      (fun value coefficient =>
        value * point + coefficient * Evaluation.eval right point) 0 =
    Evaluation.eval left point * Evaluation.eval right point
  simpa only [zero_mul, Evaluation.eval,
    DensePolynomial.eval,
    DensePolynomial.evalCoeffs] using
      foldl_scaled_horner point (Evaluation.eval right point) left.coeffs 0
end Purelib.Polynomial.Dense.Gaussian.Multiplication

end
