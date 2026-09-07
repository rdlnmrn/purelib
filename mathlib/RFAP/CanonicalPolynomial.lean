import mathlib.RFAP.CanonicalGaussian
import mathlib.RFAP.ComputableDerivative

/-!
# Dense polynomials over canonical Gaussian rationals

This module fixes the existing finite high-to-low coefficient-list algorithms
to the quotient-free canonical Gaussian carrier.  The concrete wrapper
theorems are dependency audit points: normalization, Horner evaluation,
coefficientwise addition, finite Horner multiplication, and automatic
differentiation must remain free of choice and quotient soundness when the
abstract coefficient interface is discharged by canonical arithmetic.
-/

namespace RFAP.CanonicalPolynomial

abbrev Coordinate := RFAP.CanonicalFraction.Rational
abbrev Gaussian := RFAP.CanonicalGaussian.Gaussian
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Gaussian

open RFAP.ComputablePolynomial.DensePolynomial

/-- Remove only the finitely displayed leading zero coefficients. -/
def normalize (polynomial : Polynomial) : Polynomial := polynomial.normalize

/-- High-to-low Horner evaluation of a finite coefficient list. -/
def evalCoeffs (point : Gaussian) (coefficients : List Gaussian) : Gaussian :=
  RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point coefficients

/-- High-to-low Horner evaluation of a dense polynomial. -/
def eval (polynomial : Polynomial) (point : Gaussian) : Gaussian :=
  polynomial.eval point

/-- Coefficientwise addition after finite left padding and normalization. -/
def add (left right : Polynomial) : Polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial.add left right

/-- Finite Horner multiplication followed by normalization at each clause. -/
def mul (left right : Polynomial) : Polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial.mulPolynomial left right

/-- Finite automatic differentiation of a dense coefficient list. -/
def derivative (polynomial : Polynomial) : Polynomial :=
  RFAP.ComputableDerivative.derivative polynomial

theorem normalize_idempotent (polynomial : Polynomial) :
    normalize (normalize polynomial) = normalize polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial.normalize_normalize polynomial

theorem eval_normalize (polynomial : Polynomial) (point : Gaussian) :
    eval (normalize polynomial) point = eval polynomial point :=
  RFAP.ComputablePolynomial.DensePolynomial.eval_normalize polynomial point

theorem eval_add (left right : Polynomial) (point : Gaussian) :
    eval (add left right) point = eval left point + eval right point :=
  RFAP.ComputablePolynomial.DensePolynomial.eval_add left right point

private theorem foldl_append_singleton
    (point : Gaussian) (coefficients : List Gaussian)
    (accumulator coefficient : Gaussian) :
    (coefficients ++ [coefficient]).foldl
        (fun value next => value * point + next) accumulator =
      coefficients.foldl (fun value next => value * point + next)
          accumulator * point + coefficient := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, List.foldl_cons]
      exact inductionHypothesis (accumulator * point + head)

private theorem evalCoeffs_append_zero
    (point : Gaussian) (coefficients : List Gaussian) :
    evalCoeffs point (coefficients ++ [0]) =
      evalCoeffs point coefficients * point := by
  unfold evalCoeffs RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  rw [foldl_append_singleton]
  exact add_zero _

/-- The single-slot shift evaluation law, proved by direct list recursion so
that it does not pass through the generic `List.foldl_append`/`LawfulMonad`
extensionality route. -/
private theorem eval_shift_one (polynomial : Polynomial) (point : Gaussian) :
    (RFAP.ComputablePolynomial.DensePolynomial.shift 1 polynomial).eval point =
      polynomial.eval point * point := by
  rw [RFAP.ComputablePolynomial.DensePolynomial.shift]
  split
  · rename_i polynomialZero
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_zero,
      RFAP.ComputablePolynomial.DensePolynomial.eval_eq_zero_of_isZero
        polynomialZero,
      zero_mul]
  · change evalCoeffs point (polynomial.normalize.coeffs ++ [0]) =
      polynomial.eval point * point
    rw [evalCoeffs_append_zero]
    change polynomial.normalize.eval point * point =
      polynomial.eval point * point
    exact congrArg (fun value : Gaussian => value * point)
      (RFAP.ComputablePolynomial.DensePolynomial.eval_normalize
        polynomial point)

private theorem gaussian_mul_swap_middle
    (first second third : Gaussian) :
    (first * second) * third = (first * third) * second := by
  calc
    (first * second) * third = first * (second * third) :=
      RFAP.CanonicalGaussian.Gaussian.mul_assoc first second third
    _ = first * (third * second) := by
      rw [RFAP.CanonicalGaussian.Gaussian.mul_comm second third]
    _ = (first * third) * second :=
      (RFAP.CanonicalGaussian.Gaussian.mul_assoc first third second).symm

private theorem gaussian_add_mul
    (first second factor : Gaussian) :
    (first + second) * factor = first * factor + second * factor := by
  calc
    (first + second) * factor = factor * (first + second) :=
      RFAP.CanonicalGaussian.Gaussian.mul_comm (first + second) factor
    _ = factor * first + factor * second :=
      RFAP.CanonicalGaussian.Gaussian.left_distrib factor first second
    _ = first * factor + second * factor := by
      rw [RFAP.CanonicalGaussian.Gaussian.mul_comm factor first,
        RFAP.CanonicalGaussian.Gaussian.mul_comm factor second]

private theorem eval_mul_fold (point : Gaussian) (right : Polynomial) :
    forall (coefficients : List Gaussian) (accumulator : Polynomial),
      (coefficients.foldl
          (fun value coefficient =>
            RFAP.ComputablePolynomial.DensePolynomial.shift 1 value +
              RFAP.ComputablePolynomial.DensePolynomial.scale
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
        RFAP.ComputablePolynomial.DensePolynomial.eval_add,
        eval_shift_one,
        RFAP.ComputablePolynomial.DensePolynomial.eval_scale]

private theorem foldl_scaled_horner
    (point scale : Gaussian) (coefficients : List Gaussian)
    (accumulator : Gaussian) :
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

theorem eval_mul (left right : Polynomial) (point : Gaussian) :
    eval (mul left right) point = eval left point * eval right point := by
  unfold eval mul RFAP.ComputablePolynomial.DensePolynomial.mulPolynomial
  rw [eval_mul_fold]
  change left.coeffs.foldl
      (fun value coefficient =>
        value * point + coefficient * eval right point) 0 =
    eval left point * eval right point
  simpa only [zero_mul, eval,
    RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs] using
      foldl_scaled_horner point (eval right point) left.coeffs 0

theorem derivative_normalize (polynomial : Polynomial) :
    derivative (normalize polynomial) = derivative polynomial :=
  RFAP.ComputableDerivative.derivative_normalize polynomial

private theorem eval_derivative_fold
    (point : Gaussian) (coefficients : List Gaussian)
    (state : Polynomial × Polynomial) :
    ((coefficients.foldl
        RFAP.ComputableDerivative.derivativeStep state).1.eval point,
      (coefficients.foldl
        RFAP.ComputableDerivative.derivativeStep state).2.eval point) =
      coefficients.foldl
        (RFAP.ComputableDerivative.evalDerivativeStep point)
        (state.1.eval point, state.2.eval point) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      apply congrArg (fun nextState : Gaussian × Gaussian =>
        coefficients.foldl
          (RFAP.ComputableDerivative.evalDerivativeStep point) nextState)
      apply Prod.ext
      · simp only [RFAP.ComputableDerivative.derivativeStep,
          RFAP.ComputableDerivative.evalDerivativeStep]
        rw [RFAP.ComputablePolynomial.DensePolynomial.eval_add,
          eval_shift_one,
          RFAP.ComputablePolynomial.DensePolynomial.eval_constant]
      · simp only [RFAP.ComputableDerivative.derivativeStep,
          RFAP.ComputableDerivative.evalDerivativeStep]
        rw [RFAP.ComputablePolynomial.DensePolynomial.eval_add,
          eval_shift_one]

/-- The derivative evaluator is the second component of the same finite
automatic-differentiation Horner scan. -/
theorem eval_derivative (polynomial : Polynomial) (point : Gaussian) :
    eval (derivative polynomial) point =
      (RFAP.ComputableDerivative.evalDerivativeCoeffs
        point polynomial.coeffs).2 := by
  unfold eval derivative RFAP.ComputableDerivative.derivative
    RFAP.ComputableDerivative.derivativeState
    RFAP.ComputableDerivative.evalDerivativeCoeffs
  have specification := eval_derivative_fold point polynomial.coeffs
    ((0 : Polynomial), (0 : Polynomial))
  exact congrArg Prod.snd specification

end RFAP.CanonicalPolynomial
