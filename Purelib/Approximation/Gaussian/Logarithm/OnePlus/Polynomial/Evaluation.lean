module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Coefficient
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Power.Alternating
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Alternating
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Monomial
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Algebra.FiniteSum

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Ascending.Rational

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial.Evaluation

/-- Multiplying a relative-logarithm term by its input gives the corresponding alternating logarithm monomial. -/
theorem mul_log1pRelTerm_eq_monomial (u :
  Canonical) (index : Nat) :
    u * Sample.log1pRelTerm u index =
      Scale.scale (Coefficient.alternatingCoefficient index)
        (u ^ (index + 1)) := by
  have coefficientIdentity :
      (1 / ((index + 1 : Nat) : Fraction.Rational)) * Alternating.alternatingSign index =
        Coefficient.alternatingCoefficient index := by
    rw [Coefficient.alternatingCoefficient,
      Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.one_mul]
    exact Fraction.Field.mul_comm _ _
  calc
    u * Sample.log1pRelTerm u index =
        u * Scale.scale
          (1 / ((index + 1 : Nat) : Fraction.Rational)) ((-u) ^ index) := rfl
    _ = u * Scale.scale
          (1 / ((index + 1 : Nat) : Fraction.Rational))
          (Scale.scale (Alternating.alternatingSign index)
            (u ^ index)) := by
      rw [Power.Alternating.negPower_eq_scaledPower]
    _ = Scale.scale
          (1 / ((index + 1 : Nat) : Fraction.Rational))
          (u * Scale.scale (Alternating.alternatingSign index)
            (u ^ index)) := Scale.mul_scale _ _ _
    _ = Scale.scale
          (1 / ((index + 1 : Nat) : Fraction.Rational))
          (Scale.scale (Alternating.alternatingSign index)
            (u * u ^ index)) := by
      rw [Scale.mul_scale]
    _ = Scale.scale
          ((1 / ((index + 1 : Nat) : Fraction.Rational)) * Alternating.alternatingSign index)
          (u * u ^ index) := Scale.scale_scale _ _ _
    _ = Scale.scale (Coefficient.alternatingCoefficient index)
          (u ^ (index + 1)) := by
      rw [coefficientIdentity, pow_succ,
        Data.Gaussian.Basic.mul_comm]

/-- The relative-logarithm program is exactly the evaluation of the finite polynomial used by the divided-difference
calculus. -/
theorem eval_log1pPolynomial (u :
  Canonical) : ∀ index,
    GaussianEvaluation.eval (Polynomial.log1pPolynomial index) u = Sample.log1pSample u index
  | 0 => by
      rw [Polynomial.log1pPolynomial, GaussianEvaluation.eval_monomial, Sample.log1pSample, Sample.log1pRelSample,
        Prefix.sum_succ,
        Prefix.sum_zero,
        Sample.log1pRelTerm_zero, Data.Gaussian.Basic.zero_add]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im, Basic.mul_re, Basic.mul_im, pow_one,
          Purelib.Data.Gaussian.Basic.one_re, Purelib.Data.Gaussian.Basic.one_im] <;> ring1
  | index + 1 => by
      calc
        GaussianEvaluation.eval (Polynomial.log1pPolynomial (index + 1)) u =
            GaussianEvaluation.eval (Polynomial.log1pPolynomial index) u +
              Scale.scale
                (Coefficient.alternatingCoefficient (index + 1))
                (u ^ (index + 2)) := by
          rw [Polynomial.log1pPolynomial, GaussianEvaluation.eval_add, GaussianEvaluation.eval_monomial]
        _ = Sample.log1pSample u index +
              u * Sample.log1pRelTerm u (index + 1) := by
          rw [eval_log1pPolynomial u index,
            mul_log1pRelTerm_eq_monomial]
        _ = u *
            (Sample.log1pRelSample u index + Sample.log1pRelTerm u (index + 1)) := by
          rw [Sample.log1pSample]
          apply Data.Gaussian.Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
        _ = Sample.log1pSample u (index + 1) := by
          rw [Sample.log1pSample]
          apply congrArg (fun value : Canonical => u * value)
          rw [Sample.log1pRelSample, Sample.log1pRelSample]
          exact
            (Prefix.sum_succ
              (Sample.log1pRelTerm u) (index + 1)).symm

/-- Gaussian evaluation of the finite logarithm derivative polynomial equals its geometric derivative sample. -/
theorem eval_log1pGeometricPolynomial (u :
  Canonical) : ∀ index,
    GaussianEvaluation.eval (Polynomial.log1pGeometricPolynomial index) u =
      Sample.log1pDerivativeSample u index
  | 0 => by
      change
        Scale.scale 1 1 + u * 0 =
          Prefix.sum
            (fun termIndex => (-u) ^ termIndex) (0 + 1)
      rw [Prefix.sum_succ,
        Prefix.sum_zero, pow_zero]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im, Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
            Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im,
          Purelib.Data.Gaussian.Basic.zero_re, Purelib.Data.Gaussian.Basic.zero_im, Purelib.Data.Gaussian.Basic.one_re,
            Purelib.Data.Gaussian.Basic.one_im] <;> ring1
  | index + 1 => by
      calc
        GaussianEvaluation.eval (Polynomial.log1pGeometricPolynomial (index + 1)) u =
            GaussianEvaluation.eval (Polynomial.log1pGeometricPolynomial index) u +
              Scale.scale
                (Alternating.alternatingSign (index + 1)) (u ^ (index + 1)) := by
          rw [Polynomial.log1pGeometricPolynomial, GaussianEvaluation.eval_add, GaussianEvaluation.eval_monomial]
        _ = Sample.log1pDerivativeSample u index + (-u) ^ (index + 1) := by
          rw [eval_log1pGeometricPolynomial u
            index,
            Power.Alternating.negPower_eq_scaledPower]
        _ = Sample.log1pDerivativeSample u (index + 1) := by
          unfold Sample.log1pDerivativeSample
          exact
            (Prefix.sum_succ
              (fun termIndex => (-u) ^ termIndex) (index + 1)).symm
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial.Evaluation

end
