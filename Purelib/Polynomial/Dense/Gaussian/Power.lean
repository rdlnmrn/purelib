module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Leading
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Gaussian.Extensionality

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Power

/-! ## Displayed weighted polynomials and positive degree totals -/

/-- Finite polynomial power, kept local to the dense executable polynomial
representation rather than importing a broader polynomial monoid. -/
def polynomialPower (p :
  CoefficientPolynomial) : Nat →
  CoefficientPolynomial
  | 0 => DensePolynomial.constant 1
  | exponent + 1 => p * polynomialPower p exponent

/-- Evaluation commutes with the finite Gaussian polynomial power algorithm.

The exponent-zero coefficient table evaluates to one, and every recursive multiplication evaluates using the same
retained point. -/
@[simp] theorem eval_polynomialPower
    (p : CoefficientPolynomial) (exponent : Nat) (point :
      Gaussian.Basic.Canonical) :
    (polynomialPower p exponent).eval point = p.eval point ^ exponent := by
  induction exponent with
  | zero =>
      simp only [polynomialPower, DensePolynomial.eval_constant, pow_zero, -eq_self,
        -iff_self]
      rfl
  | succ exponent inductionHypothesis =>
      rw [polynomialPower, DensePolynomial.eval_mul, inductionHypothesis, pow_succ]
      exact Gaussian.Basic.mul_comm _ _

/-- Every natural power of a nonzero Gaussian polynomial is nonzero, including exponent zero. -/
theorem polynomialPower_nonzero
    {p : CoefficientPolynomial} (nonzero : p.isZero = false) :
    ∀ exponent : Nat, (polynomialPower p exponent).isZero = false
  | 0 => (Purelib.Polynomial.Dense.Leading.LeadingTerm.constant one_ne_zero).nonzero
  | exponent + 1 =>
      DensePolynomial.isZero_mul_eq_false nonzero
        (polynomialPower_nonzero nonzero exponent)

/-- The original finite Gaussian power obeys the positive-exponent derivative rule.

Finite normalized coefficient comparison identifies the two original power
orders. The derivative difference law transfers the already retained generic
power-rule readback, including at zero values of the original polynomial.
-/
theorem eval_derivative_polynomialPower_succ
    (polynomial : CoefficientPolynomial) (index : Nat) (point : Gaussian.Basic.Canonical) :
    (Dense.Derivative.derivative (polynomialPower polynomial (index + 1))).eval point =
      ((index : Gaussian.Basic.Canonical) + 1) * polynomial.eval point ^ index *
        (Dense.Derivative.derivative polynomial).eval point := by
  have differenceZero :
      (polynomialPower polynomial (index + 1) - Dense.Power.power polynomial (index + 1)).isZero = true := by
    apply Extensionality.isZero_of_eval_eq_zero
    intro argument
    rewrite [DensePolynomial.eval_sub, eval_polynomialPower, Dense.Power.eval_power]
    exact sub_self _
  exact (Dense.Derivative.eval_derivative_eq_of_sub_isZero differenceZero point).trans
    (Dense.Power.eval_derivative_power_succ polynomial index point)

/-- The same nonzero original finite power raises its original leading coefficient to the displayed exponent. -/
theorem leadingCoeff_polynomialPower (polynomial : CoefficientPolynomial)
    (nonzero : polynomial.isZero = false) : (exponent : Nat) →
    (polynomialPower polynomial exponent).leadingCoeff = polynomial.leadingCoeff ^ exponent
  | 0 => (Leading.LeadingTerm.constant (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)).coefficient_eq
  | exponent + 1 => by
      change (polynomial * polynomialPower polynomial exponent).leadingCoeff = _
      rewrite [DensePolynomial.leadingCoeff_mul nonzero (polynomialPower_nonzero nonzero exponent),
        leadingCoeff_polynomialPower polynomial nonzero exponent, pow_succ]
      exact Gaussian.Basic.mul_comm _ _
end Purelib.Polynomial.Dense.Gaussian.Power

end
