module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Leading
public import Purelib.Polynomial.Dense.Multiplication

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
end Purelib.Polynomial.Dense.Gaussian.Power

end
