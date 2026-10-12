module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Semiring.Normalization
public import Purelib.Data.Gaussian.Power.Trace
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.LucasTrace
public import Purelib.Polynomial.Dense.Rational.Power
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

namespace Purelib.Polynomial.Elimination.Gaussian.PowerCoordinates

/-- The rational Lucas trace polynomial minus twice the displayed coordinate target.

Its radius parameter is the retained Gaussian quadrance; a degree-th Gaussian power gives a root at the corresponding
real coordinate. -/
def coordinatePolynomial (radius target :
  Fraction.Rational) (degree : Nat) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.LucasTrace.tracePolynomial radius degree - Dense.Rational.LucasTrace.normalizedConstant (2 * target)

/-- For positive degree, the coordinate polynomial has that degree and leading coefficient two to that power. -/
theorem coordinatePolynomial_leading (radius target :
  Fraction.Rational)
    (degree : Nat) (positive : 0 < degree) :
    Dense.Leading.LeadingTerm (coordinatePolynomial radius target degree) degree
      (2 ^ degree) := by
  have targetBelow :
      Dense.Leading.DegreeBelow (Dense.Rational.LucasTrace.normalizedConstant (2 * target)) degree := by
    have targetAtMost := Dense.Rational.LucasTrace.normalizedConstant_atMost (2 * target)
    exact targetAtMost.toBelowSucc.mono positive
  exact (Dense.Rational.LucasTrace.tracePolynomial_leading radius degree positive).subBelow targetBelow

/-- A positive-degree coordinate polynomial is nonzero. -/
theorem coordinatePolynomial_nonzero (radius target :
  Fraction.Rational)
    (degree : Nat) (positive : 0 < degree) :
    (coordinatePolynomial radius target degree).isZero = false :=
  (coordinatePolynomial_leading radius target degree positive).nonzero

/-- A positive-degree coordinate polynomial has exactly degree plus one retained coefficients. -/
theorem coordinatePolynomial_coefficients_length
    (radius target : Fraction.Rational) (degree : Nat) (positive : 0 < degree) :
    (coordinatePolynomial radius target degree).coeffs.length = degree + 1 := by
  have leading := coordinatePolynomial_leading radius target degree positive
  have count := leading.count_eq
  change (coordinatePolynomial radius target degree).normalize.coeffs.length =
    degree + 1 at count
  rw [leading.normalized] at count
  exact count

/-- Evaluating the rational Lucas trace pair at a Gaussian real coordinate gives the real coordinates of its Gaussian
trace pair. -/
theorem tracePair_eval_eq_gaussian (point :
  Gaussian.Basic.Canonical) : ∀ degree,
    (Dense.Rational.LucasTrace.tracePair (Gaussian.Norm.Basic.normSq point) degree).1.eval point.re =
        (Gaussian.Power.Trace.gaussianTracePair point degree).1.re ∧
      (Dense.Rational.LucasTrace.tracePair (Gaussian.Norm.Basic.normSq point) degree).2.eval point.re =
        (Gaussian.Power.Trace.gaussianTracePair point degree).2.re := by
  intro degree
  induction degree with
  | zero =>
      constructor
      · change (Dense.Rational.LucasTrace.normalizedConstant 2).eval point.re = (2 : Gaussian.Basic.Canonical).re
        rw [Dense.Rational.LucasTrace.eval_normalizedConstant]
        exact (Gaussian.Cast.natCast_re 2).symm
      · change Dense.Rational.LucasTrace.twiceVariable.eval point.re = (point + Gaussian.Basic.Canonical.conj point).re
        rw [Dense.Rational.LucasTrace.eval_twiceVariable, Gaussian.Basic.add_re]
        change 2 * point.re = point.re + point.re
        ring1
  | succ degree inductionHypothesis =>
      rw [Dense.Rational.LucasTrace.tracePair, Gaussian.Power.Trace.gaussianTracePair]
      constructor
      · exact inductionHypothesis.2
      · simp only [DensePolynomial.eval_sub, DensePolynomial.eval_mul,
          Dense.Rational.LucasTrace.eval_twiceVariable,
          Dense.Rational.LucasTrace.eval_normalizedConstant]
        rw [Gaussian.Power.Trace.add_conj, Gaussian.Power.Trace.mul_conj]
        simp only [Gaussian.Basic.mul_re, Gaussian.Basic.sub_re]
        rw [inductionHypothesis.1, inductionHypothesis.2]
        dsimp only [Gaussian.Norm.Basic.normSq, Gaussian.Basic.Canonical.normSq]
        ring1

/-- The radius-parameterized trace polynomial evaluates to twice the real part of the corresponding Gaussian power. -/
theorem tracePolynomial_eval_power (point :
  Gaussian.Basic.Canonical) (degree : Nat) :
    (Dense.Rational.LucasTrace.tracePolynomial (Gaussian.Norm.Basic.normSq point) degree).eval point.re =
      2 * (point ^ degree).re := by
  have traceIdentity := (tracePair_eval_eq_gaussian point degree).1
  rw [Gaussian.Power.Trace.gaussianTracePair_eq_powers] at traceIdentity
  have conjugatePowerReal :
      (Gaussian.Basic.Canonical.conj point ^ degree).re = (point ^ degree).re := by
    have realPart := congrArg Gaussian.Basic.re
      (Gaussian.Power.conj_pow point degree)
    exact realPart.symm
  simp only [Gaussian.Basic.add_re] at traceIdentity
  rw [conjugatePowerReal] at traceIdentity
  change (Dense.Rational.LucasTrace.tracePair (Gaussian.Norm.Basic.normSq point) degree).1.eval point.re =
    2 * (point ^ degree).re
  calc
    (Dense.Rational.LucasTrace.tracePair (Gaussian.Norm.Basic.normSq point) degree).1.eval point.re =
        (point ^ degree).re + (point ^ degree).re := traceIdentity
    _ = 2 * (point ^ degree).re := by ring1

/-- A Gaussian power identity makes the real coordinate a root of its retained coordinate polynomial. -/
theorem coordinatePolynomial_real_root
    {input point : Gaussian.Basic.Canonical} {degree : Nat} (_positive : 0 < degree)
    (power : point ^ degree = input) :
    (coordinatePolynomial (Gaussian.Norm.Basic.normSq point) input.re
      degree).eval point.re = 0 := by
  rw [coordinatePolynomial, DensePolynomial.eval_sub,
    tracePolynomial_eval_power,
    Dense.Rational.LucasTrace.eval_normalizedConstant, power]
  ring1

open Purelib.Algebra.Semiring in
/-- A Gaussian power identity makes the imaginary coordinate a root of the coordinate polynomial with the rotated
target. -/
theorem coordinatePolynomial_imaginary_root
    {input point : Gaussian.Basic.Canonical} {degree : Nat} (positive : 0 < degree)
    (power : point ^ degree = input) :
    (coordinatePolynomial (Gaussian.Norm.Basic.normSq point)
      ((Gaussian.Constants.negativeImaginaryUnit ^ degree * input).re) degree).eval point.im = 0 := by
  let rotated := Gaussian.Constants.negativeImaginaryUnit * point
  have rotatedPower : rotated ^ degree = Gaussian.Constants.negativeImaginaryUnit ^ degree * input := by
    dsimp only [rotated]
    rewrite [Normalization.product_pow, power]
    rfl
  have root := coordinatePolynomial_real_root positive rotatedPower
  rw [Gaussian.Constants.negativeImaginaryUnit_mul_re,
    Gaussian.Constants.normSq_negativeImaginaryUnit_mul] at root
  exact root

/-- Gaussian quadrance satisfies the rational power polynomial induced by the retained Gaussian power identity. -/
theorem powerPolynomial_norm_root
    {input point : Gaussian.Basic.Canonical} {degree : Nat} (positive : 0 < degree)
    (power : point ^ degree = input) :
    (Dense.Rational.Power.powerPolynomial (Gaussian.Norm.Basic.normSq input) degree).eval
      (Gaussian.Norm.Basic.normSq point) = 0 := by
  rw [Dense.Rational.Power.powerPolynomial_eval _ _ _ positive, ← Gaussian.Power.normSq_pow, power]
  ring1

end Purelib.Polynomial.Elimination.Gaussian.PowerCoordinates

end
