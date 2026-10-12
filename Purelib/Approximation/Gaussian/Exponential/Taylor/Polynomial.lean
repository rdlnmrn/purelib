module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Nat.Factorial.Basic
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Composition
import Purelib.Polynomial.Ascending.Rational.Derivative
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Monomial
public import Purelib.Polynomial.Ascending.Rational.Nonnegative
public import Purelib.Polynomial.Ascending.Rational.Truncation

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite exponential Taylor coefficient polynomials

The ascending rational table retains reciprocal-factorial monomials through
its supplied finite degree. Direct coefficient algebra proves its derivative,
Gaussian evaluation, substitution and nonnegative readback identities.
-/

public section
namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Ascending.Rational
open Purelib.Polynomial.Ascending.Rational.Truncation

/-- Construct the finite exponential Taylor coefficient polynomial.

Each successor retains the preceding polynomial and adds its next monomial.
The computed factorial supplies the exact denominator-one rational directly,
without rebuilding it through a linear natural-cast procedure. -/
@[expose] def exponential : Nat → Purelib.Polynomial.Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Purelib.Polynomial.Ascending.Rational.Basic.constant 1
  | degree + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.add
        (Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.exponential degree)
        (Purelib.Polynomial.Ascending.Rational.Monomial.monomial (degree + 1)
          (1 / Purelib.Data.Rat.Fraction.Cast.fromInt
            (Int.ofNat (Purelib.Data.Nat.Factorial.Basic.factorial (degree + 1)))))

/-- Extend the finite exponential polynomial by its next reciprocal-factorial monomial. -/
theorem exponential_succ (degree : Nat) :
    Taylor.Polynomial.exponential (degree + 1) =
      Rational.Basic.add (Taylor.Polynomial.exponential degree)
        (Monomial.monomial (degree + 1)
          (1 / (Factorial.Basic.factorial (degree + 1) : Fraction.Rational))) := by
  rw [Taylor.Polynomial.exponential, Fraction.Cast.natCast_eq_fromInt, Int.ofNat_eq_natCast]

/-- The next reciprocal factorial recovers its predecessor after degree scaling.

The factorial successor product and its positive denominator give the exact
cross multiplication needed to cancel the retained nonzero rational factors. -/
theorem factorialCoefficient_step (degree : Nat) :
    ((degree + 1 : Nat) : Fraction.Rational) *
        (1 / (Factorial.Basic.factorial
          (degree + 1) : Fraction.Rational)) =
      1 / (Factorial.Basic.factorial degree : Fraction.Rational) := by
  let current : Fraction.Rational :=
    (Factorial.Basic.factorial degree : Fraction.Rational)
  let next : Fraction.Rational :=
    (Factorial.Basic.factorial (degree + 1) : Fraction.Rational)
  have currentNonzero : current ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (Factorial.Basic.factorial_pos degree)).ne'
  have nextNonzero : next ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (Factorial.Basic.factorial_pos
        (degree + 1))).ne'
  have cross :
      ((degree + 1 : Nat) : Fraction.Rational) * current = 1 * next := by
    dsimp only [current, next]
    rw [Factorial.Basic.factorial_succ, NatCast.mul]
    ring1
  calc
    ((degree + 1 : Nat) : Fraction.Rational) * (1 / next) =
        ((degree + 1 : Nat) : Fraction.Rational) / next := by
      change _ * (1 * next⁻¹) = _ * next⁻¹
      rw [Fraction.Field.one_mul]
    _ = 1 / current :=
      Fraction.Field.div_eq_div_of_cross
        _ _ _ _ nextNonzero currentNonzero cross

/-- Differentiating the next exponential polynomial recovers its predecessor.

The finite monomial derivative lowers degree and multiplies by that same degree.
The reciprocal-factorial identity supplies the preceding exact coefficient. -/
theorem derivative_exponential_succ : ∀ degree,
    Coefficientwise.CoefficientwiseEqual (Derivative.derivative (Taylor.Polynomial.exponential (degree + 1)))
      (Taylor.Polynomial.exponential degree)
  | 0 => by
      rw [Taylor.Polynomial.exponential_succ]
      change Coefficientwise.CoefficientwiseEqual
        (Derivative.derivative
          (Rational.Basic.add (Rational.Basic.constant 1)
            (Monomial.monomial 1
              (1 / (Factorial.Basic.factorial
                1 : Fraction.Rational)))))
        (Rational.Basic.constant 1)
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_add _ _)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add (Derivative.derivative_constant 1)
            (Derivative.derivative_monomial_succ 0 _))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl Rational.Basic.zero)
              (Monomial.coefficientwise_monomial_value 0
                (Taylor.Polynomial.factorialCoefficient_step 0)))
            (Coefficientwise.coefficientwise_trans
              (Coefficientwise.coefficientwise_zero_add
                (Monomial.monomial 0
                  (1 / (Factorial.Basic.factorial
                    0 : Fraction.Rational))))
              (Monomial.coefficientwise_monomial_zero 1))))
  | degree + 1 => by
      rw [Taylor.Polynomial.exponential_succ (degree + 1)]
      conv_rhs => rw [Taylor.Polynomial.exponential_succ]
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_add _ _)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.derivative_exponential_succ degree)
            (Derivative.derivative_monomial_succ (degree + 1) _))
          (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl _)
            (Monomial.coefficientwise_monomial_value (degree + 1)
              (Taylor.Polynomial.factorialCoefficient_step (degree + 1)))))

/-- Gaussian evaluation of the finite exponential polynomial equals the corresponding truncated exponential sample. -/
theorem eval_exponential (z : Gaussian.Basic.Canonical) : ∀ degree,
    GaussianEvaluation.eval (Taylor.Polynomial.exponential degree) z =
      Taylor.Basic.truncatedExp z degree
  | 0 => by
      change Scale.scale 1 1 + z * 0 = 1
      apply Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | degree + 1 => by
      rw [Taylor.Polynomial.exponential_succ, GaussianEvaluation.eval_add,
        Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.eval_exponential z degree,
        GaussianEvaluation.eval_monomial,
        Taylor.Basic.truncatedExp_succ,
        Taylor.Basic.taylorTerm]

/-- Composing consecutive exponential truncations with a polynomial of zero constant coefficient preserves all
coefficients below the new truncation degree. -/
theorem compose_exponential_succ_below (depth : Nat) (inner : Rational.Basic.CoefficientPolynomial)
    (zeroConstant : Rational.Basic.coefficient inner 0 = 0) :
    Truncation.EqualBelow (depth + 1)
      (Composition.compose (Taylor.Polynomial.exponential (depth + 1)) inner)
      (Composition.compose (Taylor.Polynomial.exponential depth) inner) := by
  rw [Taylor.Polynomial.exponential_succ]
  exact Truncation.equalBelow_trans
    (CoefficientwiseEqual.equalBelow (Composition.compose_add _ _ inner) (depth + 1))
    (Truncation.equalBelow_trans
      (Truncation.equalBelow_add (Truncation.equalBelow_refl _ _)
        (CoefficientwiseEqual.equalBelow (Composition.compose_monomial (depth + 1) _ inner) (depth + 1)))
      (Truncation.vanishesBelow_add_right
        (Truncation.vanishesBelow_scale _
          (Truncation.vanishesBelow_pow_of_zero_constant zeroConstant (depth + 1)))))

/-- Every finite exponential polynomial has constant coefficient one.

A successor monomial has positive degree and contributes zero at the constant
readback. The initial constant coefficient therefore persists unchanged. -/
theorem exponential_zero_coefficient : ∀ depth,
    Rational.Basic.coefficient (Taylor.Polynomial.exponential depth) 0 = 1
  | 0 => by rw [Taylor.Polynomial.exponential, Coefficientwise.coefficient_constant, if_pos rfl]
  | depth + 1 => by
      rw [Taylor.Polynomial.exponential, Rational.Basic.coefficient_add,
        Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.exponential_zero_coefficient depth,
        Monomial.coefficient_monomial, if_neg ((fun same : 0 = depth + 1 => Nat.noConfusion same.symm))]
      ring1

/-- Every finite exponential coefficient is a nonnegative rational.

The initial coefficient is one. Each added monomial has a reciprocal positive
factorial coefficient, while zero padding preserves nonnegative readback. -/
theorem coefficientsNonnegative_exponential : ∀ depth,
    Nonnegative.CoefficientsNonnegative (Taylor.Polynomial.exponential depth)
  | 0 => Nonnegative.coefficientsNonnegative_constant (by decide)
  | depth + 1 => by
      rw [Taylor.Polynomial.exponential_succ]
      apply Nonnegative.coefficientsNonnegative_add
        (Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.coefficientsNonnegative_exponential depth)
      apply Nonnegative.coefficientsNonnegative_monomial
      exact Fraction.Order.Field.div_nonneg_direct (by decide)
        (Fraction.Cast.Order.natCast_pos_direct
          (Factorial.Basic.factorial_pos
            (depth + 1))).le

end Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
end
