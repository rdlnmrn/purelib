module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Derivative
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Monomial
public import Purelib.Polynomial.Ascending.Rational.Nonnegative

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Basic

section
public section

/-! Approximation Gaussian Logarithm Local Polynomial and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial

open Purelib
open Purelib.Algebra.FiniteSum
open Purelib.Approximation.Gaussian.Logarithm.Local.Horner
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Ascending.Rational

/-- The finite odd local-logarithm polynomial through degree twice the depth plus one.

Its coefficients are twice the reciprocal of the positive odd degree, stored in the original ascending rational
coefficient representation. -/
@[expose] public def localLog : Nat → Purelib.Polynomial.Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Purelib.Polynomial.Ascending.Rational.Monomial.monomial 1 2
  | depth + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.add
        (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth)
        (Purelib.Polynomial.Ascending.Rational.Monomial.monomial (2 * (depth + 1) + 1)
          (2 / (2 * ((depth + 1 : Nat) : Purelib.Data.Rat.Fraction.Rational) + 1)))

/-- The finite even geometric polynomial with coefficient two at each even degree through twice the depth. -/
@[expose] public def evenGeometric : Nat → Purelib.Polynomial.Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Purelib.Polynomial.Ascending.Rational.Basic.constant 2
  | depth + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.add
        (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth)
        (Purelib.Polynomial.Ascending.Rational.Monomial.monomial (2 * (depth + 1)) 2)

/-- The ascending rational polynomial one minus the square of its variable. -/
@[expose] public def oneMinusSquare : Rational.Basic.CoefficientPolynomial :=
  Rational.Basic.add Rational.Basic.one (Monomial.monomial 2 (-1))

/-- Multiplying a local-logarithm coefficient by its positive odd degree gives two. -/
theorem odd_mul_localLogCoefficient (index : Nat) :
    ((2 * index + 1 : Nat) : Fraction.Rational) *
        (2 / (2 * (index : Fraction.Rational) + 1)) = 2 := by
  have castOdd :
      ((2 * index + 1 : Nat) : Fraction.Rational) =
        2 * (index : Fraction.Rational) + 1 := by
    rw [Purelib.Algebra.NatCast.add, Purelib.Algebra.NatCast.mul]
    rw [show ((2 : Nat) : Fraction.Rational) = 2 by decide,
      show ((1 : Nat) : Fraction.Rational) = 1 by decide]
  have denominatorPositive :
      0 < (2 * (index : Fraction.Rational) + 1) := by
    rw [← castOdd]
    exact Fraction.Cast.Order.natCast_pos_direct
      (Nat.zero_lt_succ (2 * index))
  rw [castOdd, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne 2 _
    denominatorPositive.ne'

/-- The coefficientwise derivative of the finite local-logarithm polynomial is its even geometric polynomial. -/
theorem derivative_localLog : ∀ depth,
    Coefficientwise.CoefficientwiseEqual (Derivative.derivative
      (Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth))
      (Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth)
  | 0 => by
      change Coefficientwise.CoefficientwiseEqual (Derivative.derivative (Monomial.monomial 1 2))
        (Rational.Basic.constant 2)
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_monomial_succ 0 2)
        (Coefficientwise.coefficientwise_trans
          (Monomial.coefficientwise_monomial_value 0
            (Approximation.Gaussian.Logarithm.Local.Polynomial.odd_mul_localLogCoefficient 0))
          (Monomial.coefficientwise_monomial_zero 2))
  | depth + 1 => by
      change Coefficientwise.CoefficientwiseEqual
        (Derivative.derivative
          (Rational.Basic.add (Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth)
            (Monomial.monomial (2 * (depth + 1) + 1)
              (2 / (2 * ((depth + 1 : Nat) : Fraction.Rational) + 1)))))
        (Rational.Basic.add (Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth) (Monomial.monomial
          (2 * (depth + 1)) 2))
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_add _ _)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.derivative_localLog depth)
            (Derivative.derivative_monomial_succ (2 * (depth + 1)) _))
          (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl _)
            (Monomial.coefficientwise_monomial_value (2 * (depth + 1))
              (Approximation.Gaussian.Logarithm.Local.Polynomial.odd_mul_localLogCoefficient (depth + 1)))))

/-- Multiplying the finite even geometric polynomial by one minus the square leaves exactly its constant term and final
negative remainder monomial. -/
theorem oneMinusSquare_mul_evenGeometric : ∀ depth,
    Coefficientwise.CoefficientwiseEqual (Rational.Basic.mul
      Approximation.Gaussian.Logarithm.Local.Polynomial.oneMinusSquare
      (Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth))
      (Rational.Basic.add (Rational.Basic.constant 2) (Monomial.monomial (2 * depth + 2) (-2)))
  | 0 => by
      change Coefficientwise.CoefficientwiseEqual
        (Rational.Basic.mul (Rational.Basic.add Rational.Basic.one (Monomial.monomial 2 (-1))) (Rational.Basic.constant
          2))
        (Rational.Basic.add (Rational.Basic.constant 2) (Monomial.monomial 2 (-2)))
      exact Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_add_mul Rational.Basic.one (Monomial.monomial 2 (-1)) (Rational.Basic.constant
          2))
        (Coefficientwise.coefficientwise_add
          (Coefficientwise.coefficientwise_one_mul (Rational.Basic.constant 2))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl _)
              (Coefficientwise.coefficientwise_symm (Monomial.coefficientwise_monomial_zero 2)))
            (Coefficientwise.coefficientwise_trans
              (Monomial.coefficientwise_monomial_mul 2 0 (-1) 2)
              (Monomial.coefficientwise_monomial_value 2 (by decide)))))
  | depth + 1 => by
      let currentDegree := 2 * (depth + 1)
      let highDegree := currentDegree + 2
      change Coefficientwise.CoefficientwiseEqual
        (Rational.Basic.mul Approximation.Gaussian.Logarithm.Local.Polynomial.oneMinusSquare
          (Rational.Basic.add (Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth) (Monomial.monomial
            currentDegree 2)))
        (Rational.Basic.add (Rational.Basic.constant 2) (Monomial.monomial highDegree (-2)))
      have currentProduct :
          Coefficientwise.CoefficientwiseEqual
            (Rational.Basic.mul Approximation.Gaussian.Logarithm.Local.Polynomial.oneMinusSquare (Monomial.monomial
              currentDegree 2))
            (Rational.Basic.add (Monomial.monomial currentDegree 2)
              (Monomial.monomial highDegree (-2))) := by
        exact Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add_mul Rational.Basic.one (Monomial.monomial 2 (-1))
            (Monomial.monomial currentDegree 2))
          (Coefficientwise.coefficientwise_add
            (Coefficientwise.coefficientwise_one_mul (Monomial.monomial currentDegree 2))
            (Coefficientwise.coefficientwise_trans
              (Monomial.coefficientwise_monomial_mul 2 currentDegree (-1) 2)
              (by
                have degreeEqual : 2 + currentDegree = highDegree := by
                  dsimp only [highDegree, currentDegree]
                  exact Nat.add_comm 2 (2 * (depth + 1))
                rw [degreeEqual]
                exact Monomial.coefficientwise_monomial_value highDegree (by decide))))
      exact Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_mul_add Approximation.Gaussian.Logarithm.Local.Polynomial.oneMinusSquare
          (Approximation.Gaussian.Logarithm.Local.Polynomial.evenGeometric depth)
          (Monomial.monomial currentDegree 2))
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.oneMinusSquare_mul_evenGeometric depth)
              currentProduct)
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_telescope_rearrange
              (Rational.Basic.constant 2) (Monomial.monomial currentDegree (-2))
              (Monomial.monomial currentDegree 2) (Monomial.monomial highDegree (-2)))
            (Coefficientwise.coefficientwise_trans
              (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl _)
                (Monomial.coefficientwise_monomial_cancel currentDegree 2))
              (Coefficientwise.coefficientwise_add_zero
                (Rational.Basic.add (Rational.Basic.constant 2) (Monomial.monomial highDegree (-2)))))))

/-- Gaussian evaluation of the finite local-logarithm polynomial equals the matching Horner sample. -/
theorem eval_localLog (z : Data.Gaussian.Basic.Canonical) : ∀ depth,
    GaussianEvaluation.eval (Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth) z =
      Sample.sample z depth
  | 0 => by
      rw [Approximation.Gaussian.Logarithm.Local.Polynomial.localLog, GaussianEvaluation.eval_monomial,
        Polynomial.complexLog_sample_eq_sum,
        Prefix.sum_succ,
        Prefix.sum_zero,
        Data.Gaussian.Basic.zero_add,
        Polynomial.localLogTerm]
      change Scale.scale 2 (z ^ 1) =
        Scale.scale (2 / (2 * (0 : Fraction.Rational) + 1))
          (z ^ (2 * 0 + 1))
      rw [show (2 / (2 * (0 : Fraction.Rational) + 1) : Fraction.Rational) = 2 by decide]
  | depth + 1 => by
      rw [Approximation.Gaussian.Logarithm.Local.Polynomial.localLog, GaussianEvaluation.eval_add,
        Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.eval_localLog z depth,
        GaussianEvaluation.eval_monomial,
        Polynomial.complexLog_sample_eq_sum,
        Polynomial.complexLog_sample_eq_sum,
        Prefix.sum_succ]
      change
        Prefix.sum
              (Polynomial.localLogTerm z)
              (depth + 1) +
            Scale.scale
              (2 / (2 * ((depth + 1 : Nat) : Fraction.Rational) + 1))
              (z ^ (2 * (depth + 1) + 1)) =
          Prefix.sum
              (Polynomial.localLogTerm z)
              (depth + 1) +
            Polynomial.localLogTerm z (depth + 1)
      rfl

/-- Every finite local-logarithm polynomial has zero constant coefficient. -/
theorem localLog_zero_constant : ∀ depth,
    Rational.Basic.coefficient (Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth) 0 = 0
  | 0 => by
      rw [Approximation.Gaussian.Logarithm.Local.Polynomial.localLog, Monomial.coefficient_monomial, if_neg
        Nat.zero_ne_one]
  | depth + 1 => by
      rw [Approximation.Gaussian.Logarithm.Local.Polynomial.localLog, Rational.Basic.coefficient_add,
        Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.localLog_zero_constant depth,
        Monomial.coefficient_monomial,
        if_neg ((fun impossible => Nat.noConfusion impossible)),
        Fraction.Field.zero_add]

/-- Every coefficient of the finite local-logarithm polynomial is nonnegative. -/
theorem coefficientsNonnegative_localLog : ∀ depth,
    Nonnegative.CoefficientsNonnegative (Approximation.Gaussian.Logarithm.Local.Polynomial.localLog depth)
  | 0 => Nonnegative.coefficientsNonnegative_monomial 1 (by decide)
  | depth + 1 => by
      apply Nonnegative.coefficientsNonnegative_add
        (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.coefficientsNonnegative_localLog depth)
      apply Nonnegative.coefficientsNonnegative_monomial
      exact Fraction.Order.Field.div_nonneg_direct (by decide)
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Fraction.Cast.Order.natCast_pos_direct
              (show 0 < depth + 1 by omega)).le)
          (by decide))
end Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial

end
