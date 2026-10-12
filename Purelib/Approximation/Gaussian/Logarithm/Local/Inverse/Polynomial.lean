module
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Composition
import Purelib.Polynomial.Ascending.Rational.Composition.Derivative
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Truncation
public import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.Geometric.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Monomial
import Purelib.Polynomial.Ascending.Rational.Nonnegative
import Purelib.Polynomial.Ascending.Rational.Truncation

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Logarithm Local Inverse Polynomial and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial

open Purelib
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Exponential.Taylor
open Purelib.Approximation.Gaussian.Logarithm.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Horner
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Ascending.Rational
open Purelib.Polynomial.Ascending.Rational.Composition
open Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
open Purelib.Polynomial.Ascending.Rational.Geometric
open Purelib.Polynomial.Ascending.Rational.Truncation

/-- The actual finite program obtained by substituting the displayed local logarithm polynomial into the displayed
exponential polynomial. -/
@[expose] public def exponentialLocalLog (expDegree logDepth : Nat) : Rational.Basic.CoefficientPolynomial :=
  Composition.compose (Polynomial.exponential expDegree) (Polynomial.localLog logDepth)

/-- Evaluation of the composed exponential and local-logarithm polynomials equals the finite Taylor program applied to
the matching logarithm Horner sample. -/
theorem eval_exponentialLocalLog (z : Data.Gaussian.Basic.Canonical)
    (expDegree logDepth : Nat) :
    GaussianEvaluation.eval (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog expDegree
      logDepth) z =
      Taylor.Basic.truncatedExp
        (Sample.sample z logDepth) expDegree := by
  rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog, Composition.eval_compose,
    Polynomial.eval_exponential, Polynomial.eval_localLog]

/-- Below degree twice the depth plus two, the composed polynomial satisfies the coefficient identity of twice itself
and one-minus-square times its derivative. -/
theorem exponentialLocalLog_ode_below (depth : Nat) :
    Truncation.EqualBelow (2 * depth + 2)
      (Rational.Basic.mul Polynomial.oneMinusSquare
        (Derivative.derivative (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth
          + 2) depth)))
      (Rational.Basic.scale 2 (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth
        + 2) depth)) := by
  let logarithm := Polynomial.localLog depth
  let previousExponential := Polynomial.exponential (2 * depth + 1)
  let composition := Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2) depth
  let previousComposition := Composition.compose previousExponential logarithm
  let highTerm := Monomial.monomial (2 * depth + 2) (-2)
  have derivativeIdentity :
      Coefficientwise.CoefficientwiseEqual (Derivative.derivative composition)
        (Rational.Basic.mul (Derivative.derivative logarithm) previousComposition) := by
    exact Coefficientwise.coefficientwise_trans
      (Derivative.derivative_compose (Polynomial.exponential (2 * depth + 2)) logarithm)
      (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl _)
        (Composition.compose_congr
          (Polynomial.derivative_exponential_succ (2 * depth + 1)) logarithm))
  have kernelIdentity :
      Coefficientwise.CoefficientwiseEqual (Rational.Basic.mul Polynomial.oneMinusSquare (Derivative.derivative
        logarithm))
        (Rational.Basic.add (Rational.Basic.constant 2) highTerm) := by
    exact Coefficientwise.coefficientwise_trans
      (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl Polynomial.oneMinusSquare)
        (Polynomial.derivative_localLog depth))
      (Polynomial.oneMinusSquare_mul_evenGeometric depth)
  have fullIdentity :
      Coefficientwise.CoefficientwiseEqual
        (Rational.Basic.mul Polynomial.oneMinusSquare (Derivative.derivative composition))
        (Rational.Basic.mul (Rational.Basic.add (Rational.Basic.constant 2) highTerm) previousComposition) := by
    exact Coefficientwise.coefficientwise_trans
      (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl Polynomial.oneMinusSquare)
        derivativeIdentity)
      (Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_symm
          (Coefficientwise.coefficientwise_mul_assoc Polynomial.oneMinusSquare
            (Derivative.derivative logarithm) previousComposition))
        (Coefficientwise.coefficientwise_mul kernelIdentity (Coefficientwise.coefficientwise_refl _)))
  have highVanishes :
      Truncation.VanishesBelow (2 * depth + 2)
        (Rational.Basic.mul highTerm previousComposition) :=
    Truncation.vanishesBelow_mul_left
      (Truncation.vanishesBelow_monomial (2 * depth + 2) (2 * depth + 2)
        (Nat.le_refl _) (-2)) previousComposition
  have removeHigh :
      Truncation.EqualBelow (2 * depth + 2)
        (Rational.Basic.mul (Rational.Basic.add (Rational.Basic.constant 2) highTerm) previousComposition)
        (Rational.Basic.scale 2 previousComposition) :=
    Truncation.equalBelow_trans
      (CoefficientwiseEqual.equalBelow
        (Coefficientwise.coefficientwise_add_mul (Rational.Basic.constant 2) highTerm previousComposition) _)
      (Truncation.equalBelow_trans
        (Truncation.equalBelow_add
          (CoefficientwiseEqual.equalBelow
            (Coefficientwise.coefficientwise_constant_mul 2 previousComposition) _)
          (Truncation.equalBelow_refl _ _))
        (Truncation.vanishesBelow_add_right highVanishes))
  have previousToCurrent :
      Truncation.EqualBelow (2 * depth + 2) previousComposition composition := by
    exact Truncation.equalBelow_symm
      (Polynomial.compose_exponential_succ_below (2 * depth + 1) logarithm
        (Polynomial.localLog_zero_constant depth))
  exact Truncation.equalBelow_trans (CoefficientwiseEqual.equalBelow fullIdentity _)
    (Truncation.equalBelow_trans removeHigh
      (Truncation.equalBelow_scale 2 previousToCurrent))

/-- Compute each coefficient of one-minus-square times a polynomial derivative, retaining the separate degrees below
two. -/
theorem coefficient_oneMinusSquare_mul_derivative
    (polynomial : Rational.Basic.CoefficientPolynomial) (degree : Nat) :
    Rational.Basic.coefficient (Rational.Basic.mul Polynomial.oneMinusSquare (Derivative.derivative polynomial)) degree
      =
      if degree < 2 then
        ((degree + 1 : Nat) : Fraction.Rational) *
          Rational.Basic.coefficient polynomial (degree + 1)
      else
        ((degree + 1 : Nat) : Fraction.Rational) *
            Rational.Basic.coefficient polynomial (degree + 1) -
          ((degree - 1 : Nat) : Fraction.Rational) *
            Rational.Basic.coefficient polynomial (degree - 1) := by
  rw [Polynomial.oneMinusSquare,
    (Coefficientwise.coefficientwise_add_mul Rational.Basic.one (Monomial.monomial 2 (-1))
      (Derivative.derivative polynomial)) degree,
    Rational.Basic.coefficient_add,
    (Coefficientwise.coefficientwise_one_mul (Derivative.derivative polynomial)) degree,
    Monomial.coefficient_monomial_mul, Derivative.coefficient_derivative]
  by_cases below : degree < 2
  · rw [if_pos below, if_pos below]
    ring1
  · rw [if_neg below, if_neg below, Derivative.coefficient_derivative]
    rw [show degree - 2 + 1 = degree - 1 by omega]
    ring1

/-- The synchronized exponential–local-logarithm composition has constant coefficient one. -/
theorem exponentialLocalLog_zero_coefficient (depth : Nat) :
    Rational.Basic.coefficient (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth
      + 2) depth) 0 = 1 := by
  rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog]
  exact (Composition.coefficient_compose_zero_of_inner_zero (Polynomial.localLog depth)
    (Polynomial.localLog_zero_constant depth)
    (Polynomial.exponential (2 * depth + 2)).coefficients).trans
      (Polynomial.exponential_zero_coefficient (2 * depth + 2))

/-- Through degree twice the depth plus two, the synchronized composition has constant coefficient one and every
positive-degree coefficient two. -/
theorem exponentialLocalLog_low_coefficient (depth : Nat) :
    ∀ degree, degree ≤ 2 * depth + 2 →
      Rational.Basic.coefficient (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 *
        depth + 2) depth) degree =
        if degree = 0 then 1 else 2 := by
  let polynomial := Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2) depth
  have all : ∀ limit, limit ≤ 2 * depth + 2 →
      ∀ degree, degree ≤ limit →
        Rational.Basic.coefficient polynomial degree = if degree = 0 then 1 else 2 := by
    intro limit
    induction limit with
    | zero =>
        intro limitBound degree degreeBound
        have degreeZero : degree = 0 := Nat.eq_zero_of_le_zero degreeBound
        subst degree
        rw [if_pos rfl]
        exact Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog_zero_coefficient depth
    | succ limit inductionHypothesis =>
        intro limitBound degree degreeBound
        have limitLeMaximum : limit ≤ 2 * depth + 2 :=
          (Nat.le_succ limit).trans limitBound
        by_cases earlier : degree ≤ limit
        · exact inductionHypothesis limitLeMaximum degree earlier
        · have degreeEqual : degree = limit + 1 :=
            Nat.le_antisymm degreeBound
              (Nat.succ_le_of_lt (Nat.lt_of_not_ge earlier))
          subst degree
          rw [if_neg ((fun impossible => Nat.noConfusion impossible))]
          have ode := Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog_ode_below depth
            limit
            (Nat.lt_of_succ_le limitBound)
          rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.coefficient_oneMinusSquare_mul_derivative,
            Rational.Basic.coefficient_scale] at ode
          have current := inductionHypothesis limitLeMaximum limit
            (Nat.le_refl _)
          by_cases limitZero : limit = 0
          · subst limit
            rw [if_pos (by decide)] at current
            rw [if_pos (by decide)] at ode
            rw [current] at ode
            change Rational.Basic.coefficient
              (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2) depth) 1 =
                2
            calc
              Rational.Basic.coefficient (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog
                (2 * depth + 2) depth) 1 =
                  (1 : Fraction.Rational) *
                    Rational.Basic.coefficient
                      (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2)
                        depth) 1 := by ring1
              _ = 2 * 1 := ode
              _ = 2 := by ring1
          · rw [if_neg limitZero] at current
            by_cases limitOne : limit = 1
            · subst limit
              rw [if_pos (by decide)] at ode
              rw [current] at ode
              apply Fraction.Field.mul_right_cancel_of_ne
                (show (2 : Fraction.Rational) ≠ 0 by decide)
              calc
                Rational.Basic.coefficient polynomial 2 * 2 =
                    2 * Rational.Basic.coefficient polynomial 2 := by ring1
              _ = 2 * 2 := ode
            · have atLeastTwo : 2 ≤ limit :=
                by
                  cases limit with
                  | zero => exact (limitZero rfl).elim
                  | succ predecessor =>
                      cases predecessor with
                      | zero => exact (limitOne rfl).elim
                      | succ predecessor =>
                          exact Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.zero_le predecessor))
              rw [if_neg (Nat.not_lt_of_ge atLeastTwo)] at ode
              have previous := inductionHypothesis limitLeMaximum (limit - 1)
                (Nat.sub_le limit 1)
              have previousPositive : 0 < limit - 1 :=
                Purelib.Data.Nat.Subtraction.sub_pos_of_lt atLeastTwo
              rw [if_neg previousPositive.ne'] at previous
              have scaled :
                  ((limit + 1 : Nat) : Fraction.Rational) *
                      Rational.Basic.coefficient polynomial (limit + 1) =
                    ((limit + 1 : Nat) : Fraction.Rational) * 2 := by
                calc
                  ((limit + 1 : Nat) : Fraction.Rational) *
                        Rational.Basic.coefficient polynomial (limit + 1) =
                      (((limit + 1 : Nat) : Fraction.Rational) *
                          Rational.Basic.coefficient polynomial (limit + 1) -
                        ((limit - 1 : Nat) : Fraction.Rational) *
                          Rational.Basic.coefficient polynomial (limit - 1)) +
                        ((limit - 1 : Nat) : Fraction.Rational) *
                          Rational.Basic.coefficient polynomial (limit - 1) := by ring1
                  _ = 2 * Rational.Basic.coefficient polynomial limit +
                        ((limit - 1 : Nat) : Fraction.Rational) *
                          Rational.Basic.coefficient polynomial (limit - 1) := by rw [ode]
                  _ = ((limit + 1 : Nat) : Fraction.Rational) * 2 := by
                    rw [current, previous]
                    conv_rhs =>
                      rw [show limit + 1 = (limit - 1) + 2 by
                        have oneLe : 1 ≤ limit :=
                          (show 1 ≤ 2 by decide).trans atLeastTwo
                        calc
                          limit + 1 = (limit - 1 + 1) + 1 :=
                            congrArg (· + 1) (Purelib.Data.Nat.Subtraction.sub_add_cancel oneLe).symm
                          _ = (limit - 1) + (1 + 1) :=
                            Nat.add_assoc (limit - 1) 1 1
                          _ = (limit - 1) + 2 := rfl,
                        Purelib.Algebra.NatCast.add]
                    rw [show ((2 : Nat) : Fraction.Rational) = 2 by decide]
                    ring1
              apply Fraction.Field.mul_right_cancel_of_ne
                ((Fraction.Cast.Order.natCast_pos_direct
                  (Nat.zero_lt_succ limit)).ne')
              calc
                Rational.Basic.coefficient polynomial (limit + 1) *
                      ((limit + 1 : Nat) : Fraction.Rational) =
                    ((limit + 1 : Nat) : Fraction.Rational) *
                      Rational.Basic.coefficient polynomial (limit + 1) := by ring1
                _ = ((limit + 1 : Nat) : Fraction.Rational) * 2 := scaled
                _ = 2 * ((limit + 1 : Nat) : Fraction.Rational) := by ring1
  intro degree bound
  exact all degree bound degree (Nat.le_refl _)

/-- Every coefficient of the finite exponential–local-logarithm composition is nonnegative. -/
theorem coefficientsNonnegative_exponentialLocalLog
    (expDegree logDepth : Nat) :
    Nonnegative.CoefficientsNonnegative (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog
      expDegree logDepth) :=
  Nonnegative.coefficientsNonnegative_compose
    (Polynomial.coefficientsNonnegative_exponential expDegree)
    (Polynomial.coefficientsNonnegative_localLog logDepth)

/-- The synchronized composition agrees coefficientwise with the finite geometric prefix below degree twice the depth
plus three. -/
theorem exponentialLocalLog_equalBelow_geometricPrefix (depth : Nat) :
    Truncation.EqualBelow (2 * depth + 3)
      (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2) depth)
      (Geometric.geometricPrefix (2 * depth + 2)) := by
  intro degree below
  rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog_low_coefficient depth degree (by
    omega),
    Geometric.geometricPrefix_coefficient]
  by_cases zero : degree = 0
  · rewrite [if_pos zero, if_pos zero]
    exact Eq.refl _
  · rewrite [if_neg zero, if_neg zero]
    rw [if_pos (by omega)]

/-- The evaluated composition minus its matching geometric prefix factors as the first omitted power times the retained
coefficient tail. -/
theorem exponentialLocalLog_sub_prefix (z : Data.Gaussian.Basic.Canonical) (depth : Nat) :
    GaussianEvaluation.eval (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth +
      2) depth) z -
        GaussianEvaluation.eval (Geometric.geometricPrefix (2 * depth + 2)) z =
      z ^ (2 * depth + 3) *
        GaussianEvaluation.eval
          ⟨(Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth + 2)
            depth).coefficients.drop
            (2 * depth + 3)⟩ z := by
  rw [Truncation.eval_split z (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog (2 * depth
    + 2) depth)
      (2 * depth + 3),
    Truncation.prefixEval_congr
      (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.exponentialLocalLog_equalBelow_geometricPrefix depth)
        z,
    ← GaussianEvaluation.geometricPrefix_eval_eq_prefix z (2 * depth + 2)]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
      Data.Gaussian.Basic.sub_im] <;> ring1
end Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial

end
