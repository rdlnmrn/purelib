module
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Ascending.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Coefficients of finite rational convolution

Complementary natural degrees index the original finite prefix sums. Scalar
readback identifies the retained product tables and splits degree weights
between the two derivative contributions.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Convolution

open Purelib.Algebra
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Each product-table coefficient is its finite convolution sum.

At degree `degree`, sum over left indices from zero through that degree, pairing each with the complementary right
index. -/
theorem coefficientCoefficients_mul (left right : List Fraction.Rational) :
    ∀ degree,
      Basic.coefficientCoefficients (Basic.mulCoefficients left right) degree =
        FiniteSum.Prefix.coordinateSum
          (fun leftDegree =>
            Basic.coefficientCoefficients left leftDegree *
              Basic.coefficientCoefficients right (degree - leftDegree))
          (degree + 1) := by
  induction left with
  | nil =>
      intro degree
      rw [Basic.mulCoefficients]
      change 0 = FiniteSum.Prefix.coordinateSum
        (fun leftDegree =>
          Basic.coefficientCoefficients ([] : List Fraction.Rational) leftDegree *
            Basic.coefficientCoefficients right (degree - leftDegree))
        (degree + 1)
      have allZero : ∀ count,
          FiniteSum.Prefix.coordinateSum
              (fun leftDegree =>
                Basic.coefficientCoefficients ([] : List Fraction.Rational) leftDegree *
                  Basic.coefficientCoefficients right (degree - leftDegree)) count =
            0 := by
        intro count
        induction count with
        | zero => rfl
        | succ count inductionHypothesis =>
            rw [FiniteSum.Prefix.coordinateSum_succ, inductionHypothesis,
              Basic.coefficientCoefficients_nil,
              Fraction.Field.zero_mul_direct,
              Fraction.Field.zero_add]
      exact (allZero (degree + 1)).symm
  | cons head tail inductionHypothesis =>
      intro degree
      cases degree with
      | zero =>
          rw [Basic.coefficientCoefficients_mul_zero,
            FiniteSum.Prefix.coordinateSum_succ, FiniteSum.Prefix.coordinateSum_zero]
          simp only [Nat.zero_sub, Basic.coefficientCoefficients_cons_zero]
          ring1
      | succ degree =>
          rw [Basic.coefficientCoefficients_mul_cons_succ,
            FiniteSum.Prefix.coordinateSum_succ_front]
          simp only [Basic.coefficientCoefficients_cons_zero, Nat.sub_zero]
          rw [Basic.coefficientCoefficients_map_scale]
          rw [inductionHypothesis degree]
          apply congrArg
            (head * Basic.coefficientCoefficients right (degree + 1) + ·)
          apply FiniteSum.Prefix.coordinateSum_congr
          intro index
          rw [Basic.coefficientCoefficients_cons_succ,
            Nat.succ_sub_succ_eq_sub]

/-- The coefficient of a polynomial product is the finite sum over complementary degrees. -/
@[simp] theorem coefficient_mul (left right : Basic.CoefficientPolynomial) (degree : Nat) :
    Basic.coefficient (Basic.mul left right) degree =
      FiniteSum.Prefix.coordinateSum
        (fun leftDegree =>
          Basic.coefficient left leftDegree * Basic.coefficient right (degree -
            leftDegree))
        (degree + 1) :=
  coefficientCoefficients_mul left.coefficients right.coefficients degree

end Purelib.Polynomial.Ascending.Rational.Convolution
end
