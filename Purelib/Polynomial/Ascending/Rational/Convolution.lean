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

/-- Split a degree-weighted convolution into the two derivative contributions.

For finite sums through degree `degree + 1`, distribute the total degree between the left and right indices. The zero
endpoint weights remove the extra endpoints. -/
theorem convolution_derivative_identity
    (left right : Nat → Fraction.Rational) (degree : Nat) :
    ((degree + 1 : Nat) : Fraction.Rational) *
        FiniteSum.Prefix.coordinateSum
          (fun leftDegree =>
            left leftDegree * right (degree + 1 - leftDegree))
          (degree + 2) =
      FiniteSum.Prefix.coordinateSum
          (fun index =>
            ((index + 1 : Nat) : Fraction.Rational) * left (index + 1) *
              right (degree - index))
          (degree + 1) +
        FiniteSum.Prefix.coordinateSum
          (fun index =>
            left index * ((degree - index + 1 : Nat) : Fraction.Rational) *
              right (degree - index + 1))
          (degree + 1) := by
  let full : Nat → Fraction.Rational := fun index =>
    left index * right (degree + 1 - index)
  let leftWeighted : Nat → Fraction.Rational := fun index =>
    (index : Fraction.Rational) * full index
  let rightWeighted : Nat → Fraction.Rational := fun index =>
    ((degree + 1 - index : Nat) : Fraction.Rational) * full index
  have leftExpanded :
      FiniteSum.Prefix.coordinateSum leftWeighted (degree + 2) =
        FiniteSum.Prefix.coordinateSum
          (fun index =>
            ((index + 1 : Nat) : Fraction.Rational) * left (index + 1) *
              right (degree - index))
          (degree + 1) := by
    rw [FiniteSum.Prefix.coordinateSum_succ_front]
    have headZero : leftWeighted 0 = 0 := by
      dsimp only [leftWeighted, full]
      rw [Nat.cast_zero, Fraction.Field.zero_mul_direct]
    rw [headZero, Fraction.Field.zero_add]
    apply FiniteSum.Prefix.coordinateSum_congr
    intro index
    dsimp only [leftWeighted, full]
    rw [Nat.succ_sub_succ]
    ring1
  have rightExpanded :
      FiniteSum.Prefix.coordinateSum rightWeighted (degree + 2) =
        FiniteSum.Prefix.coordinateSum
          (fun index =>
            left index * ((degree - index + 1 : Nat) : Fraction.Rational) *
              right (degree - index + 1))
          (degree + 1) := by
    rw [FiniteSum.Prefix.coordinateSum_succ]
    have finalZero : rightWeighted (degree + 1) = 0 := by
      dsimp only [rightWeighted, full]
      rw [Nat.sub_self, Nat.cast_zero,
        Fraction.Field.zero_mul_direct]
    rw [finalZero, Fraction.Field.add_comm,
      Fraction.Field.zero_add]
    apply FiniteSum.Prefix.coordinateSum_congr_lt
    intro index order
    dsimp only [rightWeighted, full]
    rw [show degree + 1 - index = degree - index + 1 by omega0]
    ring1
  rw [← leftExpanded, ← rightExpanded, ← FiniteSum.Prefix.coordinateSum_add,
    FiniteSum.Prefix.coordinateSum_scale_left]
  apply FiniteSum.Prefix.coordinateSum_congr_lt
  intro index order
  dsimp only [leftWeighted, rightWeighted, full]
  have indexLe : index ≤ degree + 1 := Nat.le_of_lt_succ order
  have castSplit :
      (index : Fraction.Rational) + ((degree + 1 - index : Nat) : Fraction.Rational) =
        ((degree + 1 : Nat) : Fraction.Rational) := by
    rw [← NatCast.add, Subtraction.add_sub_of_le indexLe]
  rw [← castSplit]
  ring1

/-- Each product-table coefficient is its finite convolution sum.

At degree `degree`, sum over left indices from zero through that degree, pairing each with the complementary right
index. -/
theorem coefficientCoefficients_mul (left right : List Fraction.Rational) :
    ∀ degree,
      Ascending.Rational.Basic.coefficientCoefficients (Ascending.Rational.Basic.mulCoefficients left right) degree =
        FiniteSum.Prefix.coordinateSum
          (fun leftDegree =>
            Ascending.Rational.Basic.coefficientCoefficients left leftDegree *
              Ascending.Rational.Basic.coefficientCoefficients right (degree - leftDegree))
          (degree + 1) := by
  induction left with
  | nil =>
      intro degree
      rw [Ascending.Rational.Basic.mulCoefficients]
      change 0 = FiniteSum.Prefix.coordinateSum
        (fun leftDegree =>
          Ascending.Rational.Basic.coefficientCoefficients ([] : List Fraction.Rational) leftDegree *
            Ascending.Rational.Basic.coefficientCoefficients right (degree - leftDegree))
        (degree + 1)
      have allZero : ∀ count,
          FiniteSum.Prefix.coordinateSum
              (fun leftDegree =>
                Ascending.Rational.Basic.coefficientCoefficients ([] : List Fraction.Rational) leftDegree *
                  Ascending.Rational.Basic.coefficientCoefficients right (degree - leftDegree)) count =
            0 := by
        intro count
        induction count with
        | zero => rfl
        | succ count inductionHypothesis =>
            rw [FiniteSum.Prefix.coordinateSum_succ, inductionHypothesis,
              Ascending.Rational.Basic.coefficientCoefficients_nil,
              Fraction.Field.zero_mul_direct,
              Fraction.Field.zero_add]
      exact (allZero (degree + 1)).symm
  | cons head tail inductionHypothesis =>
      intro degree
      cases degree with
      | zero =>
          rw [Ascending.Rational.Basic.coefficientCoefficients_mul_zero,
            FiniteSum.Prefix.coordinateSum_succ, FiniteSum.Prefix.coordinateSum_zero]
          simp only [Nat.zero_sub, Ascending.Rational.Basic.coefficientCoefficients_cons_zero]
          ring1
      | succ degree =>
          rw [Ascending.Rational.Basic.coefficientCoefficients_mul_cons_succ,
            FiniteSum.Prefix.coordinateSum_succ_front]
          simp only [Ascending.Rational.Basic.coefficientCoefficients_cons_zero, Nat.sub_zero]
          rw [Ascending.Rational.Basic.coefficientCoefficients_map_scale]
          rw [inductionHypothesis degree]
          apply congrArg
            (head * Ascending.Rational.Basic.coefficientCoefficients right (degree + 1) + ·)
          apply FiniteSum.Prefix.coordinateSum_congr
          intro index
          rw [Ascending.Rational.Basic.coefficientCoefficients_cons_succ,
            Nat.succ_sub_succ_eq_sub]

/-- The coefficient of a polynomial product is the finite sum over complementary degrees. -/
@[simp] theorem coefficient_mul (left right : Ascending.Rational.Basic.CoefficientPolynomial) (degree : Nat) :
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.mul left right) degree =
      FiniteSum.Prefix.coordinateSum
        (fun leftDegree =>
          Ascending.Rational.Basic.coefficient left leftDegree * Ascending.Rational.Basic.coefficient right (degree -
            leftDegree))
        (degree + 1) :=
  coefficientCoefficients_mul left.coefficients right.coefficients degree

end Purelib.Polynomial.Ascending.Rational.Convolution
end
