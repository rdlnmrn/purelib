module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Convolution

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Rational monomials and zero-prefix shifts

A monomial retains a singleton coefficient behind its displayed zero prefix.
Direct readback and bounded finite convolution identify its degree, scalar
value, shifts and products.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Monomial

open Purelib.Algebra
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Construct a monomial from its displayed degree and rational value.

The retained singleton coefficient table is preceded by the exact number
of zero entries, preserving the nominal ascending polynomial representation. -/
@[expose] def monomial (degree : Nat) (coefficient : Fraction.Rational) : Ascending.Rational.Basic.CoefficientPolynomial
  :=
  Ascending.Rational.Basic.shift degree (Ascending.Rational.Basic.constant coefficient)

/-- Read a shifted polynomial below or above its retained zero prefix.

A degree inside the prefix reads zero. At or beyond the prefix, bounded natural
subtraction identifies the unchanged original table and translated degree. -/
theorem coefficient_shift (count : Nat) (polynomial : Ascending.Rational.Basic.CoefficientPolynomial)
    (degree : Nat) :
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.shift count polynomial) degree =
      if degree < count then 0 else Ascending.Rational.Basic.coefficient polynomial (degree - count) := by
  by_cases below : degree < count
  · rw [if_pos below]
    exact Ascending.Rational.Basic.coefficientCoefficients_replicate_zero_append_below
      count polynomial.coefficients degree below
  · rw [if_neg below]
    have order : count ≤ degree := Nat.le_of_not_gt below
    rw [show degree = count + (degree - count) by
      exact (Subtraction.add_sub_of_le order).symm]
    change Ascending.Rational.Basic.coefficientCoefficients
        (List.replicate count 0 ++ polynomial.coefficients)
          (count + (degree - count)) =
      Ascending.Rational.Basic.coefficientCoefficients polynomial.coefficients
        (count + (degree - count) - count)
    rw [Subtraction.add_sub_cancel_left]
    exact Ascending.Rational.Basic.coefficientCoefficients_replicate_zero_append
      count polynomial.coefficients (degree - count)

/-- A monomial reads its retained value exactly at its displayed degree.

The zero prefix separates lower degrees, while the singleton table supplies
zero at every positive translated degree. No coefficient table is normalized. -/
@[simp] theorem coefficient_monomial (monomialDegree : Nat)
    (value : Fraction.Rational) (degree : Nat) :
    Ascending.Rational.Basic.coefficient (monomial monomialDegree value) degree =
      if degree = monomialDegree then value else 0 := by
  rw [monomial, coefficient_shift]
  by_cases equal : degree = monomialDegree
  · subst degree
    rw [if_neg (Nat.not_lt_of_ge (Nat.le_refl _)), Nat.sub_self,
      Ascending.Rational.Coefficientwise.coefficient_constant, if_pos rfl, if_pos rfl]
  · by_cases below : degree < monomialDegree
    · rw [if_pos below, if_neg equal]
    · have above : monomialDegree < degree := Nat.lt_of_le_of_ne
          (Nat.le_of_not_gt below) (Ne.symm equal)
      have positive : 0 < degree - monomialDegree := by omega0
      rw [if_neg below, if_neg equal, Ascending.Rational.Coefficientwise.coefficient_constant,
        if_neg (Nat.ne_of_gt positive)]

/-- The product of two monomials has summed degree and multiplied coefficient.

The finite convolution has only the summand at the left monomial degree; all other coefficients vanish. -/
theorem coefficientwise_monomial_mul (leftDegree rightDegree : Nat)
    (left right : Fraction.Rational) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (Ascending.Rational.Basic.mul (monomial leftDegree left) (monomial rightDegree right))
      (monomial (leftDegree + rightDegree) (left * right)) := open Purelib.Algebra in by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul, coefficient_monomial]
  by_cases total : degree = leftDegree + rightDegree
  · subst degree
    rw [if_pos rfl]
    have pointwise : ∀ index, index < leftDegree + rightDegree + 1 →
        Ascending.Rational.Basic.coefficient (monomial leftDegree left) index *
            Ascending.Rational.Basic.coefficient (monomial rightDegree right)
              (leftDegree + rightDegree - index) =
          if index = leftDegree then left * right else 0 := by
      intro index order
      rw [coefficient_monomial, coefficient_monomial]
      by_cases atLeft : index = leftDegree
      · subst index
        rw [if_pos rfl, if_pos (Subtraction.add_sub_cancel_left leftDegree rightDegree),
          if_pos rfl]
      · rw [if_neg atLeft, if_neg atLeft,
          Fraction.Field.zero_mul_direct]
    rw [FiniteSum.Prefix.coordinateSum_congr_lt _ pointwise,
      FiniteSum.Prefix.coordinateSum_single (left * right) leftDegree
        (leftDegree + rightDegree + 1)
          (Nat.lt_succ_of_le (Nat.le_add_right leftDegree rightDegree))]
  · rw [if_neg total]
    have pointwise : ∀ index, index < degree + 1 →
        Ascending.Rational.Basic.coefficient (monomial leftDegree left) index *
            Ascending.Rational.Basic.coefficient (monomial rightDegree right) (degree - index) = 0 := by
      intro index order
      rw [coefficient_monomial, coefficient_monomial]
      by_cases atLeft : index = leftDegree
      · subst index
        have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ order
        have differentRemainder : degree - leftDegree ≠ rightDegree := by
          intro remainderEqual
          apply total
          calc
            degree = leftDegree + (degree - leftDegree) :=
              (Subtraction.add_sub_of_le leftLe).symm
            _ = leftDegree + rightDegree :=
              congrArg (leftDegree + ·) remainderEqual
        rw [if_pos rfl, if_neg differentRemainder,
          Fraction.Field.mul_zero_direct]
      · rw [if_neg atLeft, Fraction.Field.zero_mul_direct]
    rw [FiniteSum.Prefix.coordinateSum_congr_lt _ pointwise]
    exact FiniteSum.Prefix.coordinateSum_all_zero (fun _ => (0 : Fraction.Rational))
      (fun _ => rfl) (degree + 1)

/-- Multiplication by a monomial shifts and scales every coefficient.

Degrees below the monomial degree vanish; remaining degrees use the complementary coefficient of the other factor. -/
theorem coefficient_monomial_mul (monomialDegree : Nat)
    (value : Fraction.Rational) (polynomial : Ascending.Rational.Basic.CoefficientPolynomial) (degree : Nat) :
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Basic.mul (monomial monomialDegree value) polynomial)
      degree =
      if degree < monomialDegree then 0
      else value * Ascending.Rational.Basic.coefficient polynomial (degree - monomialDegree) := open Purelib.Algebra in
        by
  rw [Ascending.Rational.Convolution.coefficient_mul]
  by_cases below : degree < monomialDegree
  · rw [if_pos below]
    rw [FiniteSum.Prefix.coordinateSum_congr_lt (degree + 1) (by
      intro index inSum
      have different : index ≠ monomialDegree := by
        intro equal
        subst index
        exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt below)) inSum
      rw [coefficient_monomial, if_neg different,
        Fraction.Field.zero_mul_direct])]
    exact FiniteSum.Prefix.coordinateSum_all_zero (fun _ => (0 : Fraction.Rational))
      (fun _ => rfl) (degree + 1)
  · rw [if_neg below]
    have inSum : monomialDegree < degree + 1 :=
      Nat.lt_succ_of_le (Nat.le_of_not_gt below)
    have pointwise : ∀ index, index < degree + 1 →
        Ascending.Rational.Basic.coefficient (monomial monomialDegree value) index *
            Ascending.Rational.Basic.coefficient polynomial (degree - index) =
          if index = monomialDegree then
            value * Ascending.Rational.Basic.coefficient polynomial (degree - monomialDegree)
          else 0 := by
      intro index indexBound
      rw [coefficient_monomial]
      by_cases equal : index = monomialDegree
      · subst index
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg equal,
          Fraction.Field.zero_mul_direct, if_neg equal]
    rw [FiniteSum.Prefix.coordinateSum_congr_lt (degree + 1) pointwise]
    exact FiniteSum.Prefix.coordinateSum_single
      (value * Ascending.Rational.Basic.coefficient polynomial (degree - monomialDegree))
      monomialDegree (degree + 1) inSum

/-- Equal rational values give coefficientwise equal monomials at the same degree. -/
theorem coefficientwise_monomial_value (degree : Nat)
    {left right : Fraction.Rational} (equal : left = right) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (monomial degree left) (monomial degree right) := by
  rw [equal]
  exact Ascending.Rational.Coefficientwise.coefficientwise_refl _

/-- A degree-zero monomial is coefficientwise equal to its constant polynomial. -/
theorem coefficientwise_monomial_zero (value : Fraction.Rational) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (monomial 0 value) (Ascending.Rational.Basic.constant value)
      := by
  intro degree
  rw [coefficient_monomial, Ascending.Rational.Coefficientwise.coefficient_constant]

/-- Opposite coefficients at the same monomial degree add to zero coefficientwise. -/
theorem coefficientwise_monomial_cancel (degree : Nat)
    (value : Fraction.Rational) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (Ascending.Rational.Basic.add (monomial degree (-value)) (monomial degree value)) Ascending.Rational.Basic.zero :=
        by
  intro outputDegree
  rw [Ascending.Rational.Basic.coefficient_add, coefficient_monomial, coefficient_monomial,
    Ascending.Rational.Coefficientwise.coefficient_zero]
  by_cases equal : outputDegree = degree
  · rw [if_pos equal, if_pos equal]
    ring1
  · rw [if_neg equal, if_neg equal]
    ring1

end Purelib.Polynomial.Ascending.Rational.Monomial
end
