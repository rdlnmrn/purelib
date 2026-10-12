module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Finite uniqueness of rational polynomial remainders

Two displayed division identities give a polynomial product whose degree is
too small unless the quotient difference vanishes.  All coefficient equality
uses the explicit bounded rational grid, and division remains the existing
executable dense long-division calculation.
-/

namespace Purelib.Polynomial.Dense.Rational.Division

open Purelib.Data.Rat Purelib.Polynomial
open Purelib.Algebra.Group

attribute [local instance high] Negation.subNegZeroMonoid

public section
/-- Descending dense polynomial data over constructive rationals.

The exact alias retains the original finite coefficient representation and
its executable normalization and long-division operations. -/
abbrev CoefficientPolynomial := Dense.Basic.DensePolynomial Fraction.Rational

/-- Division by a represented zero polynomial returns the normalized dividend.

The original normalized divisor satisfies the same zero test, which selects
the first stopping branch of the retained finite long-division calculation. -/
theorem remainder_of_divisor_zero (dividend divisor : CoefficientPolynomial) (zero : divisor.isZero = true) :
    (Dense.Basic.DensePolynomial.divMod dividend divisor).remainder = dividend.normalize := by
  have stopping : (divisor.normalize.isZero || dividend.normalize.isZero ||
      decide (dividend.normalize.natDegree < divisor.normalize.natDegree)) = true := by
    rw [Dense.Basic.DensePolynomial.isZero_normalize, zero]
    exact Eq.refl _
  unfold Dense.Basic.DensePolynomial.divMod
  rw [Dense.Basic.DensePolynomial.divLoop_succ, if_pos stopping]

/-- A normalized small candidate satisfying the division identity is the remainder.

The divisor's nonzero test and the candidate's strict coefficient-count bound
force the quotient difference to vanish by the finite product-degree identity. -/
theorem remainder_unique (dividend divisor quotient remainder : CoefficientPolynomial)
    (nonzero : divisor.isZero = false)
    (normalized : remainder.normalize = remainder)
    (small : remainder.degreeCount < divisor.degreeCount)
    (identity : ∀ point : Fraction.Rational,
      remainder.eval point + divisor.eval point * quotient.eval point = dividend.eval point) :
    remainder = (Dense.Basic.DensePolynomial.divMod dividend divisor).remainder := by
  let actual := Dense.Basic.DensePolynomial.divMod dividend divisor
  let difference := actual.quotient - quotient
  have productEq : divisor * difference = remainder - actual.remainder := by
    apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
      (Dense.Basic.DensePolynomial.normalize_mul _ _) (Dense.Basic.DensePolynomial.normalize_sub _ _)
    intro point
    have actualEq := Dense.Basic.DensePolynomial.divMod_eval_equation dividend divisor point
    have candidateEq := identity point
    change actual.remainder.eval point + divisor.eval point * actual.quotient.eval point = _ at actualEq
    simp only [difference, Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_sub]
    calc
      _ = (actual.remainder.eval point + divisor.eval point * actual.quotient.eval point) -
          (remainder.eval point + divisor.eval point * quotient.eval point) +
            (remainder.eval point - actual.remainder.eval point) := by ring1
      _ = _ := by rw [actualEq, candidateEq]; ring1
  have differenceZero : difference.isZero = true := by
    cases zero : difference.isZero with
    | true => rfl
    | false =>
      have actualSmall := Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt dividend divisor nonzero
      have subBound := Dense.Basic.DensePolynomial.degreeCount_sub_le_of_normalized normalized (q := actual.remainder)
      have productNonzero := Dense.Basic.DensePolynomial.isZero_mul_eq_false nonzero zero
      have productDegree := Dense.Basic.DensePolynomial.natDegree_mul nonzero zero
      have productCount := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount productNonzero
      have divisorCount := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
      rw [productEq] at productDegree productCount
      change actual.remainder.degreeCount < divisor.degreeCount at actualSmall
      have remainderSmall : (remainder - actual.remainder).degreeCount <
          divisor.degreeCount := by
        apply Nat.lt_of_le_of_lt subBound
        rw [Purelib.Data.Nat.Order.max_eq_natMax]
        change (if remainder.degreeCount ≤ actual.remainder.degreeCount then
          actual.remainder.degreeCount else remainder.degreeCount) < divisor.degreeCount
        by_cases ordered : remainder.degreeCount ≤ actual.remainder.degreeCount
        · rw [if_pos ordered]
          exact actualSmall
        · rw [if_neg ordered]
          exact small
      clear subBound
      omega
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq normalized
    (Dense.Basic.DensePolynomial.divMod_remainder_normalize dividend divisor)
  intro point
  have productValue := congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval point) productEq
  rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero differenceZero,
    Dense.Basic.DensePolynomial.eval_sub] at productValue
  have equal : remainder.eval point - actual.remainder.eval point = 0 := by
    calc
      _ = divisor.eval point * 0 := productValue.symm
      _ = 0 := by ring1
  calc
    remainder.eval point = (remainder.eval point - actual.remainder.eval point) +
        actual.remainder.eval point := by ring1
    _ = actual.remainder.eval point := by rw [equal]; ring1

end

end Purelib.Polynomial.Dense.Rational.Division
