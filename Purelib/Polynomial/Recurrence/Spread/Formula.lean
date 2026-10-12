module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Group.Negation
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: spread polynomials

Spread polynomials are primitive-recursive finite expressions.  No sequence
or limit object is introduced: evaluating index `n` performs exactly `n`
finite recurrence steps in the coefficient field.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Formula

variable {K : Type*} [ExplicitField K]

/-- The denominator-free spread formula needs only one formal offset whose
square is `-4s(1-s)`.  This commutative-ring form is stronger than the
source's presentation through two separately selected square roots. -/
theorem spread_polynomial_offset_formula_cleared
    {R : Type*} [CommRing R]
    (value offset : R)
    (offsetEquation : offset ^ 2 = -(4 * value * (1 - value)))
    (index : Nat) :
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
      2 - (1 - 2 * value + offset) ^ index -
        (1 - 2 * value - offset) ^ index := by
  let center := 1 - 2 * value
  let positive := center + offset
  let negative := center - offset
  have positiveQuadratic :
      positive ^ 2 = 2 * center * positive - 1 := by
    unfold positive center
    calc
      (1 - 2 * value + offset) ^ 2 =
          (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * offset + offset ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * offset -
              4 * value * (1 - value) := by
                rw [offsetEquation]
                ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value + offset) - 1 := by ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * center * negative - 1 := by
    unfold negative center
    calc
      (1 - 2 * value - offset) ^ 2 =
          (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * offset + offset ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * offset -
              4 * value * (1 - value) := by
                rw [offsetEquation]
                ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value - offset) - 1 := by ring1
  change
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
      2 - positive ^ index - negative ^ index
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          unfold Recurrence.Spread.Basic.spreadPolynomial
          ring1
      | succ index =>
          cases index with
          | zero =>
              unfold Recurrence.Spread.Basic.spreadPolynomial positive negative center
              ring1
          | succ index =>
              let priorIndex := index
              have previousFormula := inductionHypothesis (priorIndex + 1)
                (Nat.lt_succ_self (priorIndex + 1))
              have beforePreviousFormula := inductionHypothesis priorIndex
                (Nat.lt_trans (Nat.lt_succ_self priorIndex)
                  (Nat.lt_succ_self (priorIndex + 1)))
              have positiveRecurrence :
                  positive ^ (priorIndex + 2) =
                    2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by
                calc
                  positive ^ (priorIndex + 2) =
                      positive ^ priorIndex * positive ^ 2 := by
                        rw [pow_add]
                  _ = positive ^ priorIndex *
                      (2 * center * positive - 1) := by
                        rw [positiveQuadratic]
                  _ = 2 * center * (positive ^ priorIndex * positive) -
                      positive ^ priorIndex := by
                        generalize positive ^ priorIndex = priorPower
                        ring1
                  _ = 2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by rw [pow_succ]
              have negativeRecurrence :
                  negative ^ (priorIndex + 2) =
                    2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by
                calc
                  negative ^ (priorIndex + 2) =
                      negative ^ priorIndex * negative ^ 2 := by
                        rw [pow_add]
                  _ = negative ^ priorIndex *
                      (2 * center * negative - 1) := by
                        rw [negativeQuadratic]
                  _ = 2 * center * (negative ^ priorIndex * negative) -
                      negative ^ priorIndex := by
                        generalize negative ^ priorIndex = priorPower
                        ring1
                  _ = 2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by rw [pow_succ]
              change
                4 * Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 2) value =
                  2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2)
              rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
              calc
                4 *
                    (2 * (1 - 2 * value) *
                        Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 1) value -
                      Recurrence.Spread.Basic.spreadPolynomial priorIndex value + 2 * value) =
                  2 * center *
                      (4 * Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 1) value) -
                    4 * Recurrence.Spread.Basic.spreadPolynomial priorIndex value + 8 * value := by
                      unfold center
                      ring1
                _ = 2 * center *
                      (2 - positive ^ (priorIndex + 1) -
                        negative ^ (priorIndex + 1)) -
                    (2 - positive ^ priorIndex - negative ^ priorIndex) +
                    8 * value := by
                      rw [previousFormula, beforePreviousFormula]
                _ = 2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2) := by
                      rw [positiveRecurrence, negativeRecurrence]
                      unfold center
                      generalize positive ^ (priorIndex + 1) = positiveNextPower
                      generalize negative ^ (priorIndex + 1) = negativeNextPower
                      generalize positive ^ priorIndex = positivePriorPower
                      generalize negative ^ priorIndex = negativePriorPower
                      ring1

/-- A denominator-cleared power formula for spread polynomials.

Given a square root of four times the spread and its complement, and an element squaring to minus one, four times the
spread polynomial is the difference of the two displayed powers from two. -/
theorem spread_polynomial_formula_cleared
    (value root imaginary : K)
    (rootEquation : 4 * value * (1 - value) = root ^ 2)
    (imaginaryEquation : imaginary ^ 2 = -1)
    (index : Nat) :
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
      2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index := by
  let center := 1 - 2 * value
  let positive := center + imaginary * root
  let negative := center - imaginary * root
  have positiveQuadratic :
      positive ^ 2 = 2 * center * positive - 1 := by
    unfold positive center
    calc
      (1 - 2 * value + imaginary * root) ^ 2 =
          (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * imaginary * root +
            imaginary ^ 2 * root ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * imaginary * root -
            4 * value * (1 - value) := by
              rw [imaginaryEquation, ← rootEquation]
              ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value + imaginary * root) - 1 := by ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * center * negative - 1 := by
    unfold negative center
    calc
      (1 - 2 * value - imaginary * root) ^ 2 =
          (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * imaginary * root +
            imaginary ^ 2 * root ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * imaginary * root -
            4 * value * (1 - value) := by
              rw [imaginaryEquation, ← rootEquation]
              ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value - imaginary * root) - 1 := by ring1
  change
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
      2 - positive ^ index - negative ^ index
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          unfold Recurrence.Spread.Basic.spreadPolynomial
          ring1
      | succ index =>
          cases index with
          | zero =>
              unfold Recurrence.Spread.Basic.spreadPolynomial positive negative center
              ring1
          | succ index =>
              let priorIndex := index
              have previousFormula := inductionHypothesis (priorIndex + 1)
                (Nat.lt_succ_self (priorIndex + 1))
              have beforePreviousFormula := inductionHypothesis priorIndex
                (Nat.lt_trans (Nat.lt_succ_self priorIndex)
                  (Nat.lt_succ_self (priorIndex + 1)))
              have positiveRecurrence :
                  positive ^ (priorIndex + 2) =
                    2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by
                calc
                  positive ^ (priorIndex + 2) =
                      positive ^ priorIndex * positive ^ 2 := by
                        rw [pow_add]
                  _ = positive ^ priorIndex *
                      (2 * center * positive - 1) := by
                        rw [positiveQuadratic]
                  _ = 2 * center * (positive ^ priorIndex * positive) -
                      positive ^ priorIndex := by
                        generalize positive ^ priorIndex = priorPower
                        ring1
                  _ = 2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by rw [pow_succ]
              have negativeRecurrence :
                  negative ^ (priorIndex + 2) =
                    2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by
                calc
                  negative ^ (priorIndex + 2) =
                      negative ^ priorIndex * negative ^ 2 := by
                        rw [pow_add]
                  _ = negative ^ priorIndex *
                      (2 * center * negative - 1) := by
                        rw [negativeQuadratic]
                  _ = 2 * center * (negative ^ priorIndex * negative) -
                      negative ^ priorIndex := by
                        generalize negative ^ priorIndex = priorPower
                        ring1
                  _ = 2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by rw [pow_succ]
              change
                4 * Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 2) value =
                  2 - positive ^ (priorIndex + 2) - negative ^ (priorIndex + 2)
              rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
              calc
                4 *
                    (2 * (1 - 2 * value) *
                        Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 1) value -
                      Recurrence.Spread.Basic.spreadPolynomial priorIndex value + 2 * value) =
                  2 * center *
                      (4 * Recurrence.Spread.Basic.spreadPolynomial (priorIndex + 1) value) -
                    4 * Recurrence.Spread.Basic.spreadPolynomial priorIndex value + 8 * value := by
                      unfold center
                      ring1
                _ = 2 * center *
                      (2 - positive ^ (priorIndex + 1) -
                        negative ^ (priorIndex + 1)) -
                    (2 - positive ^ priorIndex - negative ^ priorIndex) +
                    8 * value := by
                      rw [previousFormula, beforePreviousFormula]
                _ = 2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2) := by
                      rw [positiveRecurrence, negativeRecurrence]
                      unfold center
                      generalize positive ^ (priorIndex + 1) = positiveNextPower
                      generalize negative ^ (priorIndex + 1) = negativeNextPower
                      generalize positive ^ priorIndex = positivePriorPower
                      generalize negative ^ priorIndex = negativePriorPower
                      ring1

/-- Evaluate a spread polynomial using two conjugate powers.

The supplied root equations determine the two bases; four must be nonzero so the cleared identity can be divided by
four. -/
theorem spread_polynomial_formula
    (value root imaginary : K)
    (fourNonzero : (4 : K) ≠ 0)
    (rootEquation : 4 * value * (1 - value) = root ^ 2)
    (imaginaryEquation : imaginary ^ 2 = -1)
    (index : Nat) :
    Recurrence.Spread.Basic.spreadPolynomial index value =
      (2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index) / 4 := by
  have cleared := spread_polynomial_formula_cleared value root imaginary
    rootEquation imaginaryEquation index
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    Recurrence.Spread.Basic.spreadPolynomial index value * 4 =
        4 * Recurrence.Spread.Basic.spreadPolynomial index value := by ring1
    _ = 2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index := cleared
    _ = ((2 - (1 - 2 * value + imaginary * root) ^ index -
          (1 - 2 * value - imaginary * root) ^ index) / 4) * 4 :=
      (ExplicitField.div_mul_cancel _ fourNonzero).symm
end Purelib.Polynomial.Recurrence.Spread.Formula

end
