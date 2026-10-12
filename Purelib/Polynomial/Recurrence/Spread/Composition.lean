module
import Purelib.Data.Nat.Multiplication
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Recurrence.Spread.Addition
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
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

namespace Purelib.Polynomial.Recurrence.Spread.Composition

variable {K : Type*} [ExplicitField K]

open Purelib.Data.Nat in
/-- Composing two spread polynomials multiplies their finite indices.

The identity holds in the explicit coefficient field and follows from the finite recurrence and addition formula. -/
theorem spread_polynomial_composition
    (outer inner : Nat) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial outer (Recurrence.Spread.Basic.spreadPolynomial inner value) =
      Recurrence.Spread.Basic.spreadPolynomial (outer * inner) value := by
  let compositionAt := fun current : Nat =>
    Recurrence.Spread.Basic.spreadPolynomial current (Recurrence.Spread.Basic.spreadPolynomial inner value) =
      Recurrence.Spread.Basic.spreadPolynomial (current * inner) value
  have allPairs : ∀ current : Nat,
      compositionAt current ∧ compositionAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold compositionAt
          simp only [Recurrence.Spread.Basic.spreadPolynomial_zero, Nat.zero_mul, -eq_self, -iff_self]
          rfl
        · unfold compositionAt
          simp only [Nat.zero_add, Recurrence.Spread.Basic.spreadPolynomial_one, Nat.one_mul, -eq_self, -iff_self]
          rfl
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · change compositionAt (Nat.succ current + 1)
          have currentFormula :
              Recurrence.Spread.Basic.spreadPolynomial current (Recurrence.Spread.Basic.spreadPolynomial inner value) =
                Recurrence.Spread.Basic.spreadPolynomial (current * inner) value := by
            exact inductionHypothesis.1
          have nextFormula :
              Recurrence.Spread.Basic.spreadPolynomial (current + 1)
                  (Recurrence.Spread.Basic.spreadPolynomial inner value) =
                Recurrence.Spread.Basic.spreadPolynomial ((current + 1) * inner) value := by
            exact inductionHypothesis.2
          unfold compositionAt
          rw [show Nat.succ current + 1 = current + 2 by rfl]
          rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ, currentFormula, nextFormula]
          have additionFormula := Recurrence.Spread.Addition.spread_polynomial_addition
            (current * inner) inner value
          calc
            2 * (1 - 2 * Recurrence.Spread.Basic.spreadPolynomial inner value) *
                  Recurrence.Spread.Basic.spreadPolynomial ((current + 1) * inner) value -
                Recurrence.Spread.Basic.spreadPolynomial (current * inner) value +
                2 * Recurrence.Spread.Basic.spreadPolynomial inner value =
              2 * (Recurrence.Spread.Basic.spreadPolynomial (current * inner + inner) value +
                    Recurrence.Spread.Basic.spreadPolynomial inner value -
                    2 * Recurrence.Spread.Basic.spreadPolynomial (current * inner + inner) value *
                      Recurrence.Spread.Basic.spreadPolynomial inner value) -
                Recurrence.Spread.Basic.spreadPolynomial (current * inner) value := by
                  rw [Multiplication.right_distrib]
                  simp only [Nat.one_mul]
                  ring1
            _ = (Recurrence.Spread.Basic.spreadPolynomial
                    (current * inner + inner + inner) value +
                  Recurrence.Spread.Basic.spreadPolynomial (current * inner) value) -
                Recurrence.Spread.Basic.spreadPolynomial (current * inner) value := by
                  rw [additionFormula]
            _ = Recurrence.Spread.Basic.spreadPolynomial
                  (current * inner + inner + inner) value := by ring1
            _ = Recurrence.Spread.Basic.spreadPolynomial ((current + 2) * inner) value := by
                  apply congrArg (fun index => Recurrence.Spread.Basic.spreadPolynomial index value)
                  rw [Multiplication.right_distrib, Nat.two_mul, ← Nat.add_assoc]
  exact (allPairs outer).1

/-- The finite spread-polynomial evaluations commute under composition. -/
theorem spread_polynomial_composition_commutative
    (first second : Nat) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial first (Recurrence.Spread.Basic.spreadPolynomial second value) =
      Recurrence.Spread.Basic.spreadPolynomial second (Recurrence.Spread.Basic.spreadPolynomial first value) := by
  calc
    Recurrence.Spread.Basic.spreadPolynomial first (Recurrence.Spread.Basic.spreadPolynomial second value) =
        Recurrence.Spread.Basic.spreadPolynomial (first * second) value :=
      spread_polynomial_composition first second value
    _ = Recurrence.Spread.Basic.spreadPolynomial (second * first) value := by
      rw [Nat.mul_comm]
    _ = Recurrence.Spread.Basic.spreadPolynomial second (Recurrence.Spread.Basic.spreadPolynomial first value) :=
      (spread_polynomial_composition second first value).symm

open Purelib.Data.Nat in
/-- The finite spread-polynomial composition law respects associativity of index multiplication. -/
theorem spread_polynomial_composition_associative
    (first second third : Nat) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial (first * second)
        (Recurrence.Spread.Basic.spreadPolynomial third value) =
      Recurrence.Spread.Basic.spreadPolynomial first
        (Recurrence.Spread.Basic.spreadPolynomial (second * third) value) := by
  calc
    Recurrence.Spread.Basic.spreadPolynomial (first * second) (Recurrence.Spread.Basic.spreadPolynomial third value) =
        Recurrence.Spread.Basic.spreadPolynomial ((first * second) * third) value :=
      spread_polynomial_composition (first * second) third value
    _ = Recurrence.Spread.Basic.spreadPolynomial (first * (second * third)) value := by
      rw [Multiplication.mul_assoc]
    _ = Recurrence.Spread.Basic.spreadPolynomial first
          (Recurrence.Spread.Basic.spreadPolynomial (second * third) value) :=
      (spread_polynomial_composition first (second * third) value).symm

end Purelib.Polynomial.Recurrence.Spread.Composition

end
