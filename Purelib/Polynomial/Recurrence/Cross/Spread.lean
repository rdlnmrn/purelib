module
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Spread

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The cross polynomial at a displayed input equals one minus the spread polynomial at its complementary input. -/
theorem crossPolynomial_eq_one_sub_spreadPolynomial
    (index : Nat) (value : K) :
    Recurrence.Cross.Basic.crossPolynomial index value =
      1 - Recurrence.Spread.Basic.spreadPolynomial index (1 - value) := by
  let relationAt := fun current : Nat =>
    Recurrence.Cross.Basic.crossPolynomial current value =
      1 - Recurrence.Spread.Basic.spreadPolynomial current (1 - value)
  have allPairs : ∀ current : Nat,
      relationAt current ∧ relationAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold relationAt Recurrence.Cross.Basic.crossPolynomial Recurrence.Spread.Basic.spreadPolynomial
          ring1
        · unfold relationAt Recurrence.Cross.Basic.crossPolynomial Recurrence.Spread.Basic.spreadPolynomial
          ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold relationAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [Recurrence.Cross.Basic.crossPolynomial_succ_succ, Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            inductionHypothesis.1, inductionHypothesis.2]
          ring1
  exact (allPairs index).1

/-- Cross and spread polynomial values at complementary inputs sum to one at every finite index. -/
theorem exercise_8_17
    (index : Nat) (crossValue spreadValue : K)
    (complementary : crossValue + spreadValue = 1) :
    Recurrence.Cross.Basic.crossPolynomial index crossValue +
      Recurrence.Spread.Basic.spreadPolynomial index spreadValue = 1 := by
  have spreadValueEquation : spreadValue = 1 - crossValue := by
    calc
      spreadValue = (crossValue + spreadValue) - crossValue := by ring1
      _ = 1 - crossValue := by rw [complementary]
  rw [crossPolynomial_eq_one_sub_spreadPolynomial, spreadValueEquation]
  ring1

/-- At the same input, even cross values complement the corresponding spreads and odd cross values equal them. -/
theorem crossPolynomial_even_and_odd (index : Nat) (value : K) :
    Recurrence.Cross.Basic.crossPolynomial (index + index) value =
        1 - Recurrence.Spread.Basic.spreadPolynomial (index + index) value ∧
      Recurrence.Cross.Basic.crossPolynomial (index + index + 1) value =
        Recurrence.Spread.Basic.spreadPolynomial (index + index + 1) value := by
  induction index with
  | zero =>
      constructor <;> unfold Recurrence.Cross.Basic.crossPolynomial Recurrence.Spread.Basic.spreadPolynomial <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨evenFormula, oddFormula⟩
      have nextEven :
          Recurrence.Cross.Basic.crossPolynomial (Nat.succ index + Nat.succ index) value =
            1 - Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index + Nat.succ index) value := by
        rw [show Nat.succ index + Nat.succ index = index + index + 2 by omega0]
        rw [Recurrence.Cross.Basic.crossPolynomial_succ_succ, Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
          evenFormula, oddFormula]
        ring1
      have nextOdd :
          Recurrence.Cross.Basic.crossPolynomial (Nat.succ index + Nat.succ index + 1) value =
            Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index + Nat.succ index + 1) value := by
        rw [show Nat.succ index + Nat.succ index + 1 =
          (index + index + 1) + 2 by omega0]
        rw [Recurrence.Cross.Basic.crossPolynomial_succ_succ, Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
          oddFormula]
        rw [show index + index + 2 =
          Nat.succ index + Nat.succ index by omega0]
        rw [nextEven]
        ring1
      exact ⟨nextEven, nextOdd⟩
end Purelib.Polynomial.Recurrence.Cross.Spread

end
