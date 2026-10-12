module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

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

namespace Purelib.Polynomial.Recurrence.Spread.Period

variable {K : Type*} [ExplicitField K]

/-- A second-order spread-polynomial orbit repeats at every later requested
index once two consecutive finite seeds repeat. -/
theorem spreadPolynomial_period
    (period : Nat) (value : K)
    (zeroSeed : Recurrence.Spread.Basic.spreadPolynomial period value = 0)
    (oneSeed : Recurrence.Spread.Basic.spreadPolynomial (period + 1) value = value)
    (index : Nat) :
    Recurrence.Spread.Basic.spreadPolynomial (index + period) value =
      Recurrence.Spread.Basic.spreadPolynomial index value := by
  let repeatsAt := fun current : Nat =>
    Recurrence.Spread.Basic.spreadPolynomial (current + period) value =
      Recurrence.Spread.Basic.spreadPolynomial current value
  have allPairs : ∀ current : Nat,
      repeatsAt current ∧ repeatsAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold repeatsAt
          simpa only [Nat.zero_add, Recurrence.Spread.Basic.spreadPolynomial_zero] using zeroSeed
        · unfold repeatsAt
          rw [show 0 + 1 + period = period + 1 by omega0]
          rw [oneSeed]
          change value = Recurrence.Spread.Basic.spreadPolynomial 1 value
          rw [Recurrence.Spread.Basic.spreadPolynomial_one]
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold repeatsAt
          have middleRepeat :
              Recurrence.Spread.Basic.spreadPolynomial (current + period + 1) value =
                Recurrence.Spread.Basic.spreadPolynomial (current + 1) value := by
            calc
              Recurrence.Spread.Basic.spreadPolynomial (current + period + 1) value =
                  Recurrence.Spread.Basic.spreadPolynomial (current + 1 + period) value := by
                congr 1
                omega0
              _ = Recurrence.Spread.Basic.spreadPolynomial (current + 1) value :=
                inductionHypothesis.2
          rw [show Nat.succ current + 1 + period =
            (current + period) + 2 by omega0]
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ, Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            inductionHypothesis.1, middleRepeat]
  exact (allPairs index).1
end Purelib.Polynomial.Recurrence.Spread.Period

end
