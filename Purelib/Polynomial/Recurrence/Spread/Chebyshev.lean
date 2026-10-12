module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the finite Chebyshev identity

Only the polynomial recurrence in Exercise 8.4 is retained.  The source's
alternative notation using a square root in a completed decimal field is not
needed for, and adds no content to, this exact identity.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Chebyshev

variable {K : Type*} [ExplicitField K]

/-- Twice a spread polynomial equals one minus a translated Chebyshev polynomial.

The cleared identity holds at every natural index over the supplied explicit field. -/
theorem exercise_8_4_cleared (index : Nat) (value : K) :
    2 * Recurrence.Spread.Basic.spreadPolynomial index value =
      1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) := by
  let identityAt := fun current : Nat =>
    2 * Recurrence.Spread.Basic.spreadPolynomial current value =
      1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst current (1 - 2 * value)
  have allPairs : ∀ current : Nat,
      identityAt current ∧ identityAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold identityAt Recurrence.Spread.Basic.spreadPolynomial Recurrence.Chebyshev.First.Basic.chebyshevFirst
          ring1
        · unfold identityAt Recurrence.Spread.Basic.spreadPolynomial Recurrence.Chebyshev.First.Basic.chebyshevFirst
          ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold identityAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ]
          calc
            2 *
                (2 * (1 - 2 * value) *
                    Recurrence.Spread.Basic.spreadPolynomial (current + 1) value -
                  Recurrence.Spread.Basic.spreadPolynomial current value + 2 * value) =
              2 * (1 - 2 * value) *
                  (2 * Recurrence.Spread.Basic.spreadPolynomial (current + 1) value) -
                2 * Recurrence.Spread.Basic.spreadPolynomial current value + 4 * value := by ring1
            _ = 2 * (1 - 2 * value) *
                  (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst (current + 1) (1 - 2 * value)) -
                (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst current (1 - 2 * value)) +
                4 * value := by
              rw [inductionHypothesis.1, inductionHypothesis.2]
            _ = 1 -
                (2 * (1 - 2 * value) *
                    Recurrence.Chebyshev.First.Basic.chebyshevFirst (current + 1) (1 - 2 * value) -
                  Recurrence.Chebyshev.First.Basic.chebyshevFirst current (1 - 2 * value)) := by ring1
  exact (allPairs index).1

/-- Express a spread polynomial through a translated Chebyshev polynomial.

Division by two requires that two be nonzero in the supplied explicit field. -/
theorem exercise_8_4
    (index : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Basic.spreadPolynomial index value =
      (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value)) / 2 := by
  apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
  calc
    Recurrence.Spread.Basic.spreadPolynomial index value * 2 =
        2 * Recurrence.Spread.Basic.spreadPolynomial index value := by ring1
    _ = 1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) :=
      exercise_8_4_cleared index value
    _ = ((1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value)) / 2) * 2 :=
      (ExplicitField.div_mul_cancel _ twoNonzero).symm

end Purelib.Polynomial.Recurrence.Spread.Chebyshev

end
