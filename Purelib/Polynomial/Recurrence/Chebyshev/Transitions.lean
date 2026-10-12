module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Chebyshev.SecondPrevious.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: constructive rational spread bounds

Exercise 8.3 is retained over the source's rational field.  The proof uses a
finite Chebyshev square invariant and the project-owned constructive order on
explicit fractions; it introduces neither completed real numbers nor limits.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.Transitions

variable {K : Type*} [ExplicitField K]

/-- The two first-order transitions underlying the Chebyshev square
invariant.  They are proved together by finite induction. -/
theorem chebyshevFirst_secondPrevious_transitions
    (index : Nat) (value : K) :
    Recurrence.Chebyshev.First.Basic.chebyshevFirst (index + 1) value =
        value * Recurrence.Chebyshev.First.Basic.chebyshevFirst index value -
          (1 - value ^ 2) * Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ∧
      Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious (index + 1) value =
        Recurrence.Chebyshev.First.Basic.chebyshevFirst index value +
          value * Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value := by
  induction index with
  | zero =>
      constructor <;>
        unfold Recurrence.Chebyshev.First.Basic.chebyshevFirst
          Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨firstTransition, secondTransition⟩
      constructor
      · rw [show Nat.succ index + 1 = index + 2 by omega0]
        rw [Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ, firstTransition, secondTransition]
        ring1
      · rw [show Nat.succ index + 1 = index + 2 by omega0]
        rw [Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious_succ_succ, firstTransition,
          secondTransition]
        ring1

/-- The finite polynomial identity
`T_n(x)^2 + (1-x^2) U_(n-1)(x)^2 = 1`. -/
theorem chebyshevFirst_square_invariant (index : Nat) (value
  : K) :
    Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 +
        (1 - value ^ 2) * Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2 = 1 := by
  induction index with
  | zero =>
      unfold Recurrence.Chebyshev.First.Basic.chebyshevFirst
        Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious
      ring1
  | succ index inductionHypothesis =>
      rcases chebyshevFirst_secondPrevious_transitions index value with
        ⟨firstTransition, secondTransition⟩
      rw [firstTransition, secondTransition]
      calc
        (value * Recurrence.Chebyshev.First.Basic.chebyshevFirst index value -
              (1 - value ^ 2) *
                Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value) ^ 2 +
            (1 - value ^ 2) *
              (Recurrence.Chebyshev.First.Basic.chebyshevFirst index value +
                value * Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value) ^ 2 =
          Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 +
            (1 - value ^ 2) *
              Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2 := by ring1
        _ = 1 := inductionHypothesis

end Purelib.Polynomial.Recurrence.Chebyshev.Transitions

end
