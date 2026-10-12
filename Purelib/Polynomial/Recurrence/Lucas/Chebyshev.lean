module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Lucas.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `Purelib.NumberTheory.Totient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace Purelib.Polynomial.Recurrence.Lucas.Chebyshev.ExerciseEightThirteen

variable {K : Type*} [ExplicitField K]

section

/-- Lucas evaluation at twice a scalar equals twice the first Chebyshev polynomial.

The identity holds at every natural index in the supplied explicit field, with no characteristic restriction. -/
theorem lucas_at_double : ∀ index : Nat, ∀
  value : K,
    Recurrence.Lucas.Basic.lucas index (2 * value) = 2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst index value
  | 0, value => by
      rw [Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero, Recurrence.Chebyshev.First.Basic.chebyshevFirst_zero]
      ring1
  | 1, value => by
      rw [Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_one, Recurrence.Chebyshev.First.Basic.chebyshevFirst_one]
  | index + 2, value => by
      rw [Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_succ_succ,
        Recurrence.Chebyshev.First.Basic.chebyshevFirst_succ_succ,
        lucas_at_double (index + 1) value,
        lucas_at_double index value]
      ring1
end

end Purelib.Polynomial.Recurrence.Lucas.Chebyshev.ExerciseEightThirteen

end
