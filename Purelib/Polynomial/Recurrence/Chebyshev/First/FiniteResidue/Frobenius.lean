module
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev
import Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Frobenius

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Frobenius

variable {K : Type*} [ExplicitField K]

section

/-- Exercise 8.5 and the centered spread/Chebyshev identity say pointwise
that the `p`th Chebyshev value fixes every centered natural residue label. -/
theorem
  chebyshevFirst_prime_centered_residue
    (prime residue : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Chebyshev.First.Basic.chebyshevFirst prime (1 - 2 * (residue : K)) =
      1 - 2 * (residue : K) := by
  have fixed := Recurrence.Spread.FiniteResidue.Frobenius.prime_residue_fixed
    (K := K) prime residue primeIsPrime primeCastZero twoNonzero
  have centered := Recurrence.Spread.Chebyshev.exercise_8_4_cleared prime (residue : K)
  rw [fixed] at centered
  calc
    Recurrence.Chebyshev.First.Basic.chebyshevFirst prime (1 - 2 * (residue : K)) =
        1 - (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst prime (1 - 2 * (residue : K))) := by
          ring1
    _ = 1 - 2 * (residue : K) := by rw [← centered]
end

end Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Frobenius

end
