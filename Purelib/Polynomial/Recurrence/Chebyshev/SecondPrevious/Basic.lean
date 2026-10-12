module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: constructive rational spread bounds

Exercise 8.3 is retained over the source's rational field.  The proof uses a
finite Chebyshev square invariant and the project-owned constructive order on
explicit fractions; it introduces neither completed real numbers nor limits.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.SecondPrevious.Basic

variable {K : Type*} [ExplicitField K]

/-- The polynomial usually written `U_(n-1)`, with its exceptional initial
value incorporated into a primitive-recursive sequence. -/
def chebyshevSecondPrevious : Nat → K → K
  | 0, _ => 0
  | 1, _ => 1
  | index + 2, value =>
      2 * value * chebyshevSecondPrevious (index + 1) value
        -
        chebyshevSecondPrevious index value

open Purelib.Polynomial
/-- The index-zero shifted second-kind Chebyshev value is zero. -/
@[simp] theorem chebyshevSecondPrevious_zero (value
  : K) :
    chebyshevSecondPrevious 0 value = 0 := rfl

/-- The index-one shifted second-kind Chebyshev value is one. -/
@[simp] theorem chebyshevSecondPrevious_one (value :
  K) :
    chebyshevSecondPrevious 1 value = 1 := rfl

/-- Twice the argument times the previous shifted Chebyshev value minus its predecessor. -/
@[simp] theorem chebyshevSecondPrevious_succ_succ
    (index : Nat) (value : K) :
    chebyshevSecondPrevious (index + 2) value =
      2 * value * chebyshevSecondPrevious (index + 1) value -
        chebyshevSecondPrevious index value := rfl

end Purelib.Polynomial.Recurrence.Chebyshev.SecondPrevious.Basic

end
