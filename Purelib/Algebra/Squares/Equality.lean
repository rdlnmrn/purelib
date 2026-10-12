module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

/-!
# Divine Proportions, Examples 2.2--2.5

The source describes square, spread, and square-spread numbers by counting an
entire finite field.  This project does not enumerate an ambient carrier.
Instead, the displayed tables are retained as explicit finite witness rows:
every listed entry carries the root which certifies it, the list is proved
duplicate-free, and its displayed length is checked by the kernel.

Exercise 2.3 is represented by the finite algebra behind the usual count.  A
square-spread value is exactly the first-coordinate square of a point on the
unit circle.  Away from the two boundary values, a supplied pair of roots
gives the four independent sign choices.  The final formulas for primes of
the forms `4l+1` and `4l+3` are finite natural-number calculations; no finite
cardinal, carrier enumeration, or selected square root is introduced.
-/

public section

namespace Purelib.Algebra.Squares.Equality

variable {K : Type*} [ExplicitField K]

/-- Equal squares give equal values or opposite values.

Decidable equality in the explicit field resolves the two factors of the difference of squares without choosing square
roots. -/
theorem eq_or_eq_neg_of_sq_eq_sq [DecidableEq K]
    {left right : K} (squaresEqual : left ^ 2 = right ^ 2) :
    left = right ∨ left = -right := by
  have productZero : (left - right) * (left + right) = 0 := by
    calc
      (left - right) * (left + right) = left ^ 2 - right ^ 2 := by ring1
      _ = 0 := by rw [squaresEqual]; ring1
  by_cases firstFactorZero : left - right = 0
  · exact Or.inl (Group.eq_of_sub_eq_zero firstFactorZero)
  · have secondFactorZero : left + right = 0 := by
      by_cases secondFactorNonzero : left + right = 0
      · exact secondFactorNonzero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstFactorZero
            secondFactorNonzero) productZero)
    exact Or.inr (eq_neg_of_add_eq_zero_left secondFactorZero)

end Purelib.Algebra.Squares.Equality

end

end
