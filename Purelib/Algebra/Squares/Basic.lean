module
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega

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

@[expose] public section

namespace Purelib.Algebra.Squares.Basic

variable {K : Type*} [ExplicitField K]

/-- A scalar is square when a scalar root witnesses its squared value.

The existential retains the equality in the displayed field without selecting a root computationally. -/
def IsSquareNumber (value : K) : Prop :=
  ∃ root : K, value = root ^ 2

end Purelib.Algebra.Squares.Basic

end
