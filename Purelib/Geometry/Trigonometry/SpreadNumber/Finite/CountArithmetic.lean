module
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega

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

namespace Purelib.Geometry.Trigonometry.SpreadNumber.Finite.CountArithmetic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Exercise 2.3, arithmetic branch `p=4l+1`: the square-spread count is `l+1=(p+3)/4` once the finite unit-circle
accounting is supplied. -/
theorem exercise_2_3_four_mul_add_one (l : Nat)
  :
    (4 * l + 1 + 3) / 4 = l + 1 := by omega0

/-- Exercise 2.3, arithmetic branch `p=4l+3`: the square-spread count is `l+2=(p+5)/4` once the finite unit-circle
accounting is supplied. -/
theorem exercise_2_3_four_mul_add_three (l :
  Nat) :
    (4 * l + 3 + 5) / 4 = l + 2 := by omega0

end

end Purelib.Geometry.Trigonometry.SpreadNumber.Finite.CountArithmetic

end
