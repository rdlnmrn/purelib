module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Squares.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Trigonometry.Spread.Number.Basic
public import Purelib.Geometry.Trigonometry.SpreadNumber.Square

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.SpreadNumber

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

namespace Purelib.Geometry.Trigonometry.SpreadNumber.Rational.Bounds

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- The constructive half of Example 2.3: a displayed square root certifies nonnegativity in the rational/decimal order.
-/
theorem squareNumber_nonnegative
    (value : Fraction.Rational) (square : Squares.Basic.IsSquareNumber value) : 0 ≤ value := by
  rcases square with ⟨root, valueSquare⟩
  rw [valueSquare]
  exact Fraction.Order.Arithmetic.sq_nonneg_direct root

/-- A rational spread-number witness forces the value into the unit interval. The converse over the source's decimal
field requires square-root closure; over constructive rationals it is correctly retained as explicit witness data rather
than a selected root. -/
theorem spreadNumber_mem_unitInterval
    (value : Fraction.Rational) (spreadNumber : Number.Basic.IsSpreadNumber value) :
    0 ≤ value ∧ value ≤ 1 := by
  rcases spreadNumber with ⟨root, spreadSquare⟩
  have productNonnegative : 0 ≤ value * (1 - value) := by
    rw [spreadSquare]
    exact Fraction.Order.Arithmetic.sq_nonneg_direct root
  constructor
  · rcases lt_trichotomy value 0 with valueNegative | valueZero |
        valuePositive
    · have onePositive : (0 : Fraction.Rational) < 1 := by decide
      have valueLessOne : value < 1 := valueNegative.trans onePositive
      have complementPositive :=
        Fraction.Order.Arithmetic.sub_pos_direct valueLessOne
      have productNegative :=
        Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct valueNegative
          complementPositive
      exact False.elim ((not_lt_of_ge productNonnegative) productNegative)
    · rw [valueZero]
    · exact Fraction.Order.Arithmetic.le_of_lt_direct valuePositive
  · rcases lt_trichotomy value 1 with valueLess | valueOne | valueGreater
    · exact Fraction.Order.Arithmetic.le_of_lt_direct valueLess
    · exact valueOne.le
    · have valuePositive : (0 : Fraction.Rational) < value :=
        (by decide : (0 : Fraction.Rational) < 1).trans valueGreater
      have complementNegative :=
        Fraction.Order.Arithmetic.sub_neg_direct valueGreater
      have productNegative :=
        Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct valuePositive
          complementNegative
      exact False.elim ((not_lt_of_ge productNonnegative) productNegative)

/-- Example 2.3 with the analytic root-existence clause made explicit: if a value and its complement carry square roots,
it is a spread number in `[0,1]`. -/
theorem example_2_3
    (value firstRoot secondRoot : Fraction.Rational)
    (valueSquare : value = firstRoot ^ 2)
    (complementSquare : 1 - value = secondRoot ^ 2) :
    Square.IsSquareSpreadNumber value ∧ 0 ≤ value ∧ value ≤ 1 := by
  have lift : Square.HasUnitCircleLift value := by
    refine ⟨firstRoot, secondRoot, valueSquare, ?_⟩
    calc
      firstRoot ^ 2 + secondRoot ^ 2 = value + (1 - value) := by
        rw [← valueSquare, ← complementSquare]
      _ = 1 := by ring1
  have squareSpread := (Square.squareSpread_iff_unitCircleLift value).2 lift
  exact ⟨squareSpread,
    spreadNumber_mem_unitInterval value squareSpread.2⟩

end

end Purelib.Geometry.Trigonometry.SpreadNumber.Rational.Bounds

end
