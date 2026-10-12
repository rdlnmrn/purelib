module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.Deriving.Repr
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Data.SignedDigit.Binary.Basic

/-- The three redundant signed binary digits minus one, zero and one. -/
inductive Digit where
  /-- The signed digit with rational value minus one. -/ | negative
  /-- The signed digit with rational value zero. -/ | zero
  /-- The signed digit with rational value one. -/ | positive
deriving DecidableEq
derive_exposed_repr Digit

end Purelib.Data.SignedDigit.Binary.Basic

namespace Purelib.Data.SignedDigit.Binary.Basic

namespace Digit

open Purelib.Data in
open Purelib.Data.Rat in
/-- Read the exact rational value of a retained signed binary digit. -/
@[expose] def value : Digit → Fraction.Rational
  | .negative => -1
  | .zero => 0
  | .positive => 1

end Digit

open Purelib.Data in
open Purelib.Data.Rat in
/-- Compute the finite signed binary value with successive weights one half, one quarter and so on. -/
@[expose] def prefixValue : List Digit → Fraction.Rational
  | [] => 0
  | digit :: remaining =>
      (digit.value + prefixValue remaining) * (1 / 2)

open Purelib.Data.Rat in
/-- Require a rational value to lie in the closed interval from minus one to one. -/
@[expose] def Bounded (value : Fraction.Rational) : Prop :=
  -1 ≤ value ∧ value ≤ 1

open Purelib.Data
open Purelib.Data.Rat
/-- Choose the negative digit for a strictly negative value and the positive digit otherwise.

The zero digit remains part of the redundant syntax but is not selected by this deterministic rule. The zero boundary
selects the positive digit. -/
@[expose] def select (value : Fraction.Rational) : Digit :=
  if value < 0 then .negative else .positive

/-- Subtract the selected digit value from twice the supplied rational. -/
@[expose] def residual (digit : Digit) (value : Fraction.Rational) : Fraction.Rational :=
  2 * value - digit.value

/-- The deterministic signed-digit residual preserves the closed interval from minus one to one. -/
theorem select_residual_bounded {value : Fraction.Rational}
    (bounded : Bounded value) : Bounded
      (residual (select value) value) := by
  unfold select
  split
  · rename_i negative
    change -1 ≤ 2 * value - (-1 : Fraction.Rational) ∧
      2 * value - (-1 : Fraction.Rational) ≤ 1
    have doubledLower : (-2 : Fraction.Rational) ≤ 2 * value := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bounded.1 (by decide : (0 : Fraction.Rational) ≤ 2)
      rw [show (2 : Fraction.Rational) * -1 = -2 by decide] at scaled
      exact scaled
    have doubledUpper : 2 * value ≤ 0 := by
      have nonpositive := le_of_lt negative
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          nonpositive (by decide : (0 : Fraction.Rational) ≤ 2)
      rw [show (2 : Fraction.Rational) * 0 = 0 by decide] at scaled
      exact scaled
    constructor
    · calc
        (-1 : Fraction.Rational) = -2 - (-1) := by decide
        _ ≤ 2 * value - (-1) := Fraction.Order.Arithmetic.sub_le_sub_right_direct doubledLower _
    · calc
        2 * value - (-1 : Fraction.Rational) ≤ 0 - (-1) :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct doubledUpper _
        _ = 1 := by decide
  · rename_i nonnegative
    change -1 ≤ 2 * value - (1 : Fraction.Rational) ∧
      2 * value - (1 : Fraction.Rational) ≤ 1
    have zeroLe : (0 : Fraction.Rational) ≤ value := le_of_not_gt nonnegative
    have doubledLower : (0 : Fraction.Rational) ≤ 2 * value := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          zeroLe (by decide : (0 : Fraction.Rational) ≤ 2)
      rw [show (2 : Fraction.Rational) * 0 = 0 by decide] at scaled
      exact scaled
    have doubledUpper : 2 * value ≤ 2 := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bounded.2 (by decide : (0 : Fraction.Rational) ≤ 2)
      rw [show (2 : Fraction.Rational) * 1 = 2 by decide] at scaled
      exact scaled
    constructor
    · calc
        (-1 : Fraction.Rational) = 0 - 1 := by decide
        _ ≤ 2 * value - 1 := Fraction.Order.Arithmetic.sub_le_sub_right_direct doubledLower _
    · calc
        2 * value - (1 : Fraction.Rational) ≤ 2 - 1 :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct doubledUpper _
        _ = 1 := by decide
end Purelib.Data.SignedDigit.Binary.Basic

end
