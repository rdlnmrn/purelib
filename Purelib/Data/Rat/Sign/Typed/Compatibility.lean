module

import Purelib.Data.Rat.Sign.Basic
public import Purelib.Data.Rat.Sign.Jump
public import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Sign.Stability
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Order.Basic

/-!
# Rational readbacks of formal signs

The original finite classifier agrees with the integer rational sign, preserving
products, negation and endpoint stability through explicit scalar certificates.
-/

open Purelib.Data.Rat
open _root_.Purelib.Data renaming Sign -> FiniteSign

-- These existing methods retain the nominal Sign owner; its module path also names Sign.
namespace Purelib.Data.Sign

/-- Reading the finite sign as an integer agrees with the rational integer-sign function.

Each strict rational comparison selects the corresponding formal constructor, whose integer reading is the retained
rational sign. -/
@[simp] public theorem value_ofCoordinate (x : Fraction.Rational) :
    FiniteSign.value (FiniteSign.ofCoordinate x) = Sign.Basic.sign x := by
  by_cases negative : x < 0
  · rw [FiniteSign.ofCoordinate, if_pos negative, FiniteSign.value, Sign.Basic.sign_of_neg negative]
  · by_cases zero : x = 0
    · subst x
      rfl
    · have positive : 0 < x := lt_of_le_of_ne (not_lt.mp negative) (Ne.symm zero)
      rw [FiniteSign.ofCoordinate, if_neg negative, if_neg zero, FiniteSign.value,
        Sign.Basic.sign_of_pos positive]

/-- The finite sign of rational zero is the zero constructor. -/
@[simp] public theorem ofCoordinate_zero : FiniteSign.ofCoordinate 0 = FiniteSign.zero := rfl

/-- A rational has finite zero sign exactly when it is zero.

The zero constructor has zero integer reading, and the original rational classifier has zero reading exactly at zero. -/
public theorem ofCoordinate_eq_zero_iff {x : Fraction.Rational} :
    FiniteSign.ofCoordinate x = FiniteSign.zero ↔ x = 0 := by
  constructor
  · intro equal
    have values := congrArg FiniteSign.value equal
    rw [FiniteSign.value_ofCoordinate, FiniteSign.value] at values
    exact Sign.Basic.sign_eq_zero_iff.mp values
  · rintro rfl
    rfl

/-- A rational has nonzero finite sign exactly when it is nonzero. -/
public theorem ofCoordinate_ne_zero_iff {x : Fraction.Rational} :
    FiniteSign.ofCoordinate x ≠ FiniteSign.zero ↔ x ≠ 0 :=
  not_congr FiniteSign.ofCoordinate_eq_zero_iff

/-- A negative rational has the finite negative sign. -/
public theorem ofCoordinate_of_neg {x : Fraction.Rational} (negative : x < 0) :
    FiniteSign.ofCoordinate x = .negative := by
  rw [FiniteSign.ofCoordinate, if_pos negative]

/-- A positive rational has the finite positive sign. -/
public theorem ofCoordinate_of_pos {x : Fraction.Rational} (positive : 0 < x) :
    FiniteSign.ofCoordinate x = .positive := by
  rw [FiniteSign.ofCoordinate, if_neg (not_lt.mpr positive.le),
    if_neg positive.ne']

/-- Finite sign classification preserves rational multiplication.

Integer readings identify formal signs. Their multiplication certificates therefore identify the formal product with the
classified rational product. -/
@[simp] public theorem ofCoordinate_mul (x y : Fraction.Rational) :
    FiniteSign.ofCoordinate (x * y) = FiniteSign.mul (FiniteSign.ofCoordinate x) (FiniteSign.ofCoordinate y) := by
  apply FiniteSign.value_injective
  rw [FiniteSign.value_ofCoordinate, FiniteSign.value_mul, FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate,
    Sign.Basic.sign_mul]

/-- Finite sign classification preserves rational negation.

Integer reading injectivity and the rational negation certificate identify the corresponding negated formal signs. -/
@[simp] public theorem ofCoordinate_neg (x : Fraction.Rational) :
    FiniteSign.ofCoordinate (-x) = FiniteSign.neg (FiniteSign.ofCoordinate x) := by
  apply FiniteSign.value_injective
  rw [FiniteSign.value_ofCoordinate, FiniteSign.value_neg, FiniteSign.value_ofCoordinate, Sign.Basic.sign_neg]

/-- The finite sign jump equals the natural absolute difference of the rational integer signs.

Both retained integer readings coincide, so their original subtraction and natural absolute value give the same jump. -/
@[simp] public theorem jump_ofCoordinate (x y : Fraction.Rational) :
    FiniteSign.jump (FiniteSign.ofCoordinate x) (FiniteSign.ofCoordinate y) = Sign.Jump.signJump x y := by
  rw [FiniteSign.jump, Sign.Jump.signJump, FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]

end Purelib.Data.Sign

namespace Purelib.Data.Rat.Sign.Typed.Compatibility

/-- A zero starting coordinate or positive endpoint product certifies stability of the two finite signs.

A zero endpoint satisfies the zero branch of stability; a positive product identifies the two nonzero endpoint signs. -/
public theorem sign_stable_of_eq_zero_or_mul_pos {x₀ x₁ : Fraction.Rational}
    (stable : x₀ = 0 ∨ 0 < x₀ * x₁) :
    FiniteSign.Stable
      (FiniteSign.ofCoordinate x₀) (FiniteSign.ofCoordinate x₁) := by
  rcases stable with rfl | positive
  · exact Or.inl rfl
  · apply Or.inr
    apply FiniteSign.value_injective
    rw [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
    exact Sign.Basic.sign_eq_of_mul_pos positive

end Purelib.Data.Rat.Sign.Typed.Compatibility

section

namespace Purelib.Data.Rat.Sign.Typed.Compatibility
/-- Multiplying on the left by a positive rational leaves the finite sign unchanged.

The positive scale has formal positive sign, which leaves every entry of the original multiplication table unchanged. -/
public theorem ofCoordinate_mul_pos_left
    (scale x : Fraction.Rational) (positive : 0 < scale) :
    FiniteSign.ofCoordinate (scale * x) = FiniteSign.ofCoordinate x := by
  rw [FiniteSign.ofCoordinate_mul,
    FiniteSign.ofCoordinate_of_pos positive]
  cases FiniteSign.ofCoordinate x <;> rfl
end Purelib.Data.Rat.Sign.Typed.Compatibility

end

namespace Purelib.Data.Rat.Sign.Typed.Compatibility.Turn

/-- A positive rational product forces equality of the factors' finite signs.

A positive rational product gives equal integer readings, and those readings identify the two formal signs. -/
public theorem ofCoordinate_eq_of_mul_pos {x y : Fraction.Rational}
    (positive : 0 < x * y) :
    FiniteSign.ofCoordinate x = FiniteSign.ofCoordinate y := by
  apply FiniteSign.value_injective
  rw [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
  exact Sign.Basic.sign_eq_of_mul_pos positive

/-- A negative rational product forces different finite signs for its factors.

Equal formal signs would give equal integer readings. The finite rational sign cases contradict a negative product for
each such pair. -/
public theorem ofCoordinate_ne_of_mul_neg {x y : Fraction.Rational}
    (negative : x * y < 0) :
    FiniteSign.ofCoordinate x ≠ FiniteSign.ofCoordinate y := by
  intro equal
  have values := congrArg FiniteSign.value equal
  rewrite [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate] at values
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
  · exact (lt_asymm (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
      xNegative yNegative) negative).elim
  · rewrite [Fraction.Field.mul_zero_direct] at negative
    exact (lt_irrefl 0 negative).elim
  · rewrite [Sign.Basic.sign_of_neg xNegative, Sign.Basic.sign_of_pos yPositive] at values
    exact ((by decide : (-1 : Int) ≠ 1) values).elim
  · rewrite [Fraction.Field.zero_mul_direct] at negative
    exact (lt_irrefl 0 negative).elim
  · rewrite [Fraction.Field.zero_mul_direct] at negative
    exact (lt_irrefl 0 negative).elim
  · rewrite [Fraction.Field.zero_mul_direct] at negative
    exact (lt_irrefl 0 negative).elim
  · rewrite [Sign.Basic.sign_of_pos xPositive, Sign.Basic.sign_of_neg yNegative] at values
    exact ((by decide : (1 : Int) ≠ -1) values).elim
  · rewrite [Fraction.Field.mul_zero_direct] at negative
    exact (lt_irrefl 0 negative).elim
  · exact (lt_asymm (Fraction.Order.Arithmetic.mul_pos_direct
      xPositive yPositive) negative).elim

end Purelib.Data.Rat.Sign.Typed.Compatibility.Turn
