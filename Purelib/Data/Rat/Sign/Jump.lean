module

public import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Tactic.Ring

/-!
# Natural distances between rational signs

The retained classifier reads each rational as minus one, zero or one. Its natural
absolute difference records equality, a zero endpoint or opposite nonzero signs.
-/

namespace Purelib.Data.Rat.Sign.Jump

open Purelib.Data.Rat
open Purelib.Data

/-- Compute the natural absolute difference between the two integer rational signs.

The result is zero for equal signs, one when exactly one input is zero, and two for opposite nonzero signs. It is
therefore the doubled endpoint sign change used by the finite variation sum. -/
@[expose] public def signJump (x y : Fraction.Rational) : Nat := (Sign.Basic.sign x - Sign.Basic.sign y).natAbs

/-- The sign jump from a rational to itself is zero. -/
@[simp] public theorem signJump_self (x : Fraction.Rational) : Sign.Jump.signJump x x = 0 := by
  have difference : Sign.Basic.sign x - Sign.Basic.sign x = 0 := by ring1
  rewrite [signJump, difference]
  exact Eq.refl _

/-- Exchanging the two rationals preserves their sign jump. -/
public theorem signJump_comm (x y : Fraction.Rational) : Sign.Jump.signJump x y = Sign.Jump.signJump y x := by
  dsimp only [Sign.Jump.signJump]
  rw [show Sign.Basic.sign y - Sign.Basic.sign x = -(Sign.Basic.sign x - Sign.Basic.sign y) by ring1, Int.natAbs_neg]

/-- Negating both rationals preserves their sign jump. -/
public theorem signJump_neg_neg (x y : Fraction.Rational) :
    Sign.Jump.signJump (-x) (-y) = Sign.Jump.signJump x y := by
  simp only [Sign.Jump.signJump, Sign.Basic.sign_neg]
  rw [show -Sign.Basic.sign x - -Sign.Basic.sign y = -(Sign.Basic.sign x - Sign.Basic.sign y) by ring1,
    Int.natAbs_neg]

/-- The two jumps from a nonzero rational through zero to its negative sum to two. -/
public theorem signJump_zero_neg_of_ne {x : Fraction.Rational} (hx : x ≠ 0) :
    Sign.Jump.signJump x 0 + Sign.Jump.signJump 0 (-x) = 2 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [Sign.Jump.signJump, Sign.Jump.signJump, Sign.Basic.sign_of_neg hx, Sign.Basic.sign_zero, Sign.Basic.sign_neg,
      Sign.Basic.sign_of_neg hx]
    decide
  · rw [Sign.Jump.signJump, Sign.Jump.signJump, Sign.Basic.sign_of_pos hx, Sign.Basic.sign_zero, Sign.Basic.sign_neg,
      Sign.Basic.sign_of_pos hx]
    decide

/-- The sign jump between a nonzero rational and zero is one. -/
public theorem signJump_zero_of_ne {x : Fraction.Rational} (hx : x ≠ 0) :
    Sign.Jump.signJump 0 x = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [Sign.Jump.signJump, Sign.Basic.sign_zero, Sign.Basic.sign_of_neg hx]
    decide
  · rw [Sign.Jump.signJump, Sign.Basic.sign_zero, Sign.Basic.sign_of_pos hx]
    decide

/-- If two rationals are not both zero, the jumps from the first through the second to the negative first sum to two.

The two distances are checked in the nine endpoint sign cases. Excluding the pair of zero inputs leaves total distance
two through the negated first endpoint. -/
public theorem signJump_add_signJump_neg {x y : Fraction.Rational}
    (notBoth : x ≠ 0 ∨ y ≠ 0) :
    Sign.Jump.signJump x y + Sign.Jump.signJump y (-x) = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_neg hx]
      | rewrite [Sign.Basic.sign_of_neg hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_neg hx]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_neg hx]
      | rewrite [Sign.Basic.sign_of_pos hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_neg hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · exact notBoth.elim (fun impossible => (impossible rfl).elim)
      (fun impossible => (impossible rfl).elim)
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_pos hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_pos hx]
      | rewrite [Sign.Basic.sign_of_neg hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_pos hx]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_neg]
      | rewrite [Sign.Basic.sign_of_pos hx]
      | rewrite [Sign.Basic.sign_of_pos hy]
      | rewrite [Sign.Basic.sign_zero]
    decide

/-- Oppositely signed outer endpoints force the two intervening sign jumps to sum to two.

The outer endpoints have opposite nonzero signs. Every possible sign of the intervening endpoint gives the same total
natural distance. -/
public theorem signJump_add_signJump_of_outer_mul_neg {x y z : Fraction.Rational}
    (hxz : x * z < 0) : Sign.Jump.signJump x y + Sign.Jump.signJump y z = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy z 0 with hz | rfl | hz
  · exact (lt_asymm hxz (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct hx hz)).elim
  · rewrite [Fraction.Field.mul_zero_direct] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_pos hz]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_pos hz]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_pos hz]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
  · rewrite [Fraction.Field.zero_mul_direct] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rewrite [Fraction.Field.mul_zero_direct] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rewrite [Fraction.Field.zero_mul_direct] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_neg hz]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_neg hz]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_neg hz]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
  · rewrite [Fraction.Field.mul_zero_direct] at hxz
    exact (lt_irrefl 0 hxz).elim
  · exact (lt_asymm hxz (Fraction.Order.Arithmetic.mul_pos_direct hx hz)).elim

/-- A negative product gives sign jump two.

The negative product excludes zero factors and equal nonzero signs. The remaining two pairs have integer sign distance
two. -/
public theorem signJump_eq_two_of_mul_neg {x y : Fraction.Rational} (hxy : x * y < 0) :
    Sign.Jump.signJump x y = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · exact (lt_asymm hxy (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct hx hy)).elim
  · rewrite [Fraction.Field.mul_zero_direct] at hxy
    exact (lt_irrefl 0 hxy).elim
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_of_neg hx]
      | rewrite [Sign.Basic.sign_of_pos hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · rewrite [Fraction.Field.zero_mul_direct] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rewrite [Fraction.Field.mul_zero_direct] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rewrite [Fraction.Field.zero_mul_direct] at hxy
    exact (lt_irrefl 0 hxy).elim
  · repeat first
      | rewrite [signJump]
      | rewrite [Sign.Basic.sign_mul]
      | rewrite [Sign.Basic.sign_of_pos hx]
      | rewrite [Sign.Basic.sign_of_neg hy]
      | rewrite [Sign.Basic.sign_zero]
    decide
  · rewrite [Fraction.Field.mul_zero_direct] at hxy
    exact (lt_irrefl 0 hxy).elim
  · exact (lt_asymm hxy (Fraction.Order.Arithmetic.mul_pos_direct hx hy)).elim

/-- A positive product gives sign jump zero.

The positive product identifies the two integer sign readings, whose retained difference is zero. -/
public theorem signJump_eq_zero_of_mul_pos {x y : Fraction.Rational} (hxy : 0 < x * y) :
    Sign.Jump.signJump x y = 0 := by
  rewrite [signJump, Sign.Basic.sign_eq_of_mul_pos hxy]
  have difference : Sign.Basic.sign y - Sign.Basic.sign y = 0 := by ring1
  rewrite [difference]
  exact Eq.refl _

/-- Oppositely signed multipliers make the original and multiplied sign jumps sum to two when the inputs are not both
zero.

The multipliers have opposite nonzero signs. Their two sign configurations and the nine endpoint configurations retain
total distance two, with the all-zero endpoint pair excluded. -/
public theorem signJump_add_signJump_mul_of_mul_neg {a b x y : Fraction.Rational}
    (hab : a * b < 0) (notBoth : x ≠ 0 ∨ y ≠ 0) :
    Sign.Jump.signJump x y + Sign.Jump.signJump (a * x) (b * y) = 2 := by
  have oppositeSigns :
      (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
      · have productPositive :=
          Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
            aNegative bNegative
        exact (lt_asymm hab productPositive).elim
      · rewrite [Fraction.Field.mul_zero_direct] at hab
        exact (lt_irrefl 0 hab).elim
      · exact Or.inl ⟨aNegative, bPositive⟩
    · rewrite [Fraction.Field.zero_mul_direct] at hab
      exact (lt_irrefl 0 hab).elim
    · rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
      · exact Or.inr ⟨aPositive, bNegative⟩
      · rewrite [Fraction.Field.mul_zero_direct] at hab
        exact (lt_irrefl 0 hab).elim
      · have productPositive :=
          Fraction.Order.Arithmetic.mul_pos_direct aPositive bPositive
        exact (lt_asymm hab productPositive).elim
  rcases oppositeSigns with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases lt_trichotomy x 0 with hx | rfl | hx <;>
      rcases lt_trichotomy y 0 with hy | rfl | hy
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · exact notBoth.elim (fun impossible => (impossible rfl).elim)
        (fun impossible => (impossible rfl).elim)
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_neg ha]
        | rewrite [Sign.Basic.sign_of_pos hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
  · rcases lt_trichotomy x 0 with hx | rfl | hx <;>
      rcases lt_trichotomy y 0 with hy | rfl | hy
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_neg hx]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · exact notBoth.elim (fun impossible => (impossible rfl).elim)
        (fun impossible => (impossible rfl).elim)
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_neg hy]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_zero]
      decide
    · repeat first
        | rewrite [signJump]
        | rewrite [Sign.Basic.sign_mul]
        | rewrite [Sign.Basic.sign_of_pos ha]
        | rewrite [Sign.Basic.sign_of_neg hb]
        | rewrite [Sign.Basic.sign_of_pos hx]
        | rewrite [Sign.Basic.sign_of_pos hy]
        | rewrite [Sign.Basic.sign_zero]
      decide

/-- Replacing each rational by another with the same integer sign preserves their sign jump.

The supplied equations identify the two retained integer readings separately. Subtraction and natural absolute value
preserve those exact scalar readings. -/
public theorem signJump_congr {x x' y y' : Fraction.Rational}
    (hx : Sign.Basic.sign x = Sign.Basic.sign x') (hy : Sign.Basic.sign y = Sign.Basic.sign y') :
    Sign.Jump.signJump x y = Sign.Jump.signJump x' y' := by
  rewrite [signJump, signJump, hx, hy]
  exact Eq.refl _

/-- The sign jump and the signed difference of the endpoint signs differ by an even integer.

A nonnegative integer difference has zero residual after absolute value; a negative one has twice its additive inverse
as residual. These are explicit integer witnesses for evenness. -/
public theorem signJump_sub_signDifference_even (x y : Fraction.Rational) :
    Even (((Sign.Jump.signJump x y : Nat) : Int) - (Sign.Basic.sign x - Sign.Basic.sign y)) := by
  let difference := Sign.Basic.sign x - Sign.Basic.sign y
  by_cases negative : difference < 0
  · refine ⟨-difference, ?_⟩
    change (difference.natAbs : Int) - difference = -difference + -difference
    rewrite [Int.Order.natAbs_of_not_pos (fun positive =>
      (Int.Order.lt_iff_le_and_not_ge.mp negative).2 (Int.Order.le_of_lt positive))]
    ring1
  · refine ⟨0, ?_⟩
    change (difference.natAbs : Int) - difference = 0 + 0
    rewrite [Int.Order.natAbs_of_nonneg (Int.Order.le_of_not_lt negative)]
    ring1

end Purelib.Data.Rat.Sign.Jump
