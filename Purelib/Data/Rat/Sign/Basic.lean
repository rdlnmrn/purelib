module

public import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Algebra.Group.Even
-- Integer-valued public laws retain the original arithmetic parents.
public import Purelib.Algebra.Ring.Int
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Integer signs of canonical rationals

The original rational comparisons select minus one, zero or one. Direct order
translations and finite sign cases certify multiplication and negation.
-/

namespace Purelib.Data.Rat.Sign.Basic

open Purelib.Data.Rat

/-- Compute the integer sign of a canonical rational as negative one, zero or one.

Compare the rational with zero using its concrete decidable order, then distinguish equality from positivity. The
returned integer has exactly one of the three values used by the sign-jump and parity identities. -/
@[expose] public def sign (x : Fraction.Rational) : Int :=
  if x < 0 then -1 else if x = 0 then 0 else 1

/-- The integer sign of rational zero is zero. -/
@[simp] public theorem sign_zero : Sign.Basic.sign 0 = 0 := rfl

/-- The integer sign of a positive rational is one.

The positive comparison excludes both the negative branch and equality to zero in the retained classifier. -/
public theorem sign_of_pos {x : Fraction.Rational} (hx : 0 < x) : Sign.Basic.sign x = 1 := by
  rewrite [sign, if_neg (not_lt.mpr hx.le), if_neg hx.ne']
  exact Eq.refl _

/-- The integer sign of a negative rational is negative one.

The supplied strict comparison selects the first branch of the original rational classifier. -/
public theorem sign_of_neg {x : Fraction.Rational} (hx : x < 0) : Sign.Basic.sign x = -1 := by
  rewrite [sign, if_pos hx]
  exact Eq.refl _

/-- The integer sign is zero exactly when the rational is zero. -/
public theorem sign_eq_zero_iff {x : Fraction.Rational} : Sign.Basic.sign x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [Sign.Basic.sign_of_neg hx] at h
      exact ((by decide : (-1 : Int) ≠ 0) h).elim
    · exact hx
    · rw [Sign.Basic.sign_of_pos hx] at h
      exact ((by decide : (1 : Int) ≠ 0) h).elim
  · rintro rfl
    exact Sign.Basic.sign_zero

/-- The integer sign is negative one exactly when the rational is negative. -/
public theorem sign_eq_neg_one_iff {x : Fraction.Rational} : Sign.Basic.sign x = -1 ↔ x < 0 := by
  constructor
  · intro equal
    rcases lt_trichotomy x 0 with negative | rfl | positive
    · exact negative
    · rw [Sign.Basic.sign_zero] at equal
      exact ((by decide : (0 : Int) ≠ -1) equal).elim
    · rw [Sign.Basic.sign_of_pos positive] at equal
      exact ((by decide : (1 : Int) ≠ -1) equal).elim
  · exact Sign.Basic.sign_of_neg

/-- The integer sign is one exactly when the rational is positive. -/
public theorem sign_eq_one_iff {x : Fraction.Rational} : Sign.Basic.sign x = 1 ↔ 0 < x := by
  constructor
  · intro equal
    rcases lt_trichotomy x 0 with negative | rfl | positive
    · rw [Sign.Basic.sign_of_neg negative] at equal
      exact ((by decide : (-1 : Int) ≠ 1) equal).elim
    · rw [Sign.Basic.sign_zero] at equal
      exact ((by decide : (0 : Int) ≠ 1) equal).elim
    · exact positive
  · exact Sign.Basic.sign_of_pos

/-- Negating a rational negates its integer sign.

Negation reverses the strict rational comparisons and fixes zero, so each of the three sign branches has the opposite
integer reading. -/
public theorem sign_neg (x : Fraction.Rational) : Sign.Basic.sign (-x) = -Sign.Basic.sign x := by
  rcases lt_trichotomy x 0 with negative | rfl | positive
  · have negPositive : 0 < -x := by
      have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct negative
      have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
      rewrite [zeroIdentity] at reversed
      exact reversed
    rewrite [sign_of_pos negPositive, sign_of_neg negative]
    decide
  · have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
    rewrite [zeroIdentity, sign_zero]
    decide
  · have negNegative : -x < 0 := by
      have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
      have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
      rewrite [zeroIdentity] at reversed
      exact reversed
    rewrite [sign_of_neg negNegative, sign_of_pos positive]
    decide

/-- The integer sign of a rational product is the product of its integer signs.

The nine pairs of negative, zero and positive inputs are resolved using direct rational product bounds and integer table
entries. -/
public theorem sign_mul (x y : Fraction.Rational) : Sign.Basic.sign (x * y) = Sign.Basic.sign x * Sign.Basic.sign y :=
  by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [Sign.Basic.sign_of_pos
        (Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct hx hy),
      Sign.Basic.sign_of_neg hx, Sign.Basic.sign_of_neg hy]
    decide
  · rewrite [Fraction.Field.mul_zero_direct, Sign.Basic.sign_zero]
    exact (MulZeroClass.mul_zero (Sign.Basic.sign x)).symm
  · rw [Sign.Basic.sign_of_neg
        (Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct hx hy),
      Sign.Basic.sign_of_neg hx, Sign.Basic.sign_of_pos hy]
    decide
  · rewrite [Fraction.Field.zero_mul_direct, Sign.Basic.sign_zero]
    exact (MulZeroClass.zero_mul (Sign.Basic.sign y)).symm
  · rewrite [Fraction.Field.zero_mul_direct, Sign.Basic.sign_zero]
    decide
  · rewrite [Fraction.Field.zero_mul_direct, Sign.Basic.sign_zero]
    exact (MulZeroClass.zero_mul (Sign.Basic.sign y)).symm
  · rw [Sign.Basic.sign_of_neg
        (Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct hx hy),
      Sign.Basic.sign_of_pos hx, Sign.Basic.sign_of_neg hy]
    decide
  · rewrite [Fraction.Field.mul_zero_direct, Sign.Basic.sign_zero]
    exact (MulZeroClass.mul_zero (Sign.Basic.sign x)).symm
  · rw [Sign.Basic.sign_of_pos (Fraction.Order.Arithmetic.mul_pos_direct hx hy),
      Sign.Basic.sign_of_pos hx, Sign.Basic.sign_of_pos hy]
    decide

/-- Rationals with positive product have the same integer sign.

A positive product excludes zero factors and opposite strict signs. The two remaining cases give identical integer
readings. -/
public theorem sign_eq_of_mul_pos {x y : Fraction.Rational} (hxy : 0 < x * y) :
    Sign.Basic.sign x = Sign.Basic.sign y := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
  · rewrite [Sign.Basic.sign_of_neg xNegative, Sign.Basic.sign_of_neg yNegative]
    exact Eq.refl _
  · rw [mul_zero] at hxy
    exact (lt_irrefl 0 hxy).elim
  · have productNegative :=
      Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        xNegative yPositive
    exact (lt_asymm hxy productNegative).elim
  · rw [zero_mul] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rw [zero_mul] at hxy
  · rw [zero_mul] at hxy
    exact (lt_irrefl 0 hxy).elim
  · have productNegative :=
      Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        xPositive yNegative
    exact (lt_asymm hxy productNegative).elim
  · rw [mul_zero] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rewrite [Sign.Basic.sign_of_pos xPositive, Sign.Basic.sign_of_pos yPositive]
    exact Eq.refl _

/-- The integer signs of two nonzero rationals differ by an even integer.

The two nonzero inputs each have reading minus one or one. Their four differences carry the explicit witnesses zero,
minus one or one. -/
public theorem sign_sub_even_of_ne_zero {x y : Fraction.Rational}
    (hx : x ≠ 0) (hy : y ≠ 0) : Even (Sign.Basic.sign x - Sign.Basic.sign y) := by
  rcases lt_or_gt_of_ne hx with xNegative | xPositive
  · rcases lt_or_gt_of_ne hy with yNegative | yPositive
    · refine ⟨0, ?_⟩
      rw [Sign.Basic.sign_of_neg xNegative, Sign.Basic.sign_of_neg yNegative]
      decide
    · refine ⟨-1, ?_⟩
      rw [Sign.Basic.sign_of_neg xNegative, Sign.Basic.sign_of_pos yPositive]
      decide
  · rcases lt_or_gt_of_ne hy with yNegative | yPositive
    · refine ⟨1, ?_⟩
      rw [Sign.Basic.sign_of_pos xPositive, Sign.Basic.sign_of_neg yNegative]
      decide
    · refine ⟨0, ?_⟩
      rw [Sign.Basic.sign_of_pos xPositive, Sign.Basic.sign_of_pos yPositive]
      decide

end Purelib.Data.Rat.Sign.Basic
