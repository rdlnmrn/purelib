module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite signed imaginary-coordinate decisions

A prescribed squared error gives a positive, negative, or near-boundary
whole-ball certificate. All margins and comparisons are rational. The last
case is a tolerance-relative result, not equality with the real axis.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Signed

open Purelib
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Data.Rat

/-- The coordinate error is bounded without extracting a square root. -/
theorem deviation {ball : Ball} {delta : Fraction.Rational} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) {value : Data.Gaussian.Basic.Canonical}
    (inside : ball.Contains value) :
    -(delta / 4) ≤ value.im - ball.center.im ∧ value.im - ball.center.im ≤ delta / 4 := by
  change (value.re - ball.center.re) ^ 2 + (value.im - ball.center.im) ^ 2 ≤
    ball.radiusSq at inside
  have squareLe : (value.im - ball.center.im) ^ 2 ≤ ball.radiusSq :=
    (le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct (value.re - ball.center.re))).trans inside
  have bounded : (value.im - ball.center.im) ^ 2 ≤ (delta / 4) ^ 2 := by
    rw [Purelib.Data.Rat.Bounds.Quarter.quarter_square]
    exact (squareLe.trans_lt fine).le
  exact ⟨Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive).le
    bounded,
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive).le bounded⟩

/-- A sufficiently fine ball whose centre exceeds the positive half-margin has every imaginary reading above the
quarter-margin. -/
theorem positive_lower {ball : Ball} {delta : Fraction.Rational} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (high : delta / 2 < ball.center.im)
    {value : Data.Gaussian.Basic.Canonical} (inside : ball.Contains value) : delta / 4 ≤ value.im := by
  have centerLower : (delta / 4) * 2 ≤ ball.center.im := by
    rw [← Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
    exact high.le
  calc
    delta / 4 = -(delta / 4) + (delta / 4) * 2 := by ring1
    _ ≤ (value.im - ball.center.im) + ball.center.im :=
      add_le_add (Approximation.Gaussian.Enclosure.Signed.deviation positive fine inside).1 centerLower
    _ = value.im := by ring1

/-- A sufficiently fine ball whose centre is below the negative half-margin has every imaginary reading below the
negative quarter-margin. -/
theorem negative_upper {ball : Ball} {delta : Fraction.Rational} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (low : ball.center.im < -(delta / 2))
    {value : Data.Gaussian.Basic.Canonical} (inside : ball.Contains value) : value.im ≤ -(delta / 4) := by
  have centerUpper : ball.center.im ≤ -((delta / 4) * 2) := by
    rw [← Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
    exact low.le
  calc
    value.im = (value.im - ball.center.im) + ball.center.im := by ring1
    _ ≤ delta / 4 + -((delta / 4) * 2) :=
      add_le_add (Approximation.Gaussian.Enclosure.Signed.deviation positive fine inside).2 centerUpper
    _ = -(delta / 4) := by ring1

/-- If neither signed centre test passes, every reading in a sufficiently fine ball has imaginary coordinate strictly
within the requested tolerance. -/
theorem near_bounds {ball : Ball} {delta : Fraction.Rational} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16)
    (notHigh : ¬ delta / 2 < ball.center.im) (notLow : ¬ ball.center.im < -(delta / 2))
    {value : Data.Gaussian.Basic.Canonical} (inside : ball.Contains value) : -delta < value.im ∧ value.im < delta := by
  have centerLower : -((delta / 4) * 2) ≤ ball.center.im := by
    rw [← Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
    exact le_of_not_gt notLow
  have centerUpper : ball.center.im ≤ (delta / 4) * 2 := by
    rw [← Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
    exact le_of_not_gt notHigh
  have tripleLess : (delta / 4) * 3 < delta := by
    calc
      (delta / 4) * 3 < (delta / 4) * 4 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)
          (by decide)
      _ = delta := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)
  constructor
  · apply (Fraction.Order.Arithmetic.neg_lt_neg_direct tripleLess).trans_le
    calc
      -((delta / 4) * 3) = -(delta / 4) + -((delta / 4) * 2) := by ring1
      _ ≤ (value.im - ball.center.im) + ball.center.im :=
        add_le_add (Approximation.Gaussian.Enclosure.Signed.deviation positive fine inside).1 centerLower
      _ = value.im := by ring1
  · apply lt_of_le_of_lt _ tripleLess
    calc
      value.im = (value.im - ball.center.im) + ball.center.im := by ring1
      _ ≤ delta / 4 + (delta / 4) * 2 :=
        add_le_add (Approximation.Gaussian.Enclosure.Signed.deviation positive fine inside).2 centerUpper
      _ = (delta / 4) * 3 := by ring1

/-- Compatibility with the existing squared-half-height positivity test. -/
theorem positive_test {ball : Ball} {delta : Fraction.Rational} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (high : delta / 2 < ball.center.im) :
    0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2 := by
  have halfPositive : 0 < delta / 2 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have quarterLe : delta / 4 ≤ ball.center.im / 2 := by
    apply (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : Fraction.Rational) < 2)).2
    rw [← Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
    exact high.le
  constructor
  · exact halfPositive.trans high
  · have squares := Fraction.Order.Arithmetic.pow_le_pow_direct (Purelib.Data.Rat.Bounds.Quarter.quarter_pos
      positive).le quarterLe 2
    rw [Purelib.Data.Rat.Bounds.Quarter.quarter_square] at squares
    exact fine.trans_le squares

/-- All three cases carry whole-ball evidence. `near` is not a zero verdict. -/
inductive Decision (ball : Ball) (delta : Fraction.Rational) : Type
  /-- The centre passes the positive half-margin test and every admitted reading meets the positive quarter-margin. -/ |
    positive (high : delta / 2 < ball.center.im)
      (lower : ∀ {value : Data.Gaussian.Basic.Canonical}, ball.Contains value → delta / 4 ≤ value.im)
  /-- The centre passes the negative half-margin test and every admitted reading meets the negative quarter-margin. -/ |
    negative (low : ball.center.im < -(delta / 2))
      (upper : ∀ {value : Data.Gaussian.Basic.Canonical}, ball.Contains value → value.im ≤ -(delta / 4))
  /-- Every admitted reading lies strictly between the two imaginary-coordinate tolerance bounds. -/ | near (bounds : ∀
    {value : Data.Gaussian.Basic.Canonical}, ball.Contains value →
      -delta < value.im ∧ value.im < delta)

/-- Classify a sufficiently fine ball by its signed imaginary-coordinate margin.

The executable comparisons return positive, negative or tolerance-relative near-boundary evidence for every admitted
reading. -/
@[expose] public def decide (ball : Ball) (delta : Fraction.Rational) (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) : Approximation.Gaussian.Enclosure.Signed.Decision ball delta :=
  if high : delta / 2 < ball.center.im then
    .positive high (Approximation.Gaussian.Enclosure.Signed.positive_lower positive fine high)
  else if low : ball.center.im < -(delta / 2) then
    .negative low (Approximation.Gaussian.Enclosure.Signed.negative_upper positive fine low)
  else .near (Approximation.Gaussian.Enclosure.Signed.near_bounds positive fine high low)

/-- Encode positive, negative and near-boundary decisions as one, two and zero respectively. -/
@[expose] public def Decision.tag {ball : Ball} {delta : Fraction.Rational} :
  Approximation.Gaussian.Enclosure.Signed.Decision ball delta → Nat
  | .positive _ _ => 1
  | .negative _ _ => 2
  | .near _ => 0

end Purelib.Approximation.Gaussian.Enclosure.Signed

end
