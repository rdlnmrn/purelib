module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

section
public section

/-!
# Separating persistent CCL events across winding regions

Finite winding boxes and finite boundary-event cylinders now shrink in the
same squared-chordal metric.  This module supplies the missing quantitative
separation bridge: a positive coordinate gap between two rational boxes gives
a positive projective gap between all of their affine points.  Consequently a
sufficiently narrow nonzero boundary-event cylinder cannot meet both boxes.

Every bound is a displayed constructive rational.  No point at infinity,
completed root, compactness argument, or selected limiting parameter occurs.
-/

namespace Purelib.Data.Rat.SmallWidth

open Purelib.Data.Rat
/-- Choose the smaller of one and the target divided by twice one plus the coefficient.

For a nonnegative coefficient and positive target, the denominator is positive. The minimum keeps the width at most one
while the extra factor of two leaves a strict margin for the coefficient-weighted square bound. -/
@[expose] def shrinkingWidth (coefficient target : Fraction.Rational) : Fraction.Rational :=
  min 1 (target / (2 * (coefficient + 1)))

/-- A nonnegative coefficient and positive target give a positive chosen shrinking width. -/
theorem shrinkingWidth_pos
    {coefficient target : Fraction.Rational} (coefficientNonnegative : 0 ≤ coefficient)
    (targetPositive : 0 < target) :
    0 < shrinkingWidth coefficient target := by
  have denominatorPositive : 0 < 2 * (coefficient + 1) :=
    Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct coefficientNonnegative (by decide))
  exact Basic.lt_min (by decide)
    (Field.div_pos_direct targetPositive
      denominatorPositive)

/-- The nonnegative coefficient times the chosen positive width stays strictly below the target.

The original finite minimum is at most its displayed target ratio. The
coefficient is strictly smaller than the same denominator, so multiplying
by the retained positive width supplies the strict margin directly.
-/
theorem coefficient_mul_shrinkingWidth_lt
    {coefficient target : Fraction.Rational} (coefficientNonnegative : 0 ≤ coefficient)
    (targetPositive : 0 < target) : coefficient * shrinkingWidth coefficient target < target := by
  let width := shrinkingWidth coefficient target
  let denominator := 2 * (coefficient + 1)
  have widthPositive : 0 < width :=
    shrinkingWidth_pos coefficientNonnegative targetPositive
  have widthLeRatio : width ≤ target / denominator := Basic.min_le_right _ _
  have denominatorPositive : 0 < denominator :=
    Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct coefficientNonnegative (by decide))
  have coefficientStrict : coefficient < denominator := by
    have addStrict : coefficient < coefficient + 1 := by
      have shifted := Arithmetic.add_lt_add_left_direct
        (show (0 : Fraction.Rational) < 1 by decide) coefficient
      calc
        coefficient = coefficient + 0 := by ring1
        _ < coefficient + 1 := shifted
    have addNonnegative : 0 ≤ coefficient + 1 :=
      add_nonneg coefficientNonnegative (by decide)
    have scaled :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 : Fraction.Rational) ≤ 2 by decide) addNonnegative
    exact addStrict.trans_le (by
      simpa only [denominator, Fraction.Field.one_mul] using scaled)
  have denominatorWidthLe : denominator * width ≤ target := by
    have divided :=
      (Field.le_div_iff_pos denominatorPositive).mp
        widthLeRatio
    calc
      denominator * width = width * denominator :=
        Fraction.Field.mul_comm _ _
      _ ≤ target := divided
  exact (Arithmetic.mul_lt_mul_of_pos_right_direct coefficientStrict widthPositive).trans_le denominatorWidthLe

/-- The nonnegative coefficient times the chosen width square is strictly below the positive target. -/
theorem coefficient_mul_shrinkingWidth_sq_lt
    {coefficient target : Fraction.Rational} (coefficientNonnegative : 0 ≤ coefficient)
    (targetPositive : 0 < target) :
    coefficient * shrinkingWidth coefficient target ^ 2 < target := by
  let width := shrinkingWidth coefficient target
  have widthPositive : 0 < width := shrinkingWidth_pos coefficientNonnegative targetPositive
  have widthLeOne : width ≤ 1 := Basic.min_le_left _ _
  have widthSquareLe : width ^ 2 ≤ width := by
    rewrite [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct widthLeOne widthPositive.le).trans_eq
      (Fraction.Field.one_mul width)
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquareLe coefficientNonnegative).trans_lt
    (coefficient_mul_shrinkingWidth_lt coefficientNonnegative targetPositive)

end Purelib.Data.Rat.SmallWidth

end
