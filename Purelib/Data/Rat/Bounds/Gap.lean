module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! Direct comparisons of rational leading values minus retained error budgets. -/

namespace Purelib.Data.Rat.Bounds.Gap

open Purelib.Data.Rat
open Fraction.Order

/-- A positive radius whose quadruple fits a gap is strictly smaller than that same gap. -/
public theorem radius_lt_gap {radius gap : Fraction.Rational} (positive : 0 < radius)
    (paid : 4 * radius ≤ gap) : radius < gap := by
  calc
    radius = radius + 0 := by ring1
    _ < radius + 3 * radius := Arithmetic.add_lt_add_left_direct
      (Arithmetic.mul_pos_direct (by decide) positive) radius
    _ = 4 * radius := by ring1
    _ ≤ gap := paid

/-- A gap paying four radii retains at least three radii after the same one-radius displacement. -/
public theorem three_radius_le_remaining_gap {radius gap : Fraction.Rational} (paid : 4 * radius ≤ gap) :
    3 * radius ≤ gap - radius := by
  calc
    3 * radius = 4 * radius - radius := by ring1
    _ ≤ gap - radius := Arithmetic.sub_le_sub_right_direct paid radius

/-- A gap paying four positive radii retains squared clearance above the squared two-radius displacement.

The remaining gap is at least three radii. Squaring its nonnegative lower
bound gives nine radius squares, strictly above four radius squares. -/
public theorem four_radius_sq_lt_remaining_gap_sq {radius gap : Fraction.Rational} (positive : 0 < radius)
    (paid : 4 * radius ≤ gap) : 4 * radius ^ 2 < (gap - radius) ^ 2 := by
  calc
    4 * radius ^ 2 < 9 * radius ^ 2 := Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide) (Arithmetic.exact_rational_sq_pos positive.ne')
    _ = (3 * radius) ^ 2 := by ring1
    _ ≤ (gap - radius) ^ 2 := Arithmetic.pow_le_pow_direct
      (Arithmetic.mul_nonneg_direct (by decide) positive.le) (three_radius_le_remaining_gap paid) 2

end Purelib.Data.Rat.Bounds.Gap
