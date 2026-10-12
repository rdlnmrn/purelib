module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

/-! # Positive rational radius requests with squared budgets -/

public section

namespace Purelib.Approximation.Rational.Budget.Square

/-- Positive rational box-radius request with square below the target area. -/
@[expose] def radius (target : Fraction.Rational) : Fraction.Rational :=
  min 1 (target / 4)

/-- A positive target gives a positive area radius. -/
theorem radius_pos {target : Fraction.Rational} (positive : 0 < target) :
    0 < radius target := by
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct positive (by decide))

/-- The selected area radius has square strictly below a positive target. -/
theorem radius_sq_lt {target : Fraction.Rational}
    (positive : 0 < target) : radius target ^ 2 < target :=
      by
  let radius := radius target
  have radiusPositive : 0 < radius := radius_pos positive
  have radiusLeOne : radius ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have radiusLeQuarter : radius ≤ target / 4 := Fraction.Order.Basic.min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq
        (Fraction.Field.one_mul radius)
  have radiusLtFourRadius : radius < 4 * radius := by
    calc
      radius = 1 * radius :=
        (Fraction.Field.one_mul radius).symm
      _ < 4 * radius :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (by decide) radiusPositive
  have fourRadiusLe : 4 * radius ≤ target := by
    have divided :=
      (Fraction.Order.Field.le_div_iff_pos
        (by decide : (0 : Fraction.Rational) < 4)).mp radiusLeQuarter
    calc
      4 * radius = radius * 4 :=
        Fraction.Field.mul_comm _ _
      _ ≤ target := divided
  exact radiusSquareLe.trans_lt (radiusLtFourRadius.trans_le fourRadiusLe)
end Purelib.Approximation.Rational.Budget.Square

end
