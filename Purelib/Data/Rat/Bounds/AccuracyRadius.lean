module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Explicit rational accuracy radii

The minimum of one and one quarter of a rational target defines an explicit
radius. Positivity of the target gives positivity of the radius and a strict
upper bound on its square.
-/

namespace Purelib.Data.Rat.Bounds.AccuracyRadius

open Purelib.Data.Rat
open Fraction.Order

/-- Choose the smaller of one and one quarter of a rational target as an explicit radius.

For a positive target, both inputs to the minimum are positive. Its upper
bounds by one and by one quarter of the target make its square strictly
smaller than the target. -/
@[expose] public def accuracyRadius (target : Fraction.Rational) : Fraction.Rational :=
  min 1 (target / 4)

/-- The explicit accuracy radius is positive when its target is positive.

Both one and the positive target divided by four are strictly positive.
The retained minimum chooses one of these original rational inputs. -/
public theorem accuracyRadius_pos {target : Fraction.Rational} (positive : 0 < target) :
    0 < accuracyRadius target := by
  exact Basic.lt_min (by decide)
    (Field.div_pos_direct positive (by decide))

/-- The square of the explicit accuracy radius is strictly below its positive target.

The retained radius is bounded by one and by one quarter of the target.
Its square is therefore at most the radius, whose strict comparison with
four times itself gives the stated bound using target positivity. -/
public theorem accuracyRadius_sq_lt {target : Fraction.Rational} (positive : 0 < target) :
    accuracyRadius target ^ 2 < target := by
  let radius := accuracyRadius target
  have radiusPositive : 0 < radius := accuracyRadius_pos positive
  have radiusLeOne : radius ≤ 1 := Basic.min_le_left _ _
  have radiusLeQuarter : radius ≤ target / 4 := Basic.min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq
        (Fraction.Field.one_mul radius)
  have radiusLtFourRadius : radius < 4 * radius := by
    calc
      radius = 1 * radius :=
        (Fraction.Field.one_mul radius).symm
      _ < 4 * radius :=
        Arithmetic.mul_lt_mul_of_pos_right_direct
          (by decide) radiusPositive
  have fourRadiusLe : 4 * radius ≤ target := by
    have divided :=
      (Field.le_div_iff_pos
        (by decide : (0 : Fraction.Rational) < 4)).mp radiusLeQuarter
    calc
      4 * radius = radius * 4 :=
        Fraction.Field.mul_comm _ _
      _ ≤ target := divided
  exact radiusSquareLe.trans_lt (radiusLtFourRadius.trans_le fourRadiusLe)

end Purelib.Data.Rat.Bounds.AccuracyRadius
