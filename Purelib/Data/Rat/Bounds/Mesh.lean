module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Explicit rational mesh sides

The minimum of one and one sixteenth of a rational threshold defines an
explicit mesh side. A positive threshold makes that side positive and bounds
eight times its square strictly below the threshold.
-/

namespace Purelib.Data.Rat.Bounds.Mesh

open Purelib.Data.Rat
open Fraction.Order

/-- Choose the smaller of one and one sixteenth of a rational threshold as a mesh side.

For a positive threshold, both inputs to the minimum are positive. Its
one-sixteenth scaling leaves enough margin that eight times its square is
strictly below the original threshold. -/
@[expose] public def meshSide (threshold : Fraction.Rational) : Fraction.Rational :=
  min 1 ((1 / 16 : Fraction.Rational) * threshold)

/-- The chosen mesh side is positive when the threshold is positive.

Both one and the scaled positive threshold are positive. The retained
minimum selects one of those two original values, preserving its strict bound. -/
public theorem meshSide_pos {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) : 0 < meshSide threshold := by
  exact Basic.lt_min
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
    (Arithmetic.mul_pos_direct (by decide) thresholdPositive)

/-- Eight times the chosen mesh-side square is strictly below its positive threshold.

The retained minimum is bounded by both one and one sixteenth of the
threshold. Multiplication by its positive value gives the required square bound. -/
public theorem eight_meshSide_sq_lt {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    8 * meshSide threshold ^ 2 < threshold := by
  let side := meshSide threshold
  have sidePositive : 0 < side := meshSide_pos thresholdPositive
  have sideLeOne : side ≤ 1 := Basic.min_le_left _ _
  have sideLeScale : side ≤ (1 / 16 : Fraction.Rational) * threshold :=
    Basic.min_le_right _ _
  have squareLeSide : side ^ 2 ≤ side := by
    rw [pow_two]
    calc
      side * side ≤ 1 * side :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          sideLeOne sidePositive.le
      _ = side := by ring1
  have eightNonnegative : (0 : Fraction.Rational) ≤ 8 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 8) (by decide)).le
  have inverseIdentity : (8 : Fraction.Rational) * (1 / 16) = 1 / 2 := by decide
  have halfLtOne : (1 / 2 : Fraction.Rational) < 1 := by decide
  calc
    8 * side ^ 2 ≤ 8 * side :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct squareLeSide
        eightNonnegative
    _ ≤ 8 * ((1 / 16 : Fraction.Rational) * threshold) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct sideLeScale
        eightNonnegative
    _ = (1 / 2 : Fraction.Rational) * threshold := by
      rw [show 8 * ((1 / 16 : Fraction.Rational) * threshold) =
          (8 * (1 / 16 : Fraction.Rational)) * threshold by ring1,
        inverseIdentity]
    _ < 1 * threshold :=
      Arithmetic.mul_lt_mul_of_pos_right_direct halfLtOne
        thresholdPositive
    _ = threshold := by ring1

end Purelib.Data.Rat.Bounds.Mesh
