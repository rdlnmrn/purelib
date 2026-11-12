module

public import Purelib.Geometry.Rational.Box.Interior
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Transport of original interior side gaps

Bounded coordinate displacement loses at most the same radius from each
original side gap. A radius below their positive minimum preserves strict
containment and a lower bound for the four squared side gaps.
-/

public section

namespace Purelib.Geometry.Rational.Box.Interior

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Fraction.Order

/-- Moving an original point by the displayed coordinate radius loses at most that radius from every box side gap.

The original four-gap minimum bounds each retained side separately. Both
signed bounds on each actual coordinate displacement transport those four
inequalities to the same original box at the target point. -/
theorem coordinate_gaps_lower_of_near {box : Box} {point target : Canonical} {radius : Fraction.Rational}
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) :
    strictCoordinateGap box point - radius ≤ target.re - box.xLower ∧
      strictCoordinateGap box point - radius ≤ box.xUpper - target.re ∧
      strictCoordinateGap box point - radius ≤ target.im - box.yLower ∧
      strictCoordinateGap box point - radius ≤ box.yUpper - target.im := by
  have left : strictCoordinateGap box point ≤ point.re - box.xLower := Basic.min_le_left _ _
  have right : strictCoordinateGap box point ≤ box.xUpper - point.re :=
    (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)
  have bottom : strictCoordinateGap box point ≤ point.im - box.yLower :=
    (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))
  have top : strictCoordinateGap box point ≤ box.yUpper - point.im :=
    (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))
  constructor
  · calc
      _ ≤ (point.re - box.xLower) - radius := Arithmetic.sub_le_sub_right_direct left radius
      _ = (point.re - box.xLower) + (-radius) := by ring1
      _ ≤ (point.re - box.xLower) + (target.re - point.re) := Arithmetic.add_le_add_direct le_rfl near.1
      _ = target.re - box.xLower := by ring1
  · constructor
    · calc
        _ ≤ (box.xUpper - point.re) - radius := Arithmetic.sub_le_sub_right_direct right radius
        _ ≤ (box.xUpper - point.re) - (target.re - point.re) := Arithmetic.sub_le_sub_left_direct near.2.1 _
        _ = box.xUpper - target.re := by ring1
    · constructor
      · calc
          _ ≤ (point.im - box.yLower) - radius := Arithmetic.sub_le_sub_right_direct bottom radius
          _ = (point.im - box.yLower) + (-radius) := by ring1
          _ ≤ (point.im - box.yLower) + (target.im - point.im) := Arithmetic.add_le_add_direct le_rfl near.2.2.1
          _ = target.im - box.yLower := by ring1
      · calc
          _ ≤ (box.yUpper - point.im) - radius := Arithmetic.sub_le_sub_right_direct top radius
          _ ≤ (box.yUpper - point.im) - (target.im - point.im) := Arithmetic.sub_le_sub_left_direct near.2.2.2 _
          _ = box.yUpper - target.im := by ring1

/-- Displacement below the original minimum side gap keeps the target point strictly inside that same box. -/
theorem strictContains_of_near {box : Box} {point target : Canonical} {radius : Fraction.Rational}
    (small : radius < strictCoordinateGap box point)
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) : box.StrictContains target := by
  have positive := Arithmetic.sub_pos_direct small
  have gaps := coordinate_gaps_lower_of_near (box := box) near
  exact ⟨Arithmetic.lt_of_sub_pos_direct (positive.trans_le gaps.1),
    Arithmetic.lt_of_sub_pos_direct (positive.trans_le gaps.2.1),
    Arithmetic.lt_of_sub_pos_direct (positive.trans_le gaps.2.2.1),
    Arithmetic.lt_of_sub_pos_direct (positive.trans_le gaps.2.2.2)⟩

/-- The target's four squared side gaps bound the square of the original minimum gap minus the displacement radius. -/
theorem squared_gaps_lower_of_near {box : Box} {point target : Canonical} {radius : Fraction.Rational}
    (small : radius < strictCoordinateGap box point)
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) :
    (strictCoordinateGap box point - radius) ^ 2 ≤
      min ((target.re - box.xLower) ^ 2)
        (min ((box.xUpper - target.re) ^ 2)
          (min ((target.im - box.yLower) ^ 2) ((box.yUpper - target.im) ^ 2))) := by
  have gaps := coordinate_gaps_lower_of_near (box := box) near
  have nonnegative := Arithmetic.sub_nonneg_direct small.le
  exact Basic.le_min (Arithmetic.pow_le_pow_direct nonnegative gaps.1 2)
    (Basic.le_min (Arithmetic.pow_le_pow_direct nonnegative gaps.2.1 2)
      (Basic.le_min (Arithmetic.pow_le_pow_direct nonnegative gaps.2.2.1 2)
        (Arithmetic.pow_le_pow_direct nonnegative gaps.2.2.2 2)))

end Purelib.Geometry.Rational.Box.Interior
