module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Coordinates
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Orientation of the two original waist banks

The affine branch-segment coordinate increases along both forward rational
quarters and decreases along their reflected time reversals. The proof clears
only the displayed positive stereographic denominators and retains the exact
original direction readings. The original parameter bounds pay every sign.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle

/-- The displayed stereographic scalar denominator is strictly positive. -/
private theorem scalar_pos (time : Fraction.Rational) : 0 < time ^ 2 + 1 :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Arithmetic.sq_nonneg_direct time) (by decide +kernel)

/-- The first quarter's original real reading decreases with its nonnegative parameter. -/
private theorem real_antitone {first last : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ last) :
    (Stereographic.unitQuarterPoint last).re ≤ (Stereographic.unitQuarterPoint first).re := by
  let cost := (first ^ 2 + 1) * (last ^ 2 + 1)
  have positive : 0 < cost := Arithmetic.mul_pos_direct (scalar_pos first) (scalar_pos last)
  have identity : ((Stereographic.unitQuarterPoint first).re -
      (Stereographic.unitQuarterPoint last).re) * cost = 2 * (last - first) * (last + first) := by
    calc
      _ = ((Stereographic.unitQuarterPoint first).re * (first ^ 2 + 1)) * (last ^ 2 + 1) -
          ((Stereographic.unitQuarterPoint last).re * (last ^ 2 + 1)) * (first ^ 2 + 1) := by
        unfold cost
        ring1
      _ = (1 - first ^ 2) * (last ^ 2 + 1) - (1 - last ^ 2) * (first ^ 2 + 1) := by
        rewrite [Stereographic.unitQuarterPoint_re_mul_scalar, Stereographic.unitQuarterPoint_re_mul_scalar]
        rfl
      _ = _ := by ring1
  have movement : 0 ≤ last - first := Arithmetic.sub_nonneg_direct ordered
  have sum : 0 ≤ last + first := by
    have result := Arithmetic.add_le_add_direct (nonnegative.trans ordered) nonnegative
    rewrite [Fraction.Field.zero_add] at result
    exact result
  have paid := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2) movement) sum
  have scaled : 0 * cost ≤ ((Stereographic.unitQuarterPoint first).re -
      (Stereographic.unitQuarterPoint last).re) * cost := by
    rewrite [Fraction.Field.zero_mul_direct, identity]
    exact paid
  exact Arithmetic.le_of_sub_nonneg_direct
    (Arithmetic.le_of_mul_le_mul_right_direct scaled positive)

/-- The second quarter's original imaginary reading increases on the same closed unit interval. -/
private theorem imaginary_monotone {first last : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ last) (upper : last ≤ 1) :
    (Stereographic.unitQuarterPoint first).im ≤ (Stereographic.unitQuarterPoint last).im := by
  let cost := (first ^ 2 + 1) * (last ^ 2 + 1)
  have positive : 0 < cost := Arithmetic.mul_pos_direct (scalar_pos first) (scalar_pos last)
  have identity : ((Stereographic.unitQuarterPoint last).im -
      (Stereographic.unitQuarterPoint first).im) * cost = 2 * (last - first) * (1 - first * last) := by
    calc
      _ = ((Stereographic.unitQuarterPoint last).im * (last ^ 2 + 1)) * (first ^ 2 + 1) -
          ((Stereographic.unitQuarterPoint first).im * (first ^ 2 + 1)) * (last ^ 2 + 1) := by
        unfold cost
        ring1
      _ = (2 * last) * (first ^ 2 + 1) - (2 * first) * (last ^ 2 + 1) := by
        rewrite [Stereographic.unitQuarterPoint_im_mul_scalar, Stereographic.unitQuarterPoint_im_mul_scalar]
        rfl
      _ = _ := by ring1
  have product : first * last ≤ 1 := by
    calc
      _ ≤ first * 1 := Arithmetic.mul_le_mul_of_nonneg_left_direct upper nonnegative
      _ = first := Fraction.Field.mul_one_direct _
      _ ≤ 1 := ordered.trans upper
  have paid := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
      (Arithmetic.sub_nonneg_direct ordered))
    (Arithmetic.sub_nonneg_direct product)
  have scaled : 0 * cost ≤ ((Stereographic.unitQuarterPoint last).im -
      (Stereographic.unitQuarterPoint first).im) * cost := by
    rewrite [Fraction.Field.zero_mul_direct, identity]
    exact paid
  exact Arithmetic.le_of_sub_nonneg_direct
    (Arithmetic.le_of_mul_le_mul_right_direct scaled positive)

/-- Each original forward bank half runs monotonically toward the fixed labelled branch. -/
public theorem forward_parameter_mono (half : Half) {first last : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ last) (upper : last ≤ 1) :
    segmentParameter (forwardDirection half first) ≤ segmentParameter (forwardDirection half last) := by
  have eraseZero (value : Fraction.Rational) : value - 0 = value := by ring0
  have decreasing : (forwardDirection half last).value.re ≤ (forwardDirection half first).value.re := by
    cases half with
    | first =>
      change (direction .first last).value.re ≤ (direction .first first).value.re
      rewrite [direction_value, direction_value]
      change 1 * (Stereographic.unitQuarterPoint last).re - 0 * (Stereographic.unitQuarterPoint last).im ≤
        1 * (Stereographic.unitQuarterPoint first).re - 0 * (Stereographic.unitQuarterPoint first).im
      rewrite [Fraction.Field.one_mul, Fraction.Field.one_mul,
        Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct,
        eraseZero, eraseZero]
      exact real_antitone nonnegative ordered
    | second =>
      change (direction .second last).value.re ≤ (direction .second first).value.re
      rewrite [direction_value, direction_value]
      change 0 * (Stereographic.unitQuarterPoint last).re - 1 * (Stereographic.unitQuarterPoint last).im ≤
        0 * (Stereographic.unitQuarterPoint first).re - 1 * (Stereographic.unitQuarterPoint first).im
      rewrite [Fraction.Field.one_mul, Fraction.Field.one_mul,
        Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct]
      have result := Arithmetic.sub_le_sub_left_direct (imaginary_monotone nonnegative ordered upper) 0
      exact result
  change (1 - (forwardDirection half first).value.re) * (2 : Fraction.Rational)⁻¹ ≤
    (1 - (forwardDirection half last).value.re) * (2 : Fraction.Rational)⁻¹
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.sub_le_sub_left_direct decreasing 1)
    (Fraction.Order.Field.inv_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 2)).le

/-- Each reflected returning bank half runs monotonically in the opposite original segment orientation. -/
public theorem reverse_parameter_antitone (half : Half) {first last : Fraction.Rational}
    (nonnegative : 0 ≤ first) (ordered : first ≤ last) (upper : last ≤ 1) :
    segmentParameter (reverseDirection half last) ≤ segmentParameter (reverseDirection half first) := by
  change segmentParameter (mirror (forwardDirection half (1 - last))) ≤
    segmentParameter (mirror (forwardDirection half (1 - first)))
  rewrite [segmentParameter_mirror, segmentParameter_mirror]
  have reverseUpper : 1 - first ≤ 1 := by
    have result := Arithmetic.sub_le_sub_left_direct nonnegative 1
    rewrite [(by decide +kernel : (1 : Fraction.Rational) - 0 = 1)] at result
    exact result
  exact forward_parameter_mono half (Arithmetic.sub_nonneg_direct upper)
    (Arithmetic.sub_le_sub_left_direct ordered 1) reverseUpper

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks
