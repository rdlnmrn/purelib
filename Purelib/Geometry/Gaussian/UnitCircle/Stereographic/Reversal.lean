module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Coordinates
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Exact reversal of the original stereographic quarter

The computed Mobius parameter `(1-t)/(1+t)` exchanges the original quarter's
real and imaginary coordinate readings. The displayed denominator clearance,
unit-interval bounds and involution retain that exact original finite time.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The computed parameter reversal between an original waist quarter and its reflected quarter. -/
@[expose] public def reverseTime (time : Fraction.Rational) : Fraction.Rational := (1 - time) / (1 + time)

/-- A nonnegative original time clears the displayed reversal denominator. -/
private theorem denominator_pos {time : Fraction.Rational} (nonnegative : 0 ≤ time) : 0 < 1 + time :=
  Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) nonnegative

/-- The computed reversal remains on the same closed rational unit interval. -/
public theorem reverseTime_bounds {time : Fraction.Rational} (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    0 ≤ reverseTime time ∧ reverseTime time ≤ 1 := by
  constructor
  · exact Fraction.Order.Field.div_nonneg_direct (Arithmetic.sub_nonneg_direct upper)
      (denominator_pos nonnegative).le
  · apply (Fraction.Order.Field.div_le_iff_pos (denominator_pos nonnegative)).mpr
    have first : 1 - time ≤ 1 := by
      have result := Arithmetic.sub_le_sub_left_direct nonnegative 1
      rewrite [(by decide +kernel : (1 : Fraction.Rational) - 0 = 1)] at result
      exact result
    have last : 1 ≤ 1 + time := by
      have result := Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) nonnegative
      rewrite [add_zero] at result
      exact result
    rewrite [Fraction.Field.one_mul]
    exact first.trans last

/-- The displayed original reversal denominator recovers its exact retained numerator. -/
private theorem reverseTime_product {time : Fraction.Rational} (nonnegative : 0 ≤ time) :
    reverseTime time * (1 + time) = 1 - time :=
  Fraction.Field.div_mul_cancel_of_ne _ _ (denominator_pos nonnegative).ne'

/-- Reversal twice recovers the original finite chart time. -/
public theorem reverseTime_reverseTime {time : Fraction.Rational} (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    reverseTime (reverseTime time) = time := by
  have reverseNonnegative := (reverseTime_bounds nonnegative upper).1
  apply Fraction.Field.mul_right_cancel_of_ne (denominator_pos nonnegative).ne'
  apply Fraction.Field.mul_right_cancel_of_ne (denominator_pos reverseNonnegative).ne'
  calc
    reverseTime (reverseTime time) * (1 + time) * (1 + reverseTime time) =
        (reverseTime (reverseTime time) * (1 + reverseTime time)) * (1 + time) := by ring1
    _ = (1 - reverseTime time) * (1 + time) := by
      rewrite [reverseTime_product reverseNonnegative]
      rfl
    _ = (1 + time) - reverseTime time * (1 + time) := by ring1
    _ = (1 + time) - (1 - time) := by
      rewrite [reverseTime_product nonnegative]
      rfl
    _ = time * (1 + time) * (1 + reverseTime time) := by
      calc
        _ = time * ((1 + time) + (1 - time)) := by ring1
        _ = time * ((1 + time) + reverseTime time * (1 + time)) :=
          congrArg (fun value => time * ((1 + time) + value)) (reverseTime_product nonnegative).symm
        _ = _ := by ring1

/-- The original stereographic scalar denominator is positive at each retained rational time. -/
private theorem circle_scalar_pos (time : Fraction.Rational) : 0 < time ^ 2 + 1 :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Arithmetic.sq_nonneg_direct time) (by decide +kernel)

/-- Reversal exchanges the two original retained stereographic coordinate readings. -/
public theorem unitQuarterPoint_reverseTime_readings {time : Fraction.Rational} (nonnegative : 0 ≤ time) :
    (unitQuarterPoint (reverseTime time)).re = (unitQuarterPoint time).im ∧
      (unitQuarterPoint (reverseTime time)).im = (unitQuarterPoint time).re := by
  let reversed := reverseTime time
  have numerator : reversed * (1 + time) = 1 - time := reverseTime_product nonnegative
  have square : reversed ^ 2 * (1 + time) ^ 2 = (1 - time) ^ 2 := by
    calc
      _ = (reversed * (1 + time)) ^ 2 := by ring1
      _ = _ := congrArg (fun value => value ^ 2) numerator
  have denominator : (reversed ^ 2 + 1) * (1 + time) ^ 2 = (1 - time) ^ 2 + (1 + time) ^ 2 := by
    calc
      _ = reversed ^ 2 * (1 + time) ^ 2 + (1 + time) ^ 2 := by ring1
      _ = _ := congrArg (fun value => value + (1 + time) ^ 2) square
  have scaleNonzero : (1 + time) ^ 2 ≠ 0 :=
    (Arithmetic.pow_pos_direct (denominator_pos nonnegative) 2).ne'
  have realCross : (1 - reversed ^ 2) * (time ^ 2 + 1) = 2 * time * (reversed ^ 2 + 1) := by
    apply Fraction.Field.mul_right_cancel_of_ne scaleNonzero
    calc
      _ = ((1 + time) ^ 2 - reversed ^ 2 * (1 + time) ^ 2) * (time ^ 2 + 1) := by ring1
      _ = ((1 + time) ^ 2 - (1 - time) ^ 2) * (time ^ 2 + 1) := by
        rewrite [square]
        rfl
      _ = 2 * time * ((1 - time) ^ 2 + (1 + time) ^ 2) := by ring1
      _ = 2 * time * ((reversed ^ 2 + 1) * (1 + time) ^ 2) :=
        congrArg (fun value => 2 * time * value) denominator.symm
      _ = _ := by ring1
  have imaginaryCross : 2 * reversed * (time ^ 2 + 1) = (1 - time ^ 2) * (reversed ^ 2 + 1) := by
    apply Fraction.Field.mul_right_cancel_of_ne scaleNonzero
    calc
      _ = 2 * (reversed * (1 + time)) * (time ^ 2 + 1) * (1 + time) := by ring1
      _ = 2 * (1 - time) * (time ^ 2 + 1) * (1 + time) := by
        rewrite [numerator]
        rfl
      _ = (1 - time ^ 2) * ((1 - time) ^ 2 + (1 + time) ^ 2) := by ring1
      _ = (1 - time ^ 2) * ((reversed ^ 2 + 1) * (1 + time) ^ 2) :=
        congrArg (fun value => (1 - time ^ 2) * value) denominator.symm
      _ = _ := by ring1
  have costNonzero : (reversed ^ 2 + 1) * (time ^ 2 + 1) ≠ 0 :=
    (Arithmetic.mul_pos_direct (circle_scalar_pos reversed) (circle_scalar_pos time)).ne'
  constructor
  · apply Fraction.Field.mul_right_cancel_of_ne costNonzero
    calc
      _ = ((unitQuarterPoint reversed).re * (reversed ^ 2 + 1)) * (time ^ 2 + 1) := by ring1
      _ = (1 - reversed ^ 2) * (time ^ 2 + 1) :=
        congrArg (fun value => value * (time ^ 2 + 1)) (unitQuarterPoint_re_mul_scalar reversed)
      _ = 2 * time * (reversed ^ 2 + 1) := realCross
      _ = ((unitQuarterPoint time).im * (time ^ 2 + 1)) * (reversed ^ 2 + 1) :=
        congrArg (fun value => value * (reversed ^ 2 + 1)) (unitQuarterPoint_im_mul_scalar time).symm
      _ = _ := by ring1
  · apply Fraction.Field.mul_right_cancel_of_ne costNonzero
    calc
      _ = ((unitQuarterPoint reversed).im * (reversed ^ 2 + 1)) * (time ^ 2 + 1) := by ring1
      _ = 2 * reversed * (time ^ 2 + 1) :=
        congrArg (fun value => value * (time ^ 2 + 1)) (unitQuarterPoint_im_mul_scalar reversed)
      _ = (1 - time ^ 2) * (reversed ^ 2 + 1) := imaginaryCross
      _ = ((unitQuarterPoint time).re * (time ^ 2 + 1)) * (reversed ^ 2 + 1) :=
        congrArg (fun value => value * (reversed ^ 2 + 1)) (unitQuarterPoint_re_mul_scalar time).symm
      _ = _ := by ring1

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic
