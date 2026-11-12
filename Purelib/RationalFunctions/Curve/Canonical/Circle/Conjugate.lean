module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
import Purelib.Data.Gaussian.Conjugate.Arithmetic
import Purelib.Tactic.Ring

/-!
# Conjugation of the original unit-circle chart points

Both original rational chart numerators keep their real coordinate and
negate their imaginary coordinate under parameter reflection. Their same
real denominator is unchanged, so conjugation reverses the chart parameter.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- Conjugating the original primary unit-circle point negates its same rational parameter. -/
theorem conj_circle (parameter : Rational) :
    Canonical.conj ((circle 1).point parameter) = (circle 1).point (-parameter) := by
  unfold RationalCurve.point
  rewrite [circle_numeratorAt, circle_numeratorAt, circle_denominatorAt, circle_denominatorAt,
    Basic.one_mul, Basic.one_mul, Canonical.conj_mul, Canonical.conj_inv]
  apply congrArg₂ (fun numerator denominator : Canonical => numerator * denominator⁻¹)
  · apply Canonical.ext
    · change 1 - parameter ^ 2 = 1 - (-parameter) ^ 2
      ring1
    · change -(2 * parameter) = 2 * (-parameter)
      ring1
  · apply Canonical.ext
    · change parameter ^ 2 + 1 = (-parameter) ^ 2 + 1
      ring1
    · change -(0 : Rational) = 0
      ring1

/-- Conjugating the original reciprocal unit-circle point negates its same rational parameter. -/
theorem conj_reciprocalCircle (parameter : Rational) :
    Canonical.conj ((reciprocalCircle 1).point parameter) = (reciprocalCircle 1).point (-parameter) := by
  unfold RationalCurve.point
  rewrite [reciprocalCircle_numeratorAt, reciprocalCircle_numeratorAt,
    reciprocalCircle_denominatorAt, reciprocalCircle_denominatorAt,
    Basic.one_mul, Basic.one_mul, Canonical.conj_mul, Canonical.conj_inv]
  apply congrArg₂ (fun numerator denominator : Canonical => numerator * denominator⁻¹)
  · apply Canonical.ext
    · change parameter ^ 2 - 1 = (-parameter) ^ 2 - 1
      ring1
    · change -(2 * parameter) = 2 * (-parameter)
      ring1
  · apply Canonical.ext
    · change parameter ^ 2 + 1 = (-parameter) ^ 2 + 1
      ring1
    · change -(0 : Rational) = 0
      ring1

end Purelib.RationalFunctions.Curve.Canonical.Circle

end
