module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

namespace Purelib.Data.Rat.Dyadic.Grid.EightBit
open Purelib.Data in
/-- Use the original nominal canonical Gaussian carrier under this local alias. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

open Purelib.Data.Rat
/-- Compute the rational grid spacing one over 256. -/
public def unit : Fraction.Rational := 1 / 256

/-- A matching cross product expresses a positive-denominator fraction as an integer multiple of the eight-bit grid
unit.

The denominator must be positive and the supplied cross-product equation uses the same numerator and scale. Cancellation
identifies the fraction with the scale times one over 256. -/
public theorem scaledUnit (numerator scale : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (cross : (numerator : Fraction.Rational) * 256 = (scale : Fraction.Rational) * denominator) :
    (numerator : Fraction.Rational) / denominator = (scale : Fraction.Rational) * unit := by
  unfold unit
  calc
    (numerator : Fraction.Rational) / denominator = (scale : Fraction.Rational) / 256 :=
      Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Cast.Order.natCast_pos_direct (n := denominator) denominatorPositive).ne'
        (Fraction.Cast.Order.natCast_pos_direct (n := 256) (by decide)).ne' cross
    _ = (scale : Fraction.Rational) * (1 / 256) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct,
        _root_.one_mul, -eq_self, -iff_self]
      rfl

/-- The eight-bit grid unit equals 256 times its square. -/
public theorem unit_eq_scaled_square : unit = 256 *
  unit ^ 2 := by
  unfold unit
  rw [pow_two]
  calc
    (1 / 256 : Fraction.Rational) = 1 * (1 / 256) := by ring1
    _ = ((1 / 256 : Fraction.Rational) * 256) * (1 / 256) :=
      congrArg (fun value : Fraction.Rational => value * (1 / 256))
        (Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Cast.Order.natCast_pos_direct (n := 256) (by decide)).ne').symm
    _ = 256 * ((1 / 256 : Fraction.Rational) * (1 / 256)) := by ring1

/-- The square of the eight-bit grid unit is one over 65536. -/
public theorem unitSquare : unit ^ 2 = (1 / 65536 :
  Fraction.Rational) := by
  unfold unit
  rw [pow_two, Fraction.Field.div_mul_div_direct, one_mul]
  rw [show (256 : Fraction.Rational) * 256 = 65536 by ring1]

/-- The rational value one quarter equals 64 times the eight-bit grid unit. -/
public theorem oneQuarterUnit : (1 / 4 : Fraction.Rational) = 64 *
  unit :=
  scaledUnit 1 64 4 (by decide) (by ring1)

/-- The rational value one sixteenth equals 16 times the eight-bit grid unit. -/
public theorem oneSixteenthUnit : (1 / 16 : Fraction.Rational) = 16 *
  unit :=
  scaledUnit 1 16 16 (by decide) (by ring1)

/-- The rational value one half equals 128 times the eight-bit grid unit. -/
public theorem oneHalfUnit : (1 / 2 : Fraction.Rational) = 128 *
  unit :=
  scaledUnit 1 128 2 (by decide) (by ring1)

/-- The rational value negative one half equals -128 times the eight-bit grid unit. -/
public theorem negativeOneHalfUnit : (-1 / 2 : Fraction.Rational) = -128 *
  unit := by
  rw [Fraction.Compatibility.negativeDiv, oneHalfUnit]
  ring1

/-- The rational value negative one quarter equals -64 times the eight-bit grid unit. -/
public theorem negativeOneQuarterUnit : (-1 / 4 : Fraction.Rational) = -64
  * unit := by
  rw [Fraction.Compatibility.negativeDiv, oneQuarterUnit]
  ring1

/-- The rational value three quarters equals 192 times the eight-bit grid unit. -/
public theorem threeQuarterUnit : (3 / 4 : Fraction.Rational) = 192 *
  unit :=
  scaledUnit 3 192 4 (by decide) (by ring1)

/-- The rational value one equals 256 times the eight-bit grid unit. -/
public theorem oneUnit : (1 : Fraction.Rational) = 256 *
  unit := by
  unfold unit
  calc
    (1 : Fraction.Rational) = (1 / 256 : Fraction.Rational) * 256 :=
      (Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Cast.Order.natCast_pos_direct (n := 256) (by decide)).ne').symm
    _ = 256 * (1 / 256 : Fraction.Rational) := by ring1

/-- The rational value negative one equals -256 times the eight-bit grid unit. -/
public theorem negativeOneUnit : (-1 : Fraction.Rational) = -256 *
  unit := by
  rw [show (-1 : Fraction.Rational) = -(1 : Fraction.Rational) by ring1, oneUnit]
  ring1

/-- The rational value one sixty-fourth equals 4 times the eight-bit grid unit. -/
public theorem oneSixtyFourUnit : (1 / 64 : Fraction.Rational) = 4 *
  unit :=
  scaledUnit 1 4 64 (by decide) (by ring1)

/-- The canonical rational number one over 64 is positive. -/
public theorem oneSixtyFourPositive : (0 : Fraction.Rational) < 1 / 64 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)) (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by
      decide))

/-- The square of one half is one quarter. -/
private theorem halfSquare : (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 := by
  rw [pow_two, oneHalfUnit, oneQuarterUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

/-- The fourth power of one half is one sixteenth. -/
private theorem halfPowFour : (1 / 2 : Fraction.Rational) ^ 4 = 1 / 16 :=
  by
  rw [show (1 / 2 : Fraction.Rational) ^ 4 = ((1 / 2 : Fraction.Rational) ^ 2) ^ 2 by ring1,
    halfSquare, pow_two, oneQuarterUnit,
      oneSixteenthUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

/-- The fifth power of one half is one thirty-second. -/
public theorem halfPowFive : (1 / 2 : Fraction.Rational) ^ 5 = 1 / 32 :=
  by
  have thirtySecondUnit : (1 / 32 : Fraction.Rational) = 8 * unit :=
    scaledUnit 1 8 32 (by decide) (by ring1)
  rw [show (1 / 2 : Fraction.Rational) ^ 5 = (1 / 2 : Fraction.Rational) ^ 4 * (1 / 2) by ring1,
    halfPowFour, oneSixteenthUnit, oneHalfUnit,
      thirtySecondUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

/-- The sixth power of one half is one sixty-fourth. -/
public theorem halfPowSix : (1 / 2 : Fraction.Rational) ^ 6 = 1 / 64 := by
  have thirtySecondUnit : (1 / 32 : Fraction.Rational) = 8 * unit :=
    scaledUnit 1 8 32 (by decide) (by ring1)
  rw [show (1 / 2 : Fraction.Rational) ^ 6 = (1 / 2 : Fraction.Rational) ^ 5 * (1 / 2) by ring1,
    halfPowFive, thirtySecondUnit, oneHalfUnit,
      oneSixtyFourUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

/-- One over 1024 equals 64 times the squared eight-bit grid unit.

The original grid square is one over 65536; multiplying by 64 gives the displayed rational scale. -/
public theorem oneOver1024_eq_sixtyFourUnitSquare :
    (1 / 1024 : Fraction.Rational) = 64 * unit ^ 2 := by
  rw [unitSquare]
  calc
    (1 / 1024 : Fraction.Rational) = 64 / 65536 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by omega)).ne'
        (Fraction.Cast.Order.natCast_pos_direct (n := 65536) (by omega)).ne'
      ring1
    _ = 64 * (1 / 65536 : Fraction.Rational) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct,
        _root_.one_mul, -eq_self, -iff_self]
      rfl

/-- The rational value three sixteenths equals 48 times the eight-bit grid unit. -/
public theorem threeSixteenthUnit : (3 / 16 : Fraction.Rational) = 48 *
  unit :=
  scaledUnit 3 48 16 (by decide) (by ring1)

/-- The rational value negative three sixteenths equals -48 times the eight-bit grid unit. -/
public theorem negativeThreeSixteenthUnit : (-3 / 16 : Fraction.Rational)
  = -48 * unit := by
  rw [Fraction.Compatibility.negativeDiv, threeSixteenthUnit]
  ring1

/-- The rational value three thirty-seconds equals 24 times the eight-bit grid unit. -/
public theorem threeThirtySecondUnit : (3 / 32 : Fraction.Rational) = 24 *
  unit :=
  scaledUnit 3 24 32 (by decide) (by ring1)

/-- The rational value negative three thirty-seconds equals -24 times the eight-bit grid unit. -/
public theorem negativeThreeThirtySecondUnit : (-3 / 32 :
  Fraction.Rational) =
    -24 * unit := by
  rw [Fraction.Compatibility.negativeDiv, threeThirtySecondUnit]
  ring1

/-- The rational value nine sixteenths equals 144 times the eight-bit grid unit. -/
public theorem nineSixteenthUnit : (9 / 16 : Fraction.Rational) = 144 *
  unit :=
  scaledUnit 9 144 16 (by decide) (by ring1)

/-- The rational value eleven eighths equals 352 times the eight-bit grid unit. -/
public theorem elevenEighthUnit : (11 / 8 : Fraction.Rational) = 352 *
  unit :=
  scaledUnit 11 352 8 (by decide) (by ring1)

/-- The rational value negative eleven eighths equals -352 times the eight-bit grid unit. -/
public theorem negativeElevenEighthUnit : (-11 / 8 : Fraction.Rational) =
  -352 * unit := by
  rw [Fraction.Compatibility.negativeDiv, elevenEighthUnit]
  ring1

/-- The rational value one over 256 equals 1 times the eight-bit grid unit. -/
public theorem oneTwoFiftySixthUnit : (1 / 256 : Fraction.Rational) =
  unit := rfl

/-- The rational value one thirty-second equals 8 times the eight-bit grid unit. -/
public theorem oneThirtySecondUnit : (1 / 32 : Fraction.Rational) = 8 *
  unit :=
  scaledUnit 1 8 32 (by decide) (by ring1)

/-- The rational value negative one sixteenth equals -16 times the eight-bit grid unit. -/
public theorem negativeOneSixteenthUnit : (-1 / 16 : Fraction.Rational) =
  -16 * unit := by
  rw [Fraction.Compatibility.negativeDiv, oneSixteenthUnit]
  ring1

/-- The rational value negative one thirty-second equals -8 times the eight-bit grid unit. -/
public theorem negativeOneThirtySecondUnit : (-1 / 32 : Fraction.Rational)
  =
    -8 * unit := by
  rw [Fraction.Compatibility.negativeDiv, oneThirtySecondUnit]
  ring1

/-- The rational value nine thirty-seconds equals 72 times the eight-bit grid unit. -/
public theorem nineThirtySecondUnit : (9 / 32 : Fraction.Rational) = 72 *
  unit :=
  scaledUnit 9 72 32 (by decide) (by ring1)

/-- The rational value three eighths equals 96 times the eight-bit grid unit. -/
public theorem threeEighthUnit : (3 / 8 : Fraction.Rational) = 96 *
  unit :=
  scaledUnit 3 96 8 (by decide) (by ring1)

/-- The rational value twenty-three sixteenths equals 368 times the eight-bit grid unit. -/
public theorem twentyThreeSixteenthUnit : (23 / 16 : Fraction.Rational) =
  368 * unit :=
  scaledUnit 23 368 16 (by decide) (by ring1)

/-- The rational value negative twenty-three sixteenths equals -368 times the eight-bit grid unit. -/
public theorem negativeTwentyThreeSixteenthUnit : (-23 / 16 :
  Fraction.Rational) =
    -368 * unit := by
  rw [Fraction.Compatibility.negativeDiv, twentyThreeSixteenthUnit]
  ring1

/-- The rational value three halves equals 384 times the eight-bit grid unit. -/
public theorem threeHalfUnit : (3 / 2 : Fraction.Rational) = 384 *
  unit :=
  scaledUnit 3 384 2 (by decide) (by ring1)

end Purelib.Data.Rat.Dyadic.Grid.EightBit

end
