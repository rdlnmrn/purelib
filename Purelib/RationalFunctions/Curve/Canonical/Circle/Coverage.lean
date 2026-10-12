module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

open Purelib.Data
open Purelib.RationalFunctions
/-- The primary chart covers every unit-quadrance point with nonnegative real coordinate.

The explicit parameter is the imaginary coordinate divided by one plus the real coordinate. It lies between minus one
and one, and the unit-base primary circle evaluates exactly to the supplied point. -/
theorem primaryUnitCircle_covers
    (unit : Canonical) (unitNorm : Gaussian.Norm.Basic.normSq unit = 1)
    (realNonnegative : 0 ≤ unit.re) :
    let parameter := unit.im / (1 + unit.re)
    (-1 : Rational) ≤ parameter ∧ parameter ≤ 1 ∧
      (Curve.Canonical.Circle.circle 1).point parameter = unit := by
  let x := unit.re
  let y := unit.im
  let scale : Rational := 1 + x
  let parameter : Rational := y / scale
  have xLessScale : x < scale := by
    have added := Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct
      (show (0 : Rational) < 1 by decide) x
    dsimp only [scale]
    calc
      x = 0 + x := (Rat.Fraction.Field.zero_add x).symm
      _ < 1 + x := added
  have scalePositive : 0 < scale := realNonnegative.trans_lt xLessScale
  have imaginarySquare : y ^ 2 ≤ 1 := by
    have realSquareNonnegative :=
      Rat.Fraction.Order.Arithmetic.sq_nonneg_direct x
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      realSquareNonnegative (y ^ 2)
    have squareLeNorm : y ^ 2 ≤ Gaussian.Norm.Basic.normSq unit := by
      dsimp only [x, y]
      calc
        unit.im ^ 2 = 0 + unit.im ^ 2 :=
          (Rat.Fraction.Field.zero_add _).symm
        _ ≤ unit.re ^ 2 + unit.im ^ 2 := added
        _ = Gaussian.Norm.Basic.normSq unit := rfl
    exact squareLeNorm.trans_eq unitNorm
  have imaginaryLower : (-1 : Rational) ≤ y :=
    Rat.Quadratic.neg_one_le_of_sq_le_one imaginarySquare
  have imaginaryUpper : y ≤ (1 : Rational) :=
    Rat.Quadratic.le_one_of_sq_le_one imaginarySquare
  have oneLeScale : (1 : Rational) ≤ scale := by
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      realNonnegative 1
    dsimp only [scale]
    calc
      1 = 0 + 1 := (Rat.Fraction.Field.zero_add 1).symm
      _ ≤ x + 1 := added
      _ = 1 + x := Rat.Fraction.Field.add_comm _ _
  have negScaleLe : -scale ≤ y :=
    (Rat.Fraction.Order.Arithmetic.neg_le_neg_direct oneLeScale).trans
      imaginaryLower
  have yLeScale : y ≤ scale := imaginaryUpper.trans oneLeScale
  have parameterLower : (-1 : Rational) ≤ parameter := by
    apply (Rat.Fraction.Order.Field.le_div_iff_pos scalePositive).2
    calc
      (-1 : Rational) * scale = -scale := by ring1
      _ ≤ y := negScaleLe
  have parameterUpper : parameter ≤ (1 : Rational) := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos scalePositive).2
    calc
      y ≤ scale := yLeScale
      _ = (1 : Rational) * scale :=
        (Rat.Fraction.Field.one_mul scale).symm
  have parameterScale : parameter * scale = y := by
    exact Rat.Fraction.Field.div_mul_cancel_of_ne y scale
      scalePositive.ne'
  have factored : (1 - x) * scale = y ^ 2 := by
    dsimp only [x, y, scale]
    dsimp only [Gaussian.Norm.Basic.normSq] at unitNorm
    calc
      (1 - unit.re) * (1 + unit.re) =
          1 - (unit.re ^ 2 + unit.im ^ 2) + unit.im ^ 2 := by ring1
      _ = unit.im ^ 2 := by rw [unitNorm]; ring1
  have parameterFactored : (parameter ^ 2 * scale) * scale = y ^ 2 := by
    calc
      (parameter ^ 2 * scale) * scale = (parameter * scale) ^ 2 := by
        ring1
      _ = y ^ 2 := by rw [parameterScale]
  have relation : 1 - x = parameter ^ 2 * scale :=
    Rat.Fraction.Field.mul_right_cancel_of_ne scalePositive.ne'
      (factored.trans parameterFactored.symm)
  have relationExpanded :
      1 - x = parameter ^ 2 * (1 + x) := by
    simpa only [scale] using relation
  have realIdentity :
      1 - parameter ^ 2 = x * (parameter ^ 2 + 1) := by
    calc
      1 - parameter ^ 2 = x + (1 - x) - parameter ^ 2 := by ring1
      _ = x + parameter ^ 2 * (1 + x) - parameter ^ 2 := by
        rw [relationExpanded]
      _ = x * (parameter ^ 2 + 1) := by ring1
  have scaleIdentity : scale * (1 + parameter ^ 2) = 2 := by
    calc
      scale * (1 + parameter ^ 2) = scale + parameter ^ 2 * scale := by
        ring1
      _ = scale + (1 - x) := by rw [← relation]
      _ = 2 := by dsimp only [scale]; ring1
  have imaginaryIdentity :
      2 * parameter = y * (parameter ^ 2 + 1) := by
    calc
      2 * parameter = parameter * 2 :=
        Rat.Fraction.Field.mul_comm _ _
      _ = parameter * (scale * (1 + parameter ^ 2)) := by
        rw [scaleIdentity]
      _ = (parameter * scale) * (parameter ^ 2 + 1) := by ring1
      _ = y * (parameter ^ 2 + 1) := by rw [parameterScale]
  have directionIdentity :
      (⟨1 - parameter ^ 2, 2 * parameter⟩ : Canonical) =
        unit * ⟨parameter ^ 2 + 1, 0⟩ := by
    apply Gaussian.Basic.ext
    · change 1 - parameter ^ 2 =
        x * (parameter ^ 2 + 1) - y * 0
      calc
        1 - parameter ^ 2 = x * (parameter ^ 2 + 1) := realIdentity
        _ = x * (parameter ^ 2 + 1) - y * 0 := by ring1
    · change 2 * parameter = x * 0 + y * (parameter ^ 2 + 1)
      simpa only [Rat.Fraction.Field.mul_zero_direct,
        Rat.Fraction.Field.zero_add] using imaginaryIdentity
  have pointIdentity :
      (Curve.Canonical.Circle.circle 1).point parameter = unit := by
    have denominatorNonzero :=
      Curve.Canonical.Circle.circle_denominator_ne 1 parameter
    apply Gaussian.Field.mul_right_cancel_of_ne
      denominatorNonzero
    calc
      (Curve.Canonical.Circle.circle 1).point parameter *
          (Curve.Canonical.Circle.circle 1).denominatorAt parameter =
          (Curve.Canonical.Circle.circle 1).numeratorAt parameter :=
        (Curve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
          (Curve.Canonical.Circle.circle 1) parameter
            denominatorNonzero).symm
      _ = (1 : Canonical) *
          ⟨1 - parameter ^ 2, 2 * parameter⟩ :=
        Curve.Canonical.Circle.circle_numeratorAt 1 parameter
      _ = ⟨1 - parameter ^ 2, 2 * parameter⟩ :=
        Gaussian.Basic.one_mul _
      _ = unit * ⟨parameter ^ 2 + 1, 0⟩ := directionIdentity
      _ = unit *
          (Curve.Canonical.Circle.circle 1).denominatorAt parameter := by
        rw [Curve.Canonical.Circle.circle_denominatorAt]
  exact ⟨parameterLower, parameterUpper, pointIdentity⟩

/-- The reciprocal chart covers every unit-quadrance point with nonpositive real coordinate.

The explicit parameter is the imaginary coordinate divided by one minus the real coordinate. It lies between minus one
and one, and the unit-base reciprocal circle evaluates exactly to the supplied point. -/
theorem reciprocalUnitCircle_covers
    (unit : Canonical) (unitNorm : Gaussian.Norm.Basic.normSq unit = 1)
    (realNonpositive : unit.re ≤ 0) :
    let parameter := unit.im / (1 - unit.re)
    (-1 : Rational) ≤ parameter ∧ parameter ≤ 1 ∧
      (Curve.Canonical.Circle.reciprocalCircle 1).point parameter =
        unit := by
  let x := unit.re
  let y := unit.im
  let scale : Rational := 1 - x
  let parameter : Rational := y / scale
  have xLessOne : x < (1 : Rational) :=
    realNonpositive.trans_lt (show (0 : Rational) < 1 by decide)
  have scalePositive : 0 < scale := by
    dsimp only [scale]
    exact Rat.Fraction.Order.Arithmetic.sub_pos_direct xLessOne
  have imaginarySquare : y ^ 2 ≤ 1 := by
    have realSquareNonnegative :=
      Rat.Fraction.Order.Arithmetic.sq_nonneg_direct x
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      realSquareNonnegative (y ^ 2)
    have squareLeNorm : y ^ 2 ≤ Gaussian.Norm.Basic.normSq unit := by
      dsimp only [x, y]
      calc
        unit.im ^ 2 = 0 + unit.im ^ 2 :=
          (Rat.Fraction.Field.zero_add _).symm
        _ ≤ unit.re ^ 2 + unit.im ^ 2 := added
        _ = Gaussian.Norm.Basic.normSq unit := rfl
    exact squareLeNorm.trans_eq unitNorm
  have imaginaryLower : (-1 : Rational) ≤ y :=
    Rat.Quadratic.neg_one_le_of_sq_le_one imaginarySquare
  have imaginaryUpper : y ≤ (1 : Rational) :=
    Rat.Quadratic.le_one_of_sq_le_one imaginarySquare
  have negXNonnegative : 0 ≤ -x := by
    have negated := Rat.Fraction.Order.Arithmetic.neg_le_neg_direct realNonpositive
    simpa only [_root_.neg_zero] using negated
  have oneLeScale : (1 : Rational) ≤ scale := by
    have added := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      negXNonnegative 1
    dsimp only [scale]
    calc
      1 = 0 + 1 := (Rat.Fraction.Field.zero_add 1).symm
      _ ≤ -x + 1 := added
      _ = 1 - x := by ring1
  have negScaleLe : -scale ≤ y :=
    (Rat.Fraction.Order.Arithmetic.neg_le_neg_direct oneLeScale).trans
      imaginaryLower
  have yLeScale : y ≤ scale := imaginaryUpper.trans oneLeScale
  have parameterLower : (-1 : Rational) ≤ parameter := by
    apply (Rat.Fraction.Order.Field.le_div_iff_pos scalePositive).2
    calc
      (-1 : Rational) * scale = -scale := by ring1
      _ ≤ y := negScaleLe
  have parameterUpper : parameter ≤ (1 : Rational) := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos scalePositive).2
    calc
      y ≤ scale := yLeScale
      _ = (1 : Rational) * scale :=
        (Rat.Fraction.Field.one_mul scale).symm
  have parameterScale : parameter * scale = y :=
    Rat.Fraction.Field.div_mul_cancel_of_ne y scale scalePositive.ne'
  have factored : (1 + x) * scale = y ^ 2 := by
    dsimp only [x, y, scale]
    dsimp only [Gaussian.Norm.Basic.normSq] at unitNorm
    calc
      (1 + unit.re) * (1 - unit.re) =
          1 - (unit.re ^ 2 + unit.im ^ 2) + unit.im ^ 2 := by ring1
      _ = unit.im ^ 2 := by rw [unitNorm]; ring1
  have parameterFactored : (parameter ^ 2 * scale) * scale = y ^ 2 := by
    calc
      (parameter ^ 2 * scale) * scale = (parameter * scale) ^ 2 := by
        ring1
      _ = y ^ 2 := by rw [parameterScale]
  have relation : 1 + x = parameter ^ 2 * scale :=
    Rat.Fraction.Field.mul_right_cancel_of_ne scalePositive.ne'
      (factored.trans parameterFactored.symm)
  have realIdentity :
      parameter ^ 2 - 1 = x * (parameter ^ 2 + 1) := by
    calc
      parameter ^ 2 - 1 =
          parameter ^ 2 * scale + x * parameter ^ 2 - 1 := by
        dsimp only [scale]
        ring1
      _ = (1 + x) + x * parameter ^ 2 - 1 := by rw [← relation]
      _ = x * (parameter ^ 2 + 1) := by ring1
  have scaleIdentity : scale * (1 + parameter ^ 2) = 2 := by
    calc
      scale * (1 + parameter ^ 2) = scale + parameter ^ 2 * scale := by
        ring1
      _ = scale + (1 + x) := by rw [← relation]
      _ = 2 := by dsimp only [scale]; ring1
  have imaginaryIdentity :
      2 * parameter = y * (parameter ^ 2 + 1) := by
    calc
      2 * parameter = parameter * 2 :=
        Rat.Fraction.Field.mul_comm _ _
      _ = parameter * (scale * (1 + parameter ^ 2)) := by
        rw [scaleIdentity]
      _ = (parameter * scale) * (parameter ^ 2 + 1) := by ring1
      _ = y * (parameter ^ 2 + 1) := by rw [parameterScale]
  have directionIdentity :
      (⟨parameter ^ 2 - 1, 2 * parameter⟩ : Canonical) =
        unit * ⟨parameter ^ 2 + 1, 0⟩ := by
    apply Gaussian.Basic.ext
    · change parameter ^ 2 - 1 =
        x * (parameter ^ 2 + 1) - y * 0
      calc
        parameter ^ 2 - 1 = x * (parameter ^ 2 + 1) := realIdentity
        _ = x * (parameter ^ 2 + 1) - y * 0 := by ring1
    · change 2 * parameter = x * 0 + y * (parameter ^ 2 + 1)
      simpa only [Rat.Fraction.Field.mul_zero_direct,
        Rat.Fraction.Field.zero_add] using imaginaryIdentity
  have pointIdentity :
      (Curve.Canonical.Circle.reciprocalCircle 1).point parameter =
        unit := by
    have denominatorNonzero :=
      Curve.Canonical.Circle.reciprocalCircle_denominator_ne
        1 parameter
    apply Gaussian.Field.mul_right_cancel_of_ne
      denominatorNonzero
    calc
      (Curve.Canonical.Circle.reciprocalCircle 1).point parameter *
          (Curve.Canonical.Circle.reciprocalCircle 1).denominatorAt
            parameter =
          (Curve.Canonical.Circle.reciprocalCircle 1).numeratorAt
            parameter :=
        (Curve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
          (Curve.Canonical.Circle.reciprocalCircle 1) parameter
            denominatorNonzero).symm
      _ = (1 : Canonical) *
          ⟨parameter ^ 2 - 1, 2 * parameter⟩ :=
        Curve.Canonical.Circle.reciprocalCircle_numeratorAt 1 parameter
      _ = ⟨parameter ^ 2 - 1, 2 * parameter⟩ :=
        Gaussian.Basic.one_mul _
      _ = unit * ⟨parameter ^ 2 + 1, 0⟩ := directionIdentity
      _ = unit *
          (Curve.Canonical.Circle.reciprocalCircle 1).denominatorAt
            parameter := by
        rw [Curve.Canonical.Circle.reciprocalCircle_denominatorAt]
  exact ⟨parameterLower, parameterUpper, pointIdentity⟩
end Purelib.RationalFunctions.Curve.Canonical.Circle

end
