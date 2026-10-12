module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Canonical rational line and circle parameterizations

The CCL branch boundaries originate as coordinate lines or centered norm
circles before finite homographic pullback.  These explicit parameterizations
retain that provenance, including a proof that their parameter denominator
never vanishes.  Homographic transformation can subsequently move them into
the original polynomial coordinate.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

section
open Purelib.Data
open Purelib.RationalFunctions
/-- Multiplying unit-primary-chart coordinates by the common denominator recovers the two numerator coordinates. -/
private theorem circle_one_coordinate_products (parameter :
  Rational) :
    let point := (Curve.Canonical.Circle.circle 1).point parameter
    point.re * (parameter ^ 2 + 1) = 1 - parameter ^ 2 ∧
      point.im * (parameter ^ 2 + 1) = 2 * parameter := by
  let point := (Curve.Canonical.Circle.circle 1).point parameter
  have denominatorNonzero := Curve.Canonical.Circle.circle_denominator_ne 1 parameter
  have numeratorIdentity :=
    Curve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
      (Curve.Canonical.Circle.circle 1) parameter denominatorNonzero
  have realIdentity :=
    congrArg Gaussian.Basic.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg Gaussian.Basic.im numeratorIdentity
  rw [Curve.Canonical.Circle.circle_numeratorAt, Curve.Canonical.Circle.circle_denominatorAt]
    at realIdentity imaginaryIdentity
  simp only [_root_.one_mul,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im]
      at realIdentity imaginaryIdentity
  constructor
  · change point.re * (parameter ^ 2 + 1) = 1 - parameter ^ 2
    change 1 - parameter ^ 2 =
      point.re * (parameter ^ 2 + 1) - point.im * 0
        at realIdentity
    calc
      point.re * (parameter ^ 2 + 1) =
          point.re * (parameter ^ 2 + 1) - point.im * 0 := by ring1
      _ = 1 - parameter ^ 2 := realIdentity.symm
  · change point.im * (parameter ^ 2 + 1) = 2 * parameter
    change 2 * parameter =
      point.re * 0 + point.im * (parameter ^ 2 + 1) at imaginaryIdentity
    simpa only [Rat.Fraction.Field.mul_zero_direct,
      Rat.Fraction.Field.zero_add] using imaginaryIdentity.symm

/-- Multiplying unit-reciprocal-chart coordinates by the common denominator recovers the two numerator coordinates. -/
private theorem reciprocalCircle_one_coordinate_products
    (parameter : Rational) :
    let point := (Curve.Canonical.Circle.reciprocalCircle 1).point parameter
    point.re * (parameter ^ 2 + 1) = parameter ^ 2 - 1 ∧
      point.im * (parameter ^ 2 + 1) = 2 * parameter := by
  let point := (Curve.Canonical.Circle.reciprocalCircle 1).point parameter
  have denominatorNonzero := Curve.Canonical.Circle.reciprocalCircle_denominator_ne 1 parameter
  have numeratorIdentity :=
    Curve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
      (Curve.Canonical.Circle.reciprocalCircle 1) parameter denominatorNonzero
  have realIdentity :=
    congrArg Gaussian.Basic.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg Gaussian.Basic.im numeratorIdentity
  rw [Curve.Canonical.Circle.reciprocalCircle_numeratorAt,
    Curve.Canonical.Circle.reciprocalCircle_denominatorAt] at realIdentity imaginaryIdentity
  simp only [_root_.one_mul,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im]
      at realIdentity imaginaryIdentity
  constructor
  · change point.re * (parameter ^ 2 + 1) = parameter ^ 2 - 1
    change parameter ^ 2 - 1 =
      point.re * (parameter ^ 2 + 1) - point.im * 0
        at realIdentity
    calc
      point.re * (parameter ^ 2 + 1) =
          point.re * (parameter ^ 2 + 1) - point.im * 0 := by ring1
      _ = parameter ^ 2 - 1 := realIdentity.symm
  · change point.im * (parameter ^ 2 + 1) = 2 * parameter
    change 2 * parameter =
      point.re * 0 + point.im * (parameter ^ 2 + 1) at imaginaryIdentity
    simpa only [Rat.Fraction.Field.mul_zero_direct,
      Rat.Fraction.Field.zero_add] using imaginaryIdentity.symm

end

section
open Purelib.Algebra
open Purelib.Data
open Purelib.RationalFunctions
/-- Recover the primary stereographic parameter from its unit-circle point.

Divide the point's imaginary coordinate by one plus its real coordinate. The chart's exact coordinate identities show
that this denominator is nonzero and the quotient is the original parameter. -/
theorem circle_one_parameter_of_point (parameter :
  Rational) :
    let point := (Curve.Canonical.Circle.circle 1).point parameter
    point.im / (1 + point.re) = parameter := by
  let point := (Curve.Canonical.Circle.circle 1).point parameter
  let denominator := parameter ^ 2 + 1
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    exact lt_of_le_of_lt
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter)
      (by
        have added := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
          (show (0 : Rational) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := added)
  have products := circle_one_coordinate_products parameter
  have sumProduct : (1 + point.re) * denominator = 2 := by
    calc
      (1 + point.re) * denominator =
          denominator + point.re * denominator := by ring1
      _ = denominator + (1 - parameter ^ 2) := by rw [products.1]
      _ = 2 := by dsimp only [denominator]; ring1
  have sumNonzero : 1 + point.re ≠ 0 := by
    intro zero
    rw [zero, Rat.Fraction.Field.zero_mul_direct] at sumProduct
    exact (show (0 : Rational) ≠ 2 by decide) sumProduct
  have factorization : point.im = parameter * (1 + point.re) := by
    apply Rat.Fraction.Field.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      point.im * denominator = 2 * parameter := products.2
      _ = parameter * 2 := Rat.Fraction.Field.mul_comm _ _
      _ = parameter * ((1 + point.re) * denominator) := by rw [sumProduct]
      _ = (parameter * (1 + point.re)) * denominator :=
        (Rat.Fraction.Field.mul_assoc _ _ _).symm
  change point.im / (1 + point.re) = parameter
  rw [factorization, Field.ExplicitField.div_eq_mul_inv,
    Rat.Fraction.Field.mul_assoc,
    Rat.Fraction.Field.mul_inv_cancel _ sumNonzero,
    Rat.Fraction.Field.mul_one_direct]

/-- Recover the reciprocal stereographic parameter from its unit-circle point.

Divide the point's imaginary coordinate by one minus its real coordinate. The reciprocal chart identities make this
denominator nonzero and recover the original parameter. -/
theorem reciprocalCircle_one_parameter_of_point (parameter :
  Rational) :
    let point := (Curve.Canonical.Circle.reciprocalCircle 1).point parameter
    point.im / (1 - point.re) = parameter := by
  let point := (Curve.Canonical.Circle.reciprocalCircle 1).point parameter
  let denominator := parameter ^ 2 + 1
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    exact lt_of_le_of_lt
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct parameter)
      (by
        have added := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
          (show (0 : Rational) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := added)
  have products := reciprocalCircle_one_coordinate_products parameter
  have differenceProduct : (1 - point.re) * denominator = 2 := by
    calc
      (1 - point.re) * denominator =
          denominator - point.re * denominator := by ring1
      _ = denominator - (parameter ^ 2 - 1) := by rw [products.1]
      _ = 2 := by dsimp only [denominator]; ring1
  have differenceNonzero : 1 - point.re ≠ 0 := by
    intro zero
    rw [zero, Rat.Fraction.Field.zero_mul_direct] at differenceProduct
    exact (show (0 : Rational) ≠ 2 by decide) differenceProduct
  have factorization : point.im = parameter * (1 - point.re) := by
    apply Rat.Fraction.Field.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      point.im * denominator = 2 * parameter := products.2
      _ = parameter * 2 := Rat.Fraction.Field.mul_comm _ _
      _ = parameter * ((1 - point.re) * denominator) := by
        rw [differenceProduct]
      _ = (parameter * (1 - point.re)) * denominator :=
        (Rat.Fraction.Field.mul_assoc _ _ _).symm
  change point.im / (1 - point.re) = parameter
  rw [factorization, Field.ExplicitField.div_eq_mul_inv,
    Rat.Fraction.Field.mul_assoc,
    Rat.Fraction.Field.mul_inv_cancel _ differenceNonzero,
    Rat.Fraction.Field.mul_one_direct]

end

open Purelib.Data
open Purelib.RationalFunctions
/-- The unit-base primary circle chart is injective in its rational parameter. -/
theorem circle_one_point_injective : Function.Injective
  (Curve.Canonical.Circle.circle 1).point := by
  intro left right equal
  have recovered := congrArg
    (fun point : Canonical => point.im / (1 + point.re)) equal
  simpa only [circle_one_parameter_of_point] using recovered

/-- The unit-base reciprocal circle chart is injective in its rational parameter. -/
theorem reciprocalCircle_one_point_injective :
    Function.Injective (Curve.Canonical.Circle.reciprocalCircle 1).point := by
  intro left right equal
  have recovered := congrArg
    (fun point : Canonical => point.im / (1 - point.re)) equal
  simpa only [reciprocalCircle_one_parameter_of_point] using recovered

/-- A primary circle chart with nonzero base is injective in its rational parameter. -/
theorem circle_point_injective (base : Canonical)
  (baseNonzero : base ≠ 0) :
    Function.Injective (Curve.Canonical.Circle.circle base).point := by
  intro left right equal
  have equal' : base * (Curve.Canonical.Circle.circle 1).point left =
      base * (Curve.Canonical.Circle.circle 1).point right := by
    calc
      base * (Curve.Canonical.Circle.circle 1).point left = (Curve.Canonical.Circle.circle base).point left :=
        (Curve.Canonical.Circle.circle_point_scale base left).symm
      _ = (Curve.Canonical.Circle.circle base).point right := equal
      _ = base * (Curve.Canonical.Circle.circle 1).point right := Curve.Canonical.Circle.circle_point_scale base right
  apply circle_one_point_injective
  apply Gaussian.Field.mul_right_cancel_of_ne baseNonzero
  calc
    (Curve.Canonical.Circle.circle 1).point left * base = base * (Curve.Canonical.Circle.circle 1).point left :=
      Gaussian.Basic.mul_comm _ _
    _ = base * (Curve.Canonical.Circle.circle 1).point right := equal'
    _ = (Curve.Canonical.Circle.circle 1).point right * base :=
      Gaussian.Basic.mul_comm _ _

/-- A reciprocal circle chart with nonzero base is injective in its rational parameter. -/
theorem reciprocalCircle_point_injective
    (base : Canonical) (baseNonzero : base ≠ 0) :
    Function.Injective (Curve.Canonical.Circle.reciprocalCircle base).point := by
  intro left right equal
  have equal' : base * (Curve.Canonical.Circle.reciprocalCircle 1).point left =
      base * (Curve.Canonical.Circle.reciprocalCircle 1).point right := by
    calc
      base * (Curve.Canonical.Circle.reciprocalCircle 1).point left =
          (Curve.Canonical.Circle.reciprocalCircle base).point left :=
        (Curve.Canonical.Circle.reciprocalCircle_point_scale base left).symm
      _ = (Curve.Canonical.Circle.reciprocalCircle base).point right := equal
      _ = base * (Curve.Canonical.Circle.reciprocalCircle 1).point right :=
        Curve.Canonical.Circle.reciprocalCircle_point_scale base right
  apply reciprocalCircle_one_point_injective
  apply Gaussian.Field.mul_right_cancel_of_ne baseNonzero
  calc
    (Curve.Canonical.Circle.reciprocalCircle 1).point left * base =
        base * (Curve.Canonical.Circle.reciprocalCircle 1).point left :=
      Gaussian.Basic.mul_comm _ _
    _ = base * (Curve.Canonical.Circle.reciprocalCircle 1).point right := equal'
    _ = (Curve.Canonical.Circle.reciprocalCircle 1).point right * base :=
      Gaussian.Basic.mul_comm _ _
end Purelib.RationalFunctions.Curve.Canonical.Circle

end
