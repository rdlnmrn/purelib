module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Finite tangent and remainder laws for the original rational circle chart

The same original chart point has a fractional-linear presentation with real
part one in its denominator. Exact finite differences give a quadratic
remainder bounded at every rational base parameter and increment. Its tangent
is the original point times a purely imaginary logarithmic velocity.
-/

public section

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Algebra.Field

/-- The original fractional-linear chart denominator, whose real coordinate is exactly one. -/
@[expose] def denominator (time : Fraction.Rational) : Canonical := ⟨1, -time⟩

/-- The exact real increment embedded in the original Gaussian rational carrier. -/
@[expose] def increment (value : Fraction.Rational) : Canonical := ⟨value, 0⟩

/-- The actual embedded real chart increment has its exact original squared quadrance. -/
theorem increment_normSq (delta : Fraction.Rational) :
    Norm.Basic.normSq (increment delta) = delta ^ 2 := by
  change delta ^ 2 + 0 ^ 2 = delta ^ 2
  ring1

/-- The same original embedded increment's squared quadrance is exactly its chart fourth power. -/
theorem increment_fourth (delta : Fraction.Rational) :
    Norm.Basic.normSq (increment delta) ^ 2 = delta ^ 4 := by
  rewrite [increment_normSq]
  ring1

/-- Two actual chart times in the original unit interval internally pay the embedded increment's unit-disk condition. -/
theorem increment_unit {time delta : Fraction.Rational} (first : 0 ≤ time ∧ time ≤ 1)
    (last : 0 ≤ time + delta ∧ time + delta ≤ 1) :
    Norm.Basic.normSq (increment delta) ≤ 1 := by
  have lower := Arithmetic.sub_le_sub_direct last.1 first.2
  have upper := Arithmetic.sub_le_sub_direct last.2 first.1
  have difference : time + delta - time = delta := by ring1
  rewrite [difference] at lower upper
  have squared := Box.sq_le_endpoint_max lower upper
  have endpoints : max ((0 - 1 : Fraction.Rational) ^ 2) ((1 - 0 : Fraction.Rational) ^ 2) = 1 := by decide +kernel
  rewrite [endpoints] at squared
  rewrite [increment_normSq]
  exact squared

/-- The displayed fractional-linear denominator never vanishes at a rational parameter. -/
theorem denominator_ne_zero (time : Fraction.Rational) : denominator time ≠ 0 := by
  intro zero
  have real := congrArg (fun value : Canonical => value.re) zero
  change (1 : Fraction.Rational) = 0 at real
  exact (by decide +kernel : (1 : Fraction.Rational) ≠ 0) real

/-- The denominator's conjugate is also nonzero at every rational parameter. -/
private theorem conjugate_ne_zero (time : Fraction.Rational) : Basic.conj (denominator time) ≠ 0 := by
  intro zero
  have real := congrArg (fun value : Canonical => value.re) zero
  change (1 : Fraction.Rational) = 0 at real
  exact (by decide +kernel : (1 : Fraction.Rational) ≠ 0) real

/-- The original real chart denominator is the product of this same fractional-linear pair. -/
private theorem denominator_product (time : Fraction.Rational) :
    Basic.conj (denominator time) * denominator time = unitCircleDenominator time := by
  apply Basic.ext
  · change 1 * 1 - -(-time) * (-time) = time ^ 2 + 1
    ring1
  · change 1 * (-time) + -(-time) * 1 = 0
    ring1

/-- The original displayed chart numerator is the square of the same conjugate denominator. -/
private theorem numerator_square (time : Fraction.Rational) :
    unitCircleDirection time = Basic.conj (denominator time) ^ 2 := by
  rewrite [pow_two]
  apply Basic.ext
  · change 1 - time ^ 2 = 1 * 1 - -(-time) * -(-time)
    ring1
  · change 2 * time = 1 * -(-time) + -(-time) * 1
    ring1

/-- The original circle point retains its exact fractional-linear numerator after clearing the same denominator. -/
private theorem point_mul_denominator (time : Fraction.Rational) :
    unitQuarterPoint time * denominator time = Basic.conj (denominator time) := by
  apply ExplicitField.eq_of_mul_eq_mul_right (conjugate_ne_zero time)
  calc
    (unitQuarterPoint time * denominator time) * Basic.conj (denominator time) =
        unitQuarterPoint time * (Basic.conj (denominator time) * denominator time) := by ring1
    _ = unitCircleDirection time := by
      rewrite [denominator_product, unitQuarterPoint_mul_denominator]
      rfl
    _ = Basic.conj (denominator time) * Basic.conj (denominator time) := by
      rewrite [numerator_square, pow_two]
      rfl

/-- The original chart point has the exact reciprocal presentation used by its finite difference law. -/
private theorem point_reciprocal (time : Fraction.Rational) :
    unitQuarterPoint time = -1 + 2 / denominator time := by
  apply ExplicitField.eq_of_mul_eq_mul_right (denominator_ne_zero time)
  calc
    unitQuarterPoint time * denominator time = Basic.conj (denominator time) := point_mul_denominator time
    _ = -denominator time + 2 := by
      apply Basic.ext
      · change 1 = -1 + 2
        decide +kernel
      · change -(-time) = -(-time) + 0
        ring1
    _ = (-1 + 2 / denominator time) * denominator time := by
      rewrite [_root_.add_mul, ExplicitField.div_mul_cancel _ (denominator_ne_zero time)]
      ring1

/-- The exact tangent of the original rational circle chart. -/
@[expose] def velocity (time : Fraction.Rational) : Canonical :=
  (⟨0, 2⟩ : Canonical) / denominator time ^ 2

/-- The original point's purely imaginary logarithmic velocity. -/
@[expose] def logarithmicVelocity (time : Fraction.Rational) : Canonical :=
  (⟨0, 2⟩ : Canonical) / unitCircleDenominator time

/-- Clearing the original real denominator recovers the same logarithmic-velocity numerator. -/
theorem logarithmicVelocity_mul_denominator (time : Fraction.Rational) :
    logarithmicVelocity time * unitCircleDenominator time = (⟨0, 2⟩ : Canonical) := by
  have nonzero : unitCircleDenominator time ≠ 0 := by
    rewrite [← denominator_product]
    exact Field.mul_ne_zero_direct (conjugate_ne_zero time) (denominator_ne_zero time)
  exact ExplicitField.div_mul_cancel _ nonzero

/-- The original logarithmic velocity is purely imaginary at every rational chart parameter. -/
theorem logarithmicVelocity_real (time : Fraction.Rational) : (logarithmicVelocity time).re = 0 := by
  have scalarLower : (1 : Fraction.Rational) ≤ time ^ 2 + 1 := by
    calc
      1 = 0 + 1 := by ring1
      _ ≤ _ := Arithmetic.add_le_add_direct (Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Basic.le_refl _)
  have nonzero : time ^ 2 + 1 ≠ 0 :=
    ((by decide +kernel : (0 : Fraction.Rational) < 1).trans_le scalarLower).ne'
  have real := congrArg (fun value : Canonical => value.re) (logarithmicVelocity_mul_denominator time)
  change (logarithmicVelocity time).re * (time ^ 2 + 1) - (logarithmicVelocity time).im * 0 = 0 at real
  apply Fraction.Field.mul_right_cancel_of_ne nonzero
  calc
    _ = (logarithmicVelocity time).re * (time ^ 2 + 1) - (logarithmicVelocity time).im * 0 := by ring1
    _ = 0 := real
    _ = _ := by ring1

/-- The logarithmic velocity is the imaginary unit times one plus the original point's embedded real component. -/
theorem logarithmicVelocity_eq_projection (time : Fraction.Rational) :
    logarithmicVelocity time =
      Constants.imaginaryUnit * (1 + Components.Projection.realPart (unitQuarterPoint time)) := by
  have nonzero : unitCircleDenominator time ≠ 0 := by
    rewrite [← denominator_product]
    exact Field.mul_ne_zero_direct (conjugate_ne_zero time) (denominator_ne_zero time)
  have pointCleared := congrArg (fun value : Canonical => value.re) (unitQuarterPoint_mul_denominator time)
  change (unitQuarterPoint time).re * (time ^ 2 + 1) - (unitQuarterPoint time).im * 0 =
    1 - time ^ 2 at pointCleared
  have realCleared : (unitQuarterPoint time).re * (time ^ 2 + 1) = 1 - time ^ 2 := by
    calc
      _ = (unitQuarterPoint time).re * (time ^ 2 + 1) - (unitQuarterPoint time).im * 0 := by ring1
      _ = _ := pointCleared
  apply ExplicitField.eq_of_mul_eq_mul_right nonzero
  rewrite [logarithmicVelocity_mul_denominator]
  apply Basic.ext
  · simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im,
      Components.Projection.realPart, Components.Basic.point, Constants.imaginaryUnit, unitCircleDenominator]
    ring1
  · simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im,
      Components.Projection.realPart, Components.Basic.point, Constants.imaginaryUnit, unitCircleDenominator]
    calc
      _ = (time ^ 2 + 1) + (unitQuarterPoint time).re * (time ^ 2 + 1) := by
        rewrite [realCleared]
        ring1
      _ = _ := by ring1

/-- The original logarithmic velocity's imaginary reading is one plus the same chart point's real reading. -/
theorem logarithmicVelocity_im (time : Fraction.Rational) :
    (logarithmicVelocity time).im = 1 + (unitQuarterPoint time).re := by
  have reading := congrArg Basic.im (logarithmicVelocity_eq_projection time)
  change (logarithmicVelocity time).im = 0 * (0 + 0) + 1 * (1 + (unitQuarterPoint time).re) at reading
  rewrite [Fraction.Field.zero_mul_direct, Fraction.Field.one_mul, Fraction.Field.zero_add] at reading
  exact reading

/-- The same original rational quarter integrand has imaginary reading at least one throughout its closed interval.

The unit parameter bounds force the original circle point's real coordinate
nonnegative. Its positive stereographic denominator and exact logarithmic
velocity readback give the lower bound, including both quarter endpoints.
-/
theorem logarithmicVelocity_im_ge_one (time : Fraction.Rational) (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    1 ≤ (logarithmicVelocity time).im := by
  have squareUpper : time ^ 2 ≤ 1 := by
    calc
      time ^ 2 = time * time := pow_two time
      _ ≤ 1 * time := Arithmetic.mul_le_mul_of_nonneg_right_direct upper nonnegative
      _ = time := Fraction.Field.one_mul time
      _ ≤ 1 := upper
  have realNonnegative : 0 ≤ (unitQuarterPoint time).re := by
    rewrite [unitQuarterPoint_re]
    exact Arithmetic.mul_nonneg_direct
      (Arithmetic.sub_nonneg_direct squareUpper)
      (Fraction.Order.Field.inv_pos_direct (unitCircleScalar_pos time)).le
  rewrite [logarithmicVelocity_im]
  calc
    (1 : Fraction.Rational) = 1 + 0 := by decide +kernel
    _ ≤ _ := Arithmetic.add_le_add_direct (show (1 : Fraction.Rational) ≤ 1 from le_rfl) realNonnegative

/-- The original logarithmic velocity has squared norm at most four for every rational chart parameter. -/
theorem logarithmicVelocity_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq (logarithmicVelocity time) ≤ 4 := by
  rewrite [logarithmicVelocity_eq_projection, Norm.Basic.normSq_mul,
    show Norm.Basic.normSq Constants.imaginaryUnit = 1 by decide +kernel, Fraction.Field.one_mul]
  calc
    _ ≤ 2 * (Norm.Basic.normSq (1 : Canonical) +
        Norm.Basic.normSq (Components.Projection.realPart (unitQuarterPoint time))) := Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (1 + 1) := by
      apply Arithmetic.mul_le_mul_of_nonneg_left_direct
      · exact Arithmetic.add_le_add_direct (by decide +kernel)
          ((Components.Projection.normSq_realPart_le _).trans_eq (unitQuarterPoint_unit time))
      · decide +kernel
    _ = _ := by decide +kernel

/-- The logarithmic velocity inherits the original chart's global squared-distance bound. -/
theorem logarithmicVelocity_distance_le (first last : Fraction.Rational) :
    Norm.Basic.normSq (logarithmicVelocity first - logarithmicVelocity last) ≤ 4 * (first - last) ^ 2 := by
  have difference : logarithmicVelocity first - logarithmicVelocity last =
      Constants.imaginaryUnit * Components.Projection.realPart (unitQuarterPoint first - unitQuarterPoint last) := by
    rewrite [logarithmicVelocity_eq_projection, logarithmicVelocity_eq_projection, Components.Projection.realPart_sub]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul,
    show Norm.Basic.normSq Constants.imaginaryUnit = 1 by decide +kernel, Fraction.Field.one_mul]
  exact (Components.Projection.normSq_realPart_le _).trans (unitQuarterPoint_distance_le first last)

/-- Clearing the displayed tangent denominator recovers its same fixed Gaussian numerator. -/
theorem velocity_mul_denominator (time : Fraction.Rational) :
    velocity time * denominator time ^ 2 = (⟨0, 2⟩ : Canonical) :=
  ExplicitField.div_mul_cancel _ (Power.pow_ne_zero_direct _ (denominator_ne_zero time) _)

/-- The original tangent is the original chart point times its same logarithmic velocity. -/
theorem velocity_eq_point_mul (time : Fraction.Rational) :
    velocity time = unitQuarterPoint time * logarithmicVelocity time := by
  have realNonzero : unitCircleDenominator time ≠ 0 := by
    rewrite [← denominator_product]
    exact Field.mul_ne_zero_direct (conjugate_ne_zero time) (denominator_ne_zero time)
  have logarithmicCleared : logarithmicVelocity time * unitCircleDenominator time = (⟨0, 2⟩ : Canonical) :=
    ExplicitField.div_mul_cancel _ realNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right (Power.pow_ne_zero_direct _ (denominator_ne_zero time) 2)
  calc
    velocity time * denominator time ^ 2 = (⟨0, 2⟩ : Canonical) := velocity_mul_denominator time
    _ = logarithmicVelocity time * (Basic.conj (denominator time) * denominator time) := by
      rewrite [denominator_product, logarithmicCleared]
      rfl
    _ = (unitQuarterPoint time * logarithmicVelocity time) * denominator time ^ 2 := by
      rewrite [pow_two]
      calc
        _ = logarithmicVelocity time * (unitQuarterPoint time * denominator time) * denominator time := by
          rewrite [point_mul_denominator]
          ring1
        _ = _ := by ring1

/-- The original logarithmic tangent is the actual original velocity divided by its nonzero original chart point. -/
theorem logarithmicVelocity_eq_quotient (time : Fraction.Rational) :
    logarithmicVelocity time = velocity time / unitQuarterPoint time := by
  have nonzero : unitQuarterPoint time ≠ 0 := by
    intro zero
    have unit := unitQuarterPoint_unit time
    rw [zero, Norm.Basic.normSq_zero] at unit
    exact (by decide +kernel : (0 : Fraction.Rational) ≠ 1) unit
  apply ExplicitField.eq_of_mul_eq_mul_right nonzero
  rw [ExplicitField.div_mul_cancel _ nonzero, velocity_eq_point_mul]
  exact Basic.mul_comm _ _

/-- The exact finite tangent remainder after clearing its two original parameter denominators. -/
theorem remainder_cleared (time delta : Fraction.Rational) :
    (unitQuarterPoint (time + delta) - unitQuarterPoint time - increment delta * velocity time) *
        (denominator (time + delta) * denominator time ^ 2) = (-2 : Canonical) * increment delta ^ 2 := by
  have shifted : denominator (time + delta) = denominator time - Constants.imaginaryUnit * increment delta := by
    apply Basic.ext
    · change 1 = 1 - (0 * delta - 1 * 0)
      ring1
    · change -(time + delta) = -time - (0 * 0 + 1 * delta)
      ring1
  have first : unitQuarterPoint (time + delta) * denominator (time + delta) = 2 - denominator (time + delta) := by
    rewrite [point_reciprocal, _root_.add_mul, ExplicitField.div_mul_cancel _ (denominator_ne_zero _)]
    ring1
  have second : unitQuarterPoint time * denominator time = 2 - denominator time := by
    rewrite [point_reciprocal, _root_.add_mul, ExplicitField.div_mul_cancel _ (denominator_ne_zero _)]
    ring1
  calc
    _ = ((unitQuarterPoint (time + delta) * denominator (time + delta)) * denominator time -
        (unitQuarterPoint time * denominator time) * denominator (time + delta)) * denominator time -
        increment delta * (velocity time * denominator time ^ 2) * denominator (time + delta) := by ring1
    _ = ((2 - denominator (time + delta)) * denominator time -
        (2 - denominator time) * denominator (time + delta)) * denominator time -
        increment delta * (⟨0, 2⟩ : Canonical) * denominator (time + delta) := by
      rewrite [first, second, velocity_mul_denominator]
      rfl
    _ = _ := by
      rewrite [shifted]
      have twoReal : (2 : Canonical).re = 2 := by decide +kernel
      have twoImaginary : (2 : Canonical).im = 0 := by decide +kernel
      apply Basic.ext
      · simp only [denominator, increment, Constants.imaginaryUnit, Basic.mul_re, Basic.mul_im,
          Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im, pow_two, twoReal, twoImaginary]
        ring1
      · simp only [denominator, increment, Constants.imaginaryUnit, Basic.mul_re, Basic.mul_im,
          Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im, pow_two, twoReal, twoImaginary]
        ring1

/-- The same original denominator's squared norm is at least one at every rational parameter. -/
theorem denominator_normSq_lower (time : Fraction.Rational) :
    (1 : Fraction.Rational) ≤ Norm.Basic.normSq (denominator time) := by
  change (1 : Fraction.Rational) ≤ 1 ^ 2 + (-time) ^ 2
  calc
    1 = 1 ^ 2 + 0 := by ring1
    _ ≤ _ := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
      (Arithmetic.sq_nonneg_direct _)

/-- Every original finite chart increment has a squared tangent remainder at most four times its fourth power. -/
theorem remainder_normSq_le (time delta : Fraction.Rational) :
    Norm.Basic.normSq (unitQuarterPoint (time + delta) - unitQuarterPoint time - increment delta * velocity time) ≤
      4 * delta ^ 4 := by
  let remainder := unitQuarterPoint (time + delta) - unitQuarterPoint time - increment delta * velocity time
  let divisor := denominator (time + delta) * denominator time ^ 2
  have norms := congrArg Norm.Basic.normSq (remainder_cleared time delta)
  have product : Norm.Basic.normSq remainder * Norm.Basic.normSq divisor = 4 * delta ^ 4 := by
    calc
      _ = Norm.Basic.normSq (remainder * divisor) := (Norm.Basic.normSq_mul _ _).symm
      _ = Norm.Basic.normSq ((-2 : Canonical) * increment delta ^ 2) := norms
      _ = 4 * (delta ^ 2) ^ 2 := by
        rewrite [Norm.Basic.normSq_mul,
          show Norm.Basic.normSq (-2 : Canonical) = 4 by decide +kernel, Power.normSq_pow, increment_normSq]
        rfl
      _ = _ := by ring1
  have oneLeDivisor : (1 : Fraction.Rational) ≤ Norm.Basic.normSq divisor := by
    unfold divisor
    rewrite [Norm.Basic.normSq_mul, Power.normSq_pow]
    have lastLower := denominator_normSq_lower (time + delta)
    have firstLower := Arithmetic.pow_le_pow_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
      (denominator_normSq_lower time) 2
    rewrite [one_pow] at firstLower
    exact (show (1 : Fraction.Rational) = 1 * 1 by ring1).trans_le
      (Arithmetic.mul_le_mul_direct lastLower firstLower (by decide +kernel)
        ((by decide +kernel : (0 : Fraction.Rational) ≤ 1).trans lastLower))
  calc
    _ = Norm.Basic.normSq remainder * 1 := (Fraction.Field.mul_one_direct _).symm
    _ ≤ Norm.Basic.normSq remainder * Norm.Basic.normSq divisor :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct oneLeDivisor (Norm.Basic.normSq_nonneg _)
    _ = _ := product

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
