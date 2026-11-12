module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Exact tangents of the original rational circle curve

The same original circle through its retained base has the scaled original
stereographic tangent. Its actual tangent divided by its actual nonzero
point reads the same logarithmic circle integrand, independently of base.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Algebra.Field

/-- The original rational circle point is its retained base times the original stereographic point. -/
theorem point_eq_base_mul (base : Canonical) (time : Fraction.Rational) :
    (circle base).point time = base * Stereographic.unitQuarterPoint time := by
  rw [RationalCurve.point, circle_numeratorAt, circle_denominatorAt, Field.inv_eq,
    Stereographic.unitQuarterPoint]
  change (base * (⟨1 - time ^ 2, 2 * time⟩ : Canonical)) *
    Field.inv (⟨time ^ 2 + 1, 0⟩ : Canonical) =
      base * ((⟨1 - time ^ 2, 2 * time⟩ : Canonical) * Field.inv (⟨time ^ 2 + 1, 0⟩ : Canonical))
  exact Basic.mul_assoc _ _ _

/-- The original rational circle through a nonzero retained base avoids zero at every rational parameter. -/
theorem point_ne_zero (base : Canonical) (nonzero : base ≠ 0) (time : Fraction.Rational) :
    (circle base).point time ≠ 0 := by
  intro zero
  have baseNorm : Basic.Canonical.normSq base = 0 := by
    rw [← normSq_circle_point base time, zero]
    decide +kernel
  exact nonzero ((Basic.Canonical.normSq_eq_zero base).mp baseNorm)

/-- The original stereographic tangent scaled by the same retained original circle base. -/
@[expose] def velocity (base : Canonical) (time : Fraction.Rational) : Canonical :=
  base * Stereographic.Tangent.velocity time

/-- The original circle tangent is its actual point times the same logarithmic tangent. -/
theorem velocity_eq_point_mul (base : Canonical) (time : Fraction.Rational) :
    velocity base time = (circle base).point time * Stereographic.Tangent.logarithmicVelocity time := by
  rw [velocity, Stereographic.Tangent.velocity_eq_point_mul, point_eq_base_mul]
  exact (Basic.mul_assoc _ _ _).symm

/-- Every original circle increment has the same retained scaled fourth-order tangent-remainder ceiling. -/
theorem remainder_normSq_le (base : Canonical) (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((circle base).point (time + delta) - (circle base).point time -
      Stereographic.Tangent.increment delta * velocity base time) ≤ Norm.Basic.normSq base * (4 * delta ^ 4) := by
  rw [point_eq_base_mul, point_eq_base_mul, velocity]
  have factored : base * Stereographic.unitQuarterPoint (time + delta) - base * Stereographic.unitQuarterPoint time -
      Stereographic.Tangent.increment delta * (base * Stereographic.Tangent.velocity time) =
      base * (Stereographic.unitQuarterPoint (time + delta) - Stereographic.unitQuarterPoint time -
        Stereographic.Tangent.increment delta * Stereographic.Tangent.velocity time) := by ring1
  rw [factored, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Stereographic.Tangent.remainder_normSq_le time delta) (Norm.Basic.normSq_nonneg base)

/-- The original circle's quadrance readback also uses the explicit Gaussian norm owner. -/
theorem point_normSq (base : Canonical) (time : Fraction.Rational) :
    Norm.Basic.normSq ((circle base).point time) = Norm.Basic.normSq base := by
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
  exact normSq_circle_point base time

/-- The original circle displacement is paid by its actual base quadrance and parameter displacement. -/
theorem movement_normSq_le (base : Canonical) (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((circle base).point (time + delta) - (circle base).point time) ≤
      (4 * Norm.Basic.normSq base) * delta ^ 2 := by
  rewrite [point_eq_base_mul, point_eq_base_mul,
    show base * Stereographic.unitQuarterPoint (time + delta) - base * Stereographic.unitQuarterPoint time =
      base * (Stereographic.unitQuarterPoint (time + delta) - Stereographic.unitQuarterPoint time) by ring1,
    Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Stereographic.unitQuarterPoint_distance_le (time + delta) time) (Norm.Basic.normSq_nonneg base)).trans_eq
      (by ring1)

/-- The original tangent is bounded by four times the same retained circle-base quadrance. -/
theorem velocity_normSq_le (base : Canonical) (time : Fraction.Rational) :
    Norm.Basic.normSq (velocity base time) ≤ 4 * Norm.Basic.normSq base := by
  rewrite [velocity_eq_point_mul, Norm.Basic.normSq_mul, point_normSq]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Stereographic.Tangent.logarithmicVelocity_normSq_le time) (Norm.Basic.normSq_nonneg base)).trans_eq
      (by ring1)

/-- The actual circle velocity has a uniform finite squared-distance bound from the same retained base.

The original tangent is the product of the actual circle point and its
logarithmic velocity. Their existing pointwise magnitude and displacement
bounds pay both original product-difference terms at the same parameters.
-/
theorem velocity_distance_le (base : Canonical) (first last : Fraction.Rational) :
    Norm.Basic.normSq (velocity base first - velocity base last) ≤
      40 * Norm.Basic.normSq base * (first - last) ^ 2 := by
  have pointDistance := movement_normSq_le base last (first - last)
  rewrite [show last + (first - last) = first by ring1] at pointDistance
  have logarithmicDistance := Stereographic.Tangent.logarithmicVelocity_distance_le first last
  have logarithmicBound := Stereographic.Tangent.logarithmicVelocity_normSq_le first
  have firstProduct :=
    (Arithmetic.mul_le_mul_of_nonneg_right_direct pointDistance
      (Norm.Basic.normSq_nonneg (Stereographic.Tangent.logarithmicVelocity first))).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct logarithmicBound
        ((Norm.Basic.normSq_nonneg _).trans pointDistance))
  have secondProduct := Arithmetic.mul_le_mul_of_nonneg_left_direct logarithmicDistance
    (Norm.Basic.normSq_nonneg ((circle base).point last))
  rewrite [velocity_eq_point_mul base first, velocity_eq_point_mul base last]
  have estimate := (Norm.Bounds.normSq_mul_sub_mul_le
    ((circle base).point first) (Stereographic.Tangent.logarithmicVelocity first)
    ((circle base).point last) (Stereographic.Tangent.logarithmicVelocity last)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstProduct secondProduct) (by decide))
  rewrite [point_normSq] at estimate
  exact estimate.trans_eq (by ring1)

/-- The actual circle tangent pays the finite variation of two supplied scalar coefficient readings.

Both retained scalar values stay distinct. The original tangent magnitude
and parameter-distance estimates bound the two exact product-difference
terms without asserting any regularity or comparison of the readings.
-/
theorem integrand_distance_le (base : Canonical) (first last : Fraction.Rational)
    (firstValue lastValue : Canonical) :
    Norm.Basic.normSq (velocity base last * lastValue - velocity base first * firstValue) ≤
      2 * ((40 * Norm.Basic.normSq base * (last - first) ^ 2) * Norm.Basic.normSq lastValue +
        (4 * Norm.Basic.normSq base) * Norm.Basic.normSq (lastValue - firstValue)) := by
  have firstTerm := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (velocity_distance_le base last first) (Norm.Basic.normSq_nonneg lastValue)
  have secondTerm := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (velocity_normSq_le base first) (Norm.Basic.normSq_nonneg (lastValue - firstValue))
  exact (Norm.Bounds.normSq_mul_sub_mul_le (velocity base last) lastValue
    (velocity base first) firstValue).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide))

/-- The actual original circle tangent divided by its actual original point.

The supplied exact curve view retains the same original base and actual
coefficient tables. Evaluation consumes that supplied cache; the original
circle constructor remains the literal default.
-/
@[expose] def logarithmicVelocity (base : Canonical) (time : Fraction.Rational)
    (curve : { value : RationalCurve // value = circle base } := ⟨circle base, rfl⟩) : Canonical :=
  velocity base time / curve.val.point time

/-- A nonzero retained original base gives exactly the original logarithmic stereographic integrand. -/
theorem logarithmicVelocity_eq (base : Canonical) (nonzero : base ≠ 0) (time : Fraction.Rational)
    (curve : { value : RationalCurve // value = circle base } := ⟨circle base, rfl⟩) :
    logarithmicVelocity base time curve = Stereographic.Tangent.logarithmicVelocity time := by
  rw [logarithmicVelocity, curve.property]
  apply ExplicitField.eq_of_mul_eq_mul_right (point_ne_zero base nonzero time)
  rw [ExplicitField.div_mul_cancel _ (point_ne_zero base nonzero time),
    velocity_eq_point_mul]
  exact Basic.mul_comm _ _

end Purelib.RationalFunctions.Curve.Canonical.Circle
