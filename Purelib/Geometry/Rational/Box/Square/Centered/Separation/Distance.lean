module

public import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Sum
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Quantitative sums in neighboring retained signed squares

A finite displacement bounds the original coordinate maxima and computed
square radii. Candidates in both original squares then have a paid sum floor,
without identifying their readings or replacing either separation owner.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- A finite center displacement bounds the increase of its computed signed-coordinate maximum. -/
theorem coordinateMaximum_distance_le {first last : Canonical} {radius : Fraction.Rational}
    (nonnegative : 0 ≤ radius) (distance : Norm.Basic.normSq (last - first) ≤ radius ^ 2) :
    coordinateMaximum last ≤ coordinateMaximum first + radius := by
  have source := coordinate_bounds first
  have movement := Norm.Bounds.coordinate_bounds_of_normSq_le nonnegative distance
  change -radius ≤ last.re - first.re ∧ last.re - first.re ≤ radius ∧
    -radius ≤ last.im - first.im ∧ last.im - first.im ≤ radius at movement
  have realUpper : last.re ≤ coordinateMaximum first + radius := by
    calc
      _ = first.re + (last.re - first.re) := by ring1
      _ ≤ _ := Arithmetic.add_le_add_direct source.1 movement.2.1
  have realNegative := Arithmetic.neg_le_neg_direct movement.1
  rewrite [show -(-radius) = radius by ring1] at realNegative
  have negativeRealUpper : -last.re ≤ coordinateMaximum first + radius := by
    calc
      _ = -first.re + -(last.re - first.re) := by ring1
      _ ≤ _ := Arithmetic.add_le_add_direct source.2.1 realNegative
  have imaginaryUpper : last.im ≤ coordinateMaximum first + radius := by
    calc
      _ = first.im + (last.im - first.im) := by ring1
      _ ≤ _ := Arithmetic.add_le_add_direct source.2.2.1 movement.2.2.2
  have imaginaryNegative := Arithmetic.neg_le_neg_direct movement.2.2.1
  rewrite [show -(-radius) = radius by ring1] at imaginaryNegative
  have negativeImaginaryUpper : -last.im ≤ coordinateMaximum first + radius := by
    calc
      _ = -first.im + -(last.im - first.im) := by ring1
      _ ≤ _ := Arithmetic.add_le_add_direct source.2.2.2 imaginaryNegative
  exact Fraction.Order.Basic.max_le
    (Fraction.Order.Basic.max_le realUpper negativeRealUpper)
    (Fraction.Order.Basic.max_le imaginaryUpper negativeImaginaryUpper)

namespace Separation

/-- A finite center displacement bounds the increase of the two original computed square radii. -/
theorem radius_distance_le {first last : Canonical}
    (source : Separation first) (target : Separation last) {radius : Fraction.Rational}
    (nonnegative : 0 ≤ radius) (distance : Norm.Basic.normSq (last - first) ≤ radius ^ 2) :
    target.radius ≤ source.radius + radius / 2 := by
  have maximum := coordinateMaximum_distance_le nonnegative distance
  rewrite [← source.radius_eq, ← target.radius_eq] at maximum
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide +kernel)
  calc
    target.radius * 2 = 2 * target.radius := by ring1
    _ ≤ 2 * source.radius + radius := maximum
    _ = (source.radius + radius / 2) * 2 := by
      calc
        _ = source.radius * 2 + (radius / 2) * 2 := by
          rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)]
          ring1
        _ = _ := by ring1

/-- The original radius squared divided by 256 is the square of its sixteenth. -/
private theorem sixteenth_square (radius : Fraction.Rational) :
    radius ^ 2 / Fraction.Cast.fromInt 256 = (radius / 16) ^ 2 := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.mul_pow_direct]
  have coefficient : ((16 : Fraction.Rational)⁻¹) ^ 2 = (Fraction.Cast.fromInt 256)⁻¹ := by decide +kernel
  rewrite [coefficient]
  rfl

/-- Centers within one sixteenth of the source radius retain a uniform bound on the target radius. -/
theorem near_radius_le {first last : Canonical} (source : Separation first) (target : Separation last)
    (distance : Norm.Basic.normSq (last - first) ≤ source.radius ^ 2 / Fraction.Cast.fromInt 256) :
    target.radius ≤ (17 / 16) * source.radius := by
  have sixteenthNonnegative : 0 ≤ source.radius / 16 :=
    Fraction.Order.Field.div_nonneg_direct source.positive.le (by decide +kernel)
  have near := radius_distance_le source target sixteenthNonnegative
    (distance.trans_eq (sixteenth_square source.radius))
  apply near.trans
  calc
    source.radius + (source.radius / 16) / 2 =
        (1 + (16 : Fraction.Rational)⁻¹ * (2 : Fraction.Rational)⁻¹) * source.radius := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = (33 / 32) * source.radius := by
      rewrite [show (1 + (16 : Fraction.Rational)⁻¹ * (2 : Fraction.Rational)⁻¹) = 33 / 32 by decide +kernel]
      rfl
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (show (33 / 32 : Fraction.Rational) ≤ 17 / 16 by decide +kernel) source.positive.le

/-- Candidates in the nearby target's original square stay within seven halves of the source radius squared. -/
theorem near_candidate_distance_le {first last value : Canonical}
    (source : Separation first) (target : Separation last)
    (distance : Norm.Basic.normSq (last - first) ≤ source.radius ^ 2 / Fraction.Cast.fromInt 256)
    (inside : (Affine.centeredSquare last target.radius target.positive.le).Contains value) :
    Norm.Basic.normSq (value - first) ≤ (7 / 2) * source.radius ^ 2 := by
  have targetRadius := near_radius_le source target distance
  have radiusSquare := Arithmetic.pow_le_pow_direct target.positive.le targetRadius 2
  have targetDistance := centeredSquare_normSq_sub_center_le last target.positive.le inside
  have shifted : (last - first) + (value - last) = value - first := by ring1
  have triangle := Norm.Bounds.normSq_add_le_three_one_and_half (last - first) (value - last)
  rewrite [shifted] at triangle
  have coefficient : (3 / Fraction.Cast.fromInt 256 : Fraction.Rational) + 3 * (17 / 16) ^ 2 ≤ 7 / 2 := by
    decide +kernel
  calc
    _ ≤ 3 * Norm.Basic.normSq (last - first) + (3 / 2) * Norm.Basic.normSq (value - last) := triangle
    _ ≤ 3 * (source.radius ^ 2 / Fraction.Cast.fromInt 256) + (3 / 2) * (2 * target.radius ^ 2) :=
      Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct distance (by decide +kernel))
        (Arithmetic.mul_le_mul_of_nonneg_left_direct targetDistance (by decide +kernel))
    _ ≤ 3 * (source.radius ^ 2 / Fraction.Cast.fromInt 256) +
        (3 / 2) * (2 * ((17 / 16) * source.radius) ^ 2) :=
      Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare (by decide +kernel))
          (by decide +kernel))
    _ = (3 * (Fraction.Cast.fromInt 256)⁻¹ + ((3 / 2) * 2) * (17 / 16) ^ 2) * source.radius ^ 2 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct (source.radius ^ 2) (Fraction.Cast.fromInt 256)]
      ring1
    _ = ((3 / Fraction.Cast.fromInt 256) + 3 * (17 / 16) ^ 2) * source.radius ^ 2 := by
      rewrite [show ((3 / 2) * 2 : Fraction.Rational) = 3 by decide +kernel,
        ← Fraction.Field.div_eq_mul_inv_direct 3 (Fraction.Cast.fromInt 256)]
      rfl
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
      (Arithmetic.sq_nonneg_direct source.radius)

/-- Two candidates in the original nearby signed squares have a source-radius-squared sum floor.

The source's retained zero side pays the center sum. The finite displacement
and original target radius pay the remaining difference by quadrance triangles.
-/
theorem near_sum_normSq_lower {first last left right : Canonical}
    (source : Separation first) (target : Separation last)
    (distance : Norm.Basic.normSq (last - first) ≤ source.radius ^ 2 / Fraction.Cast.fromInt 256)
    (leftInside : (Affine.centeredSquare first source.radius source.positive.le).Contains left)
    (rightInside : (Affine.centeredSquare last target.radius target.positive.le).Contains right) :
    source.radius ^ 2 ≤ Norm.Basic.normSq (left + right) := by
  have leading := source.center_sum_normSq_lower leftInside
  rewrite [show first + left = left + first by ring1] at leading
  have tail := source.near_candidate_distance_le target distance rightInside
  have reversed : Norm.Basic.normSq (first - right) = Norm.Basic.normSq (right - first) := by
    rewrite [show first - right = -(right - first) by ring1, Norm.Basic.normSq_neg]
    rfl
  rewrite [← reversed] at tail
  have triangle := Norm.Bounds.normSq_add_le_two (left + right) (first - right)
  rewrite [show (left + right) + (first - right) = left + first by ring1] at triangle
  have combined : 9 * source.radius ^ 2 ≤ 2 * Norm.Basic.normSq (left + right) + 7 * source.radius ^ 2 := by
    calc
      _ ≤ Norm.Basic.normSq (left + first) := leading
      _ ≤ 2 * (Norm.Basic.normSq (left + right) + Norm.Basic.normSq (first - right)) := triangle
      _ ≤ 2 * (Norm.Basic.normSq (left + right) + (7 / 2) * source.radius ^ 2) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) tail) (by decide +kernel)
      _ = 2 * Norm.Basic.normSq (left + right) + (2 * (7 / 2)) * source.radius ^ 2 := by ring1
      _ = _ := by
        rewrite [show (2 * (7 / 2) : Fraction.Rational) = 7 by decide +kernel]
        rfl
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide +kernel)
  apply Arithmetic.le_of_add_le_add_right_direct (c := 7 * source.radius ^ 2)
  calc
    source.radius ^ 2 * 2 + 7 * source.radius ^ 2 = 9 * source.radius ^ 2 := by ring1
    _ ≤ 2 * Norm.Basic.normSq (left + right) + 7 * source.radius ^ 2 := combined
    _ = Norm.Basic.normSq (left + right) * 2 + 7 * source.radius ^ 2 := by ring1

end Separation

end Purelib.Geometry.Rational.Box.Square.Centered

end
