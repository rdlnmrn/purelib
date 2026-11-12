module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation.Reading
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original radial conic deformation and its actual root trace

The fixed unit direction follows the original conic points at scales `1+t`.
Exact reciprocal differences bound its real and imaginary axis factors by
one; the resulting cofactor path has the original half-gap squared variation
budget. Its finite preparation advances the actual original root owners.

This root deformation does not supply a primitive-boundary or integral
homotopy certificate. Those must additionally compare the actual differential
channels on this same radial family, including the branch endpoints at scale
one and the regular parallel cycle at scale two.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The original reciprocal difference factors through the same two retained positive radial scales. -/
private theorem inverse_difference (first last : Fraction.Rational) (firstPositive : 0 < first)
    (lastPositive : 0 < last) :
    first⁻¹ - last⁻¹ = -(first - last) * (first⁻¹ * last⁻¹) := by
  calc
    _ = first⁻¹ * (last * last⁻¹) - last⁻¹ * (first * first⁻¹) := by
      rewrite [Fraction.Field.mul_inv_cancel last lastPositive.ne',
        Fraction.Field.mul_inv_cancel first firstPositive.ne', Fraction.Field.mul_one_direct,
        Fraction.Field.mul_one_direct]
      rfl
    _ = _ := by ring1

/-- The product of the two retained radial reciprocals lies in the unit interval. -/
private theorem reciprocal_product_bounds (first last : Fraction.Rational) (firstPositive : 0 < first)
    (lastPositive : 0 < last) (firstLower : 1 ≤ first) (lastLower : 1 ≤ last) :
    0 ≤ first⁻¹ * last⁻¹ ∧ first⁻¹ * last⁻¹ ≤ 1 := by
  have firstInverse := (Fraction.Order.Field.inv_pos_direct firstPositive).le
  have lastInverse := (Fraction.Order.Field.inv_pos_direct lastPositive).le
  have firstUpper := Fraction.Order.Field.inv_le_inv_of_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 1) firstLower
  have lastUpper := Fraction.Order.Field.inv_le_inv_of_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 1) lastLower
  rewrite [show (1 : Fraction.Rational)⁻¹ = 1 by decide +kernel] at firstUpper lastUpper
  refine ⟨Arithmetic.mul_nonneg_direct firstInverse lastInverse, ?_⟩
  calc
    _ ≤ 1 * last⁻¹ := Arithmetic.mul_le_mul_of_nonneg_right_direct firstUpper lastInverse
    _ = last⁻¹ := Fraction.Field.one_mul _
    _ ≤ 1 := lastUpper

/-- Both exact radial divided-difference axis factors lie in the unit interval. -/
private theorem difference_factors_bounds (value : Fraction.Rational) (nonnegative : 0 ≤ value) (upper : value ≤ 1) :
    (0 ≤ (1 - value) * (1 / 2) ∧ (1 - value) * (1 / 2) ≤ 1) ∧
      (0 ≤ (1 + value) * (1 / 2) ∧ (1 + value) * (1 / 2) ≤ 1) := by
  have firstUpper := Arithmetic.sub_le_sub_left_direct nonnegative 1
  rewrite [show (1 - 0 : Fraction.Rational) = 1 by decide +kernel] at firstUpper
  have secondUpper := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) upper
  have secondNonnegative := Arithmetic.add_le_add_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1) nonnegative
  rewrite [Fraction.Field.zero_add] at secondNonnegative
  refine ⟨⟨Arithmetic.mul_nonneg_direct (Arithmetic.sub_nonneg_direct upper)
      (by decide +kernel), ?_⟩,
    ⟨Arithmetic.mul_nonneg_direct secondNonnegative (by decide +kernel), ?_⟩⟩
  · exact (Arithmetic.mul_le_mul_of_nonneg_right_direct firstUpper
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2)).trans (by decide +kernel)
  · have bounded := Arithmetic.mul_le_mul_of_nonneg_right_direct secondUpper
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2)
    rewrite [show ((1 + 1) * (1 / 2) : Fraction.Rational) = 1 by decide +kernel] at bounded
    exact bounded

/-- The original ellipse-direction radial displacement has the exact scale-difference squared budget. -/
theorem baseDirection_radial_distance_le (first last : Fraction.Rational) (value : Canonical)
    (firstPositive : 0 < first) (lastPositive : 0 < last) (firstLower : 1 ≤ first) (lastLower : 1 ≤ last) :
    Norm.Basic.normSq (baseDirection first value - baseDirection last value) ≤
      (first - last) ^ 2 * Norm.Basic.normSq value := by
  let reciprocal := first⁻¹ * last⁻¹
  let realFactor := (1 - reciprocal) * (1 / 2)
  let imaginaryFactor := (1 + reciprocal) * (1 / 2)
  have reciprocalBounds := reciprocal_product_bounds first last firstPositive lastPositive firstLower lastLower
  have factors := difference_factors_bounds reciprocal reciprocalBounds.1 reciprocalBounds.2
  have realSquare : realFactor ^ 2 ≤ 1 := by
    have result := Arithmetic.pow_le_pow_direct factors.1.1 factors.1.2 2
    rewrite [show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel] at result
    exact result
  have imaginarySquare : imaginaryFactor ^ 2 ≤ 1 := by
    have result := Arithmetic.pow_le_pow_direct factors.2.1 factors.2.2 2
    rewrite [show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel] at result
    exact result
  have longDifference : longAxis first - longAxis last = (first - last) * realFactor := by
    calc
      _ = ((first - last) + (first⁻¹ - last⁻¹)) * (1 / 2) := by unfold longAxis; ring1
      _ = _ := by
        rewrite [inverse_difference first last firstPositive lastPositive]
        unfold realFactor reciprocal
        ring1
  have shortDifference : shortAxis first - shortAxis last = (first - last) * imaginaryFactor := by
    calc
      _ = ((first - last) - (first⁻¹ - last⁻¹)) * (1 / 2) := by unfold shortAxis; ring1
      _ = _ := by
        rewrite [inverse_difference first last firstPositive lastPositive]
        unfold imaginaryFactor reciprocal
        ring1
  have factored : baseDirection first value - baseDirection last value =
      Scale.scale (first - last) ⟨realFactor * value.re, imaginaryFactor * value.im⟩ := by
    apply Basic.ext
    · change longAxis first * value.re - longAxis last * value.re = (first - last) * (realFactor * value.re)
      calc
        _ = (longAxis first - longAxis last) * value.re := by ring1
        _ = _ := by rewrite [longDifference]; ring1
    · change shortAxis first * value.im - shortAxis last * value.im =
        (first - last) * (imaginaryFactor * value.im)
      calc
        _ = (shortAxis first - shortAxis last) * value.im := by ring1
        _ = _ := by rewrite [shortDifference]; ring1
  have directionBound : Norm.Basic.normSq (⟨realFactor * value.re, imaginaryFactor * value.im⟩ : Canonical) ≤
      Norm.Basic.normSq value := by
    change (realFactor * value.re) ^ 2 + (imaginaryFactor * value.im) ^ 2 ≤ value.re ^ 2 + value.im ^ 2
    calc
      _ = realFactor ^ 2 * value.re ^ 2 + imaginaryFactor ^ 2 * value.im ^ 2 := by ring1
      _ ≤ 1 * value.re ^ 2 + 1 * value.im ^ 2 := Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct realSquare
          (Arithmetic.sq_nonneg_direct value.re))
        (Arithmetic.mul_le_mul_of_nonneg_right_direct imaginarySquare
          (Arithmetic.sq_nonneg_direct value.im))
      _ = _ := by rewrite [Fraction.Field.one_mul, Fraction.Field.one_mul]; rfl
  rewrite [factored, Scale.normSq_scale]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct directionBound
    (Arithmetic.sq_nonneg_direct (first - last))

/-- The actual original radial base displacement retains the exact original half-gap variation budget. -/
theorem radial_base_distance_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (first last : Fraction.Rational) (firstPositive : 0 < first) (lastPositive : 0 < last)
    (firstLower : 1 ≤ first) (lastLower : 1 ≤ last) :
    Norm.Basic.normSq ((point site parameter first original firstPositive).base -
        (point site parameter last original lastPositive).base) ≤
      Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have difference : (point site parameter first original firstPositive).base -
      (point site parameter last original lastPositive).base =
      halfGap site parameter * (baseDirection first original.value - baseDirection last original.value) := by
    rewrite [point_base, point_base]
    ring1
  have bounded := baseDirection_radial_distance_le first last original.value
    firstPositive lastPositive firstLower lastLower
  rewrite [original.unit, Fraction.Field.mul_one_direct] at bounded
  rewrite [difference, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Norm.Basic.normSq_nonneg _)

namespace Deformation

/-- The original radial deformation scale increases exactly from one to two. -/
@[expose] def scale (time : Fraction.Rational) : Fraction.Rational := 1 + time

/-- Every retained unit-interval parameter gives an admitted original radial scale. -/
theorem scale_bounds {time : Fraction.Rational} (inside : FixedRootBoxPath.Inside time) :
    0 < scale time ∧ 1 ≤ scale time ∧ scale time ≤ 2 := by
  have lower := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) inside.1
  rewrite [show (1 + 0 : Fraction.Rational) = 1 by decide +kernel] at lower
  have upper := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) inside.2
  rewrite [show (1 + 1 : Fraction.Rational) = 2 by decide +kernel] at upper
  exact ⟨(by decide +kernel : (0 : Fraction.Rational) < 1).trans_le lower, lower, upper⟩

/-- The exact rational cofactor formula of the original radial deformation chart. -/
@[expose] def cofactor (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (time : Fraction.Rational) : Canonical :=
  (unitPolynomial site).eval
    (center site parameter + halfGap site parameter * baseDirection (scale time) original.value)

/-- Every retained path parameter reads the cofactor at the identical admitted original conic point. -/
theorem cofactor_eq (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    cofactor site parameter original time =
      (unitPolynomial site).eval (point site parameter (scale time) original (scale_bounds inside).1).base := by
  rewrite [point_base]
  rfl

/-- The exact original radial cofactor displacement has the same original half-gap variation budget. -/
theorem cofactor_distance_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (first last : Fraction.Rational) (firstInside : FixedRootBoxPath.Inside first)
    (lastInside : FixedRootBoxPath.Inside last) :
    Norm.Basic.normSq (cofactor site parameter original first - cofactor site parameter original last) ≤
      Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have difference : cofactor site parameter original first - cofactor site parameter original last =
      (point site parameter (scale first) original (scale_bounds firstInside).1).base -
        (point site parameter (scale last) original (scale_bounds lastInside).1).base := by
    rewrite [cofactor_eq site parameter original first firstInside, cofactor_eq site parameter original last lastInside]
    rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
      Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    ring1
  have bounded := radial_base_distance_le site parameter original (scale first) (scale last)
    (scale_bounds firstInside).1 (scale_bounds lastInside).1
    (scale_bounds firstInside).2.1 (scale_bounds lastInside).2.1
  rewrite [difference]
  exact Eq.mp (congrArg (fun difference => Norm.Basic.normSq
    ((point site parameter (scale first) original (scale_bounds firstInside).1).base -
      (point site parameter (scale last) original (scale_bounds lastInside).1).base) ≤
        Norm.Basic.normSq (halfGap site parameter) * difference ^ 2)
          (show scale first - scale last = first - last by unfold scale; ring1)) bounded

end Deformation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
