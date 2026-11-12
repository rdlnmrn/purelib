module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Bounds
import Purelib.Data.Rat.Bounds.Square
import Purelib.Polynomial.Quadratic.Split
import Purelib.Tactic.Ring

/-! # Original normalized-ordinate movement on radial conic quarters

The ordinate ellipse interchanges the same original base ellipse's axes.
Their retained squared-axis bounds therefore pay its actual two-direction
movement. The original half-gap and ordered quarter chart retain their
identities throughout the resulting finite time estimate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational.Box.Square
open Purelib.Geometry.Rational.Box.Square.Centered (Separation)

/-- Intrinsic regularity makes the original parallel ordinate floor positive. -/
theorem parallel_ordinate_floor_positive (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site) :
    (0 : Fraction.Rational) < (9 / 16) * Norm.Basic.normSq (halfGap site parameter) :=
  Arithmetic.mul_pos_direct (by decide +kernel)
    (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))

/-- The original normalized-ordinate direction has its uniform five-quarter axis quadrance ceiling. -/
theorem ordinateDirection_normSq_le (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq (ordinateDirection scale original) ≤ (25 / 16 : Fraction.Rational) := by
  have axes := axis_squares scale positive lower upper
  change (shortAxis scale * original.value.re) ^ 2 + (longAxis scale * original.value.im) ^ 2 ≤ _
  calc
    _ = (shortAxis scale) ^ 2 * original.value.re ^ 2 +
        (longAxis scale) ^ 2 * original.value.im ^ 2 := by ring1
    _ ≤ (25 / 16) * original.value.re ^ 2 + (25 / 16) * original.value.im ^ 2 :=
      Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.1 (Arithmetic.sq_nonneg_direct _))
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.2 (Arithmetic.sq_nonneg_direct _))
    _ = (25 / 16) * Norm.Basic.normSq original.value := by change _ = (25 / 16) * (_ ^ 2 + _ ^ 2); ring1
    _ = _ := by rewrite [original.unit, Fraction.Field.mul_one_direct]; rfl

/-- The actual normalized ordinate retains its original half-gap in the same uniform axis quadrance ceiling. -/
theorem point_ordinate_normSq_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (original : UnitVertex) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq (point site parameter scale original positive).ordinate ≤
      (25 / 16) * Norm.Basic.normSq (halfGap site parameter) := by
  rewrite [point_ordinate, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (ordinateDirection_normSq_le scale original positive lower upper) (Norm.Basic.normSq_nonneg _)).trans_eq
      (Fraction.Field.mul_comm _ _)

/-- The normalized-ordinate ellipse pays its exact two-direction displacement with the same squared-axis budget. -/
theorem ordinateDirection_distance_le (scale : Fraction.Rational) (first last : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq (ordinateDirection scale first - ordinateDirection scale last) ≤
      (25 / 16) * Norm.Basic.normSq (first.value - last.value) := by
  have axes := axis_squares scale positive lower upper
  change (shortAxis scale * first.value.re - shortAxis scale * last.value.re) ^ 2 +
      (longAxis scale * first.value.im - longAxis scale * last.value.im) ^ 2 ≤
    (25 / 16) * ((first.value.re - last.value.re) ^ 2 + (first.value.im - last.value.im) ^ 2)
  calc
    _ = (shortAxis scale) ^ 2 * (first.value.re - last.value.re) ^ 2 +
        (longAxis scale) ^ 2 * (first.value.im - last.value.im) ^ 2 := by ring1
    _ ≤ (25 / 16) * (first.value.re - last.value.re) ^ 2 +
        (25 / 16) * (first.value.im - last.value.im) ^ 2 :=
      Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.1 (Arithmetic.sq_nonneg_direct _))
        (Arithmetic.mul_le_mul_of_nonneg_right_direct axes.2 (Arithmetic.sq_nonneg_direct _))
    _ = _ := by ring1

/-- The original normalized-ordinate displacement keeps its labelled half-gap and ordered unit-direction movement. -/
theorem ordinate_distance_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (first last : UnitVertex) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2) :
    Norm.Basic.normSq ((point site parameter scale first positive).ordinate -
      (point site parameter scale last positive).ordinate) ≤
      (25 / 16) * Norm.Basic.normSq (halfGap site parameter * first.value - halfGap site parameter * last.value) := by
  have difference : (point site parameter scale first positive).ordinate -
      (point site parameter scale last positive).ordinate =
      halfGap site parameter * (ordinateDirection scale first - ordinateDirection scale last) := by
    rewrite [point_ordinate, point_ordinate]
    ring1
  have originalDifference : halfGap site parameter * first.value - halfGap site parameter * last.value =
      halfGap site parameter * (first.value - last.value) := by ring1
  rewrite [difference, originalDifference, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (ordinateDirection_distance_le scale first last positive lower upper) (Norm.Basic.normSq_nonneg _)).trans_eq
      (by ring1)

/-- The original scale-two ordinate ellipse is Lipschitz in its original base ellipse with factor twenty-five ninths.

Both original half-gap factors remain in the quadrances, so no division
by the parameter or assumption of a global inverse curve is needed. The
exact three-quarter and five-quarter axes pay the scalar comparison.
-/
theorem parallel_ordinate_distance_le_base (site : Fin 2) (parameter : Canonical)
    (first last : UnitVertex) (positive : (0 : Fraction.Rational) < 2) :
    Norm.Basic.normSq ((point site parameter 2 first positive).ordinate -
      (point site parameter 2 last positive).ordinate) ≤
        (25 / 9) * Norm.Basic.normSq ((point site parameter 2 first positive).base -
          (point site parameter 2 last positive).base) := by
  have short : shortAxis 2 = (3 / 4 : Fraction.Rational) := by unfold shortAxis; decide +kernel
  have long : longAxis 2 = (5 / 4 : Fraction.Rational) := by unfold longAxis; decide +kernel
  have realCoefficient : shortAxis 2 ^ 2 ≤ (25 / 9 : Fraction.Rational) * longAxis 2 ^ 2 := by
    rewrite [short, long]
    decide +kernel
  have imaginaryCoefficient : longAxis 2 ^ 2 ≤ (25 / 9 : Fraction.Rational) * shortAxis 2 ^ 2 := by
    rewrite [short, long]
    decide +kernel
  have directions : Norm.Basic.normSq (ordinateDirection 2 first - ordinateDirection 2 last) ≤
      (25 / 9) * Norm.Basic.normSq (baseDirection 2 first.value - baseDirection 2 last.value) := by
    calc
      _ = shortAxis 2 ^ 2 * (first.value.re - last.value.re) ^ 2 +
          longAxis 2 ^ 2 * (first.value.im - last.value.im) ^ 2 := by
        change (shortAxis 2 * first.value.re - shortAxis 2 * last.value.re) ^ 2 +
          (longAxis 2 * first.value.im - longAxis 2 * last.value.im) ^ 2 = _
        ring1
      _ ≤ ((25 / 9) * longAxis 2 ^ 2) * (first.value.re - last.value.re) ^ 2 +
          ((25 / 9) * shortAxis 2 ^ 2) * (first.value.im - last.value.im) ^ 2 :=
        Arithmetic.add_le_add_direct
          (Arithmetic.mul_le_mul_of_nonneg_right_direct realCoefficient (Arithmetic.sq_nonneg_direct _))
          (Arithmetic.mul_le_mul_of_nonneg_right_direct imaginaryCoefficient (Arithmetic.sq_nonneg_direct _))
      _ = _ := by
        change _ = (25 / 9) * ((longAxis 2 * first.value.re - longAxis 2 * last.value.re) ^ 2 +
          (shortAxis 2 * first.value.im - shortAxis 2 * last.value.im) ^ 2)
        ring1
  have ordinates : (point site parameter 2 first positive).ordinate -
      (point site parameter 2 last positive).ordinate =
        halfGap site parameter * (ordinateDirection 2 first - ordinateDirection 2 last) := by
    rewrite [point_ordinate, point_ordinate]
    ring1
  have bases : (point site parameter 2 first positive).base -
      (point site parameter 2 last positive).base =
        halfGap site parameter * (baseDirection 2 first.value - baseDirection 2 last.value) := by
    rewrite [point_base, point_base]
    ring1
  rewrite [ordinates, bases, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct directions (Norm.Basic.normSq_nonneg _)).trans_eq
    (by ring1)

/-- Every original radial-quarter normalized ordinate has its finite twenty-five-quarter half-gap time budget. -/
theorem quarter_ordinate_distance_le (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter first) positive).ordinate -
      (point site parameter scale (Waist.direction quarter last) positive).ordinate) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have mapped := ordinate_distance_le site parameter scale (Waist.direction quarter first)
    (Waist.direction quarter last) positive lower upper
  have original := Waist.quarter_distance_le site parameter quarter first last
  change Norm.Basic.normSq (halfGap site parameter * (Waist.direction quarter first).value -
    halfGap site parameter * (Waist.direction quarter last).value) ≤
      4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 at original
  calc
    _ ≤ (25 / 16) * Norm.Basic.normSq (halfGap site parameter * (Waist.direction quarter first).value -
        halfGap site parameter * (Waist.direction quarter last).value) := mapped
    _ ≤ (25 / 16) * (4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct original (by decide +kernel)
    _ = _ := by
      calc
        _ = ((25 / 16) * 4) * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) := by ring1
        _ = (25 / 4) * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) :=
          congrArg (fun value => value * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2))
            (by decide +kernel : ((25 / 16) * 4 : Fraction.Rational) = 25 / 4)
        _ = _ := by ring1

/-- An actual signed cofactor reading gives a uniform norm floor for its original scale-two product reading. -/
theorem parallel_product_lower (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) {root : Canonical} (inside : (UnitRoot.box site).Contains root) :
    (9 / 64 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq (root * (point site parameter 2 (Waist.direction quarter time)
        (by decide +kernel)).ordinate) := by
  rewrite [Norm.Basic.normSq_mul]
  exact (show (9 / 64 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) =
      (1 / 4) * ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) by
        have constant : ((1 / 4) * (9 / 16) : Fraction.Rational) = 9 / 64 := by decide +kernel
        calc
          _ = ((1 / 4) * (9 / 16)) * Norm.Basic.normSq (halfGap site parameter) :=
            congrArg (fun coefficient => coefficient * Norm.Basic.normSq (halfGap site parameter)) constant.symm
          _ = _ := by ring1).trans_le
    (Arithmetic.mul_le_mul_direct (UnitRoot.box_normSq_lower site inside)
      (parallel_ordinate_lower site parameter (Waist.direction quarter time))
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
      (Norm.Basic.normSq_nonneg _))

/-- Close original chart times keep the sum of the actual full product readings away from zero.

Both cofactor readings remain in their original signed square. The same
normalized-ordinate movement budget pays the perturbation of their product
sum, so no successful cross-time root comparison is assumed.
-/
theorem parallel_product_sum_lower (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (first last : Fraction.Rational) {firstRoot lastRoot : Canonical}
    (firstInside : (UnitRoot.box site).Contains firstRoot) (lastInside : (UnitRoot.box site).Contains lastRoot)
    (paid : (first - last) ^ 2 ≤ (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational)) :
    Norm.Basic.normSq (halfGap site parameter) / 4 ≤
      Norm.Basic.normSq
        (firstRoot * (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).ordinate +
          lastRoot * (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).ordinate) := by
  let firstOrdinate := (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).ordinate
  let lastOrdinate := (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).ordinate
  let gapNorm := Norm.Basic.normSq (halfGap site parameter)
  let main := (firstRoot + lastRoot) * firstOrdinate
  let perturbation := lastRoot * (firstOrdinate - lastOrdinate)
  have mainLower : (9 / 16 : Fraction.Rational) * gapNorm ≤ Norm.Basic.normSq main := by
    rewrite [Norm.Basic.normSq_mul]
    exact (show (9 / 16 : Fraction.Rational) * gapNorm = 1 * ((9 / 16) * gapNorm) by ring1).trans_le
      (Arithmetic.mul_le_mul_direct (UnitRoot.box_sum_lower site firstInside lastInside)
        (parallel_ordinate_lower site parameter (Waist.direction quarter first))
        (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
        (Norm.Basic.normSq_nonneg _))
  have movement := quarter_ordinate_distance_le site parameter 2 quarter (by decide +kernel)
    (by decide +kernel) (by decide +kernel) first last
  have perturbationUpper : Norm.Basic.normSq perturbation ≤
      (75 / Fraction.Cast.fromInt 65536 : Fraction.Rational) * gapNorm := by
    rewrite [Norm.Basic.normSq_mul]
    have stepBound := Arithmetic.mul_le_mul_of_nonneg_left_direct paid
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 25 / 4)
        (Norm.Basic.normSq_nonneg (halfGap site parameter)))
    exact (Arithmetic.mul_le_mul_direct (UnitRoot.box_normSq_upper site lastInside)
      (movement.trans stepBound) (Norm.Basic.normSq_nonneg _)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 3)).trans_eq (by
        dsimp only [gapNorm]
        have constant : ((3 : Fraction.Rational) * ((25 / 4) * (1 / Fraction.Cast.fromInt 16384))) =
            75 / Fraction.Cast.fromInt 65536 := by decide +kernel
        calc
          _ = (3 * ((25 / 4) * (1 / Fraction.Cast.fromInt 16384))) *
              Norm.Basic.normSq (halfGap site parameter) := by ring1
          _ = _ := congrArg (fun coefficient => coefficient * Norm.Basic.normSq (halfGap site parameter)) constant)
  have lower := Norm.Bounds.half_normSq_sub_le_normSq_sub main perturbation
  have halfLower : ((9 / 16 : Fraction.Rational) * gapNorm) / 2 ≤ Norm.Basic.normSq main / 2 :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct mainLower (by decide +kernel)
  have coefficient : (1 / 4 : Fraction.Rational) ≤ (9 / 16) / 2 - 75 / Fraction.Cast.fromInt 65536 := by decide +kernel
  have base : gapNorm / 4 ≤ ((9 / 16 : Fraction.Rational) * gapNorm) / 2 -
      (75 / Fraction.Cast.fromInt 65536) * gapNorm := by
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
      (Norm.Basic.normSq_nonneg (halfGap site parameter))
    exact (show gapNorm / 4 = (1 / 4 : Fraction.Rational) * gapNorm by
      simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).trans_le
      (scaled.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))
  exact (base.trans ((Arithmetic.sub_le_sub_direct halfLower perturbationUpper).trans lower)).trans_eq
    (congrArg Norm.Basic.normSq (show main - perturbation =
      firstRoot * (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).ordinate +
        lastRoot * (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).ordinate by
          dsimp only [main, perturbation, firstOrdinate, lastOrdinate]; ring1))

/-- The same original radial-quarter squared ordinate has a uniform finite chart-time variation budget.

The original two ordinate readings retain their product factorization and
uniform axis ceilings. Their exact quarter-time displacement pays the bound.
-/
theorem quarter_ordinate_square_distance_le (site : Fin 2) (parameter : Canonical)
    (scale : Fraction.Rational) (quarter : UnitCircuitQuarter) (positive : 0 < scale)
    (lower : 1 ≤ scale) (upper : scale ≤ 2) (first last : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter scale (Waist.direction quarter first) positive).ordinate ^ 2 -
        (point site parameter scale (Waist.direction quarter last) positive).ordinate ^ 2) ≤
      (625 / 16) * Norm.Basic.normSq (halfGap site parameter) ^ 2 * (first - last) ^ 2 := by
  let firstValue := (point site parameter scale (Waist.direction quarter first) positive).ordinate
  let lastValue := (point site parameter scale (Waist.direction quarter last) positive).ordinate
  have sumUpper : Norm.Basic.normSq (firstValue + lastValue) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
    calc
      _ ≤ 2 * (Norm.Basic.normSq firstValue + Norm.Basic.normSq lastValue) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((25 / 16) * Norm.Basic.normSq (halfGap site parameter) +
          (25 / 16) * Norm.Basic.normSq (halfGap site parameter)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct
            (point_ordinate_normSq_le site parameter scale _ positive lower upper)
            (point_ordinate_normSq_le site parameter scale _ positive lower upper)) (by decide +kernel)
      _ = (2 * (25 / 16 + 25 / 16)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
      _ = _ := by rewrite [show (2 * (25 / 16 + 25 / 16) : Fraction.Rational) = 25 / 4 by decide +kernel]; rfl
  have movement := quarter_ordinate_distance_le site parameter scale quarter positive lower upper first last
  have factorization : firstValue ^ 2 - lastValue ^ 2 = (firstValue - lastValue) * (firstValue + lastValue) := by
    ring1
  have upperNonnegative : (0 : Fraction.Rational) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
      (Arithmetic.sq_nonneg_direct _)
  change Norm.Basic.normSq (firstValue ^ 2 - lastValue ^ 2) ≤ _
  rewrite [factorization, Norm.Basic.normSq_mul]
  calc
    _ ≤ ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) *
        ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) :=
      Arithmetic.mul_le_mul_direct movement sumUpper (Norm.Basic.normSq_nonneg _)
        upperNonnegative
    _ = ((25 / 4) * (25 / 4)) * Norm.Basic.normSq (halfGap site parameter) ^ 2 * (first - last) ^ 2 := by ring1
    _ = _ := by rewrite [show ((25 / 4) * (25 / 4) : Fraction.Rational) = 625 / 16 by decide +kernel]; rfl

/-- Exact scalar signed-square and spatial payments bound the same actual projection. -/
private theorem signed_square_projection (exactOrdinate chartOffset spatialOffset sample : Canonical)
    (gapNorm : Fraction.Rational) (gapNonnegative : 0 ≤ gapNorm)
    (separation : Separation exactOrdinate)
    (contained : (Centered.Affine.centeredSquare exactOrdinate separation.radius
      separation.positive.le).Contains sample)
    (cross : (exactOrdinate * Basic.conj chartOffset).re = (15 / 16 : Fraction.Rational) * gapNorm)
    (product : Norm.Basic.normSq exactOrdinate * Norm.Basic.normSq chartOffset ≤
      (289 / 256 : Fraction.Rational) * gapNorm ^ 2)
    (ordinateUpper : Norm.Basic.normSq exactOrdinate ≤ (25 / 16 : Fraction.Rational) * gapNorm)
    (spatialNorm : Norm.Basic.normSq spatialOffset ≤ (1 / 512 : Fraction.Rational) * gapNorm) :
    (1 / 64 : Fraction.Rational) * gapNorm ≤ (sample * Basic.conj (chartOffset + spatialOffset)).re := by
  have gapSquareNonnegative := Arithmetic.sq_nonneg_direct gapNorm
  have seedDistance : Norm.Basic.normSq (sample - exactOrdinate) ≤
      (1 / 2 : Fraction.Rational) * Norm.Basic.normSq exactOrdinate := by
    have actual := Centered.centeredSquare_normSq_sub_center_le _
      separation.positive.le contained
    have half := Arithmetic.mul_le_mul_of_nonneg_left_direct
      separation.radius_sq_le_normSq (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2)
    have scalar : (2 : Fraction.Rational) = (1 / 2) * 4 := by decide +kernel
    exact actual.trans ((show 2 * separation.radius ^ 2 = (1 / 2) * (4 * separation.radius ^ 2) by
      rewrite [← Fraction.Field.mul_assoc, ← scalar]
      rfl).trans_le half)
  have error : ((sample - exactOrdinate) * Basic.conj chartOffset).re ^ 2 ≤
      ((13 / 16 : Fraction.Rational) * gapNorm) ^ 2 := by
    have dot := Bounds.Square.dot_sq_le_product_sums
      (sample - exactOrdinate).re (sample - exactOrdinate).im chartOffset.re chartOffset.im
    calc
      _ = ((sample - exactOrdinate).re * chartOffset.re + (sample - exactOrdinate).im * chartOffset.im) ^ 2 := by
        simp only [Basic.mul_re, Basic.conj]
        ring1
      _ ≤ Norm.Basic.normSq (sample - exactOrdinate) * Norm.Basic.normSq chartOffset := dot
      _ ≤ ((1 / 2) * Norm.Basic.normSq exactOrdinate) * Norm.Basic.normSq chartOffset :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct seedDistance (Norm.Basic.normSq_nonneg _)
      _ = (1 / 2) * (Norm.Basic.normSq exactOrdinate * Norm.Basic.normSq chartOffset) := by ring1
      _ ≤ (1 / 2) * ((289 / 256) * gapNorm ^ 2) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide +kernel)
      _ = ((1 / 2) * (289 / 256)) * gapNorm ^ 2 := by ring1
      _ = (289 / 512) * gapNorm ^ 2 := congrArg (fun scalar => scalar * gapNorm ^ 2)
        (by decide +kernel : ((1 / 2) * (289 / 256) : Fraction.Rational) = 289 / 512)
      _ ≤ (169 / 256) * gapNorm ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide +kernel : (289 / 512 : Fraction.Rational) ≤ 169 / 256) gapSquareNonnegative
      _ = ((13 / 16 : Fraction.Rational) ^ 2) * gapNorm ^ 2 :=
        congrArg (fun scalar => scalar * gapNorm ^ 2)
          (by decide +kernel : (169 / 256 : Fraction.Rational) = (13 / 16) ^ 2)
      _ = _ := by ring1
  have signedError := Bounds.Square.signed_bounds_of_sq_le_sq
    (Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative) error
  have chartLower : (1 / 8 : Fraction.Rational) * gapNorm ≤ (sample * Basic.conj chartOffset).re := by
    calc
      _ = ((15 / 16) - (13 / 16)) * gapNorm := congrArg (fun scalar => scalar * gapNorm)
        (by decide +kernel : (1 / 8 : Fraction.Rational) = (15 / 16) - (13 / 16))
      _ = (15 / 16) * gapNorm + -((13 / 16) * gapNorm) := by ring1
      _ ≤ (15 / 16) * gapNorm + ((sample - exactOrdinate) * Basic.conj chartOffset).re :=
        Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) signedError.1
      _ = (exactOrdinate * Basic.conj chartOffset).re +
          ((sample - exactOrdinate) * Basic.conj chartOffset).re := by rewrite [cross]; rfl
      _ = _ := by
        simp only [Basic.mul_re, Basic.conj, Basic.sub_re, Basic.sub_im]
        ring1
  have sampleNorm : Norm.Basic.normSq sample ≤ (75 / 16 : Fraction.Rational) * gapNorm := by
    have triangle := Norm.Bounds.normSq_add_le_two exactOrdinate (sample - exactOrdinate)
    rewrite [show exactOrdinate + (sample - exactOrdinate) = sample by ring1] at triangle
    calc
      _ ≤ 2 * (Norm.Basic.normSq exactOrdinate + Norm.Basic.normSq (sample - exactOrdinate)) := triangle
      _ ≤ 2 * (Norm.Basic.normSq exactOrdinate + (1 / 2) * Norm.Basic.normSq exactOrdinate) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) seedDistance)
          (by decide +kernel)
      _ = (2 * (1 + (1 / 2 : Fraction.Rational))) * Norm.Basic.normSq exactOrdinate := by ring1
      _ = 3 * Norm.Basic.normSq exactOrdinate := congrArg (fun scalar => scalar * Norm.Basic.normSq exactOrdinate)
        (by decide +kernel : (2 * (1 + (1 / 2 : Fraction.Rational))) = 3)
      _ ≤ 3 * ((25 / 16) * gapNorm) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct ordinateUpper (by decide +kernel)
      _ = (3 * (25 / 16)) * gapNorm := by ring1
      _ = _ := congrArg (fun scalar => scalar * gapNorm)
        (by decide +kernel : (3 * (25 / 16) : Fraction.Rational) = 75 / 16)
  have spatialError : (sample * Basic.conj spatialOffset).re ^ 2 ≤
      ((7 / 64 : Fraction.Rational) * gapNorm) ^ 2 := by
    have dot := Bounds.Square.dot_sq_le_product_sums sample.re sample.im spatialOffset.re spatialOffset.im
    calc
      _ = (sample.re * spatialOffset.re + sample.im * spatialOffset.im) ^ 2 := by
        simp only [Basic.mul_re, Basic.conj]
        ring1
      _ ≤ Norm.Basic.normSq sample * Norm.Basic.normSq spatialOffset := dot
      _ ≤ ((75 / 16) * gapNorm) * ((1 / 512) * gapNorm) :=
        Arithmetic.mul_le_mul_direct sampleNorm spatialNorm (Norm.Basic.normSq_nonneg _)
          (Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative)
      _ = ((75 / 16) * (1 / 512)) * gapNorm ^ 2 := by ring1
      _ = (75 / 8192) * gapNorm ^ 2 := congrArg (fun scalar => scalar * gapNorm ^ 2)
        (by decide +kernel : ((75 / 16) * (1 / 512) : Fraction.Rational) = 75 / 8192)
      _ ≤ (49 / 4096) * gapNorm ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide +kernel : (75 / 8192 : Fraction.Rational) ≤ 49 / 4096) gapSquareNonnegative
      _ = ((7 / 64 : Fraction.Rational) ^ 2) * gapNorm ^ 2 :=
        congrArg (fun scalar => scalar * gapNorm ^ 2)
          (by decide +kernel : (49 / 4096 : Fraction.Rational) = (7 / 64) ^ 2)
      _ = _ := by ring1
  have spatialSigned := Bounds.Square.signed_bounds_of_sq_le_sq
    (Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative) spatialError
  calc
    _ = ((1 / 8) - (7 / 64)) * gapNorm := congrArg (fun scalar => scalar * gapNorm)
      (by decide +kernel : (1 / 64 : Fraction.Rational) = (1 / 8) - (7 / 64))
    _ = (1 / 8) * gapNorm + -((7 / 64) * gapNorm) := by ring1
    _ ≤ (sample * Basic.conj chartOffset).re + (sample * Basic.conj spatialOffset).re :=
      Arithmetic.add_le_add_direct chartLower spatialSigned.1
    _ = _ := by
      simp only [Basic.mul_re, Basic.conj, Basic.add_re, Basic.add_im]
      ring1

/-- Every retained signed-square reading has a positive projection against a nearby actual waist offset.

The original conic ordinate supplies the signed square. Its unchanged
radius equation and the exact ellipse-axis scalar product bound every
contained reading. The supplied physical displacement is the same local
factor-clearance payment; no square-root owner or branch is selected here.
-/
theorem parallel_signed_square_projection (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (separation : Separation
      (point site parameter 2 original (by decide +kernel)).ordinate)
    {sample value : Canonical}
    (contained : (Centered.Affine.centeredSquare
      (point site parameter 2 original (by decide +kernel)).ordinate separation.radius
        separation.positive.le).Contains sample)
    (displacement : Norm.Basic.normSq (value - (point site parameter 2 original (by decide +kernel)).base) ≤
      Norm.Basic.normSq (halfGap site parameter) / 512) :
    (1 / 64 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      (sample * Basic.conj (value - center site parameter)).re := by
  let exactOrdinate := (point site parameter 2 original (by decide +kernel)).ordinate
  let chartOffset := (point site parameter 2 original (by decide +kernel)).base - center site parameter
  let gapNorm := Norm.Basic.normSq (halfGap site parameter)
  have gapNonnegative : 0 ≤ gapNorm := Norm.Basic.normSq_nonneg _
  have chartOffset_eq : chartOffset = halfGap site parameter * baseDirection 2 original.value := by
    dsimp only [chartOffset]
    rewrite [point_base]
    ring1
  have cross : (exactOrdinate * Basic.conj chartOffset).re = (15 / 16 : Fraction.Rational) * gapNorm := by
    have direction := parallel_ordinate_base_re original
    calc
      _ = gapNorm * (ordinateDirection 2 original * Basic.conj (baseDirection 2 original.value)).re := by
        dsimp only [exactOrdinate, gapNorm]
        rewrite [point_ordinate, chartOffset_eq]
        change _ = (_ ^ 2 + _ ^ 2) * _
        simp only [Basic.mul_re, Basic.mul_im, Basic.conj]
        ring1
      _ = gapNorm * (15 / 16) := congrArg (fun scalar => gapNorm * scalar) direction
      _ = _ := Fraction.Field.mul_comm _ _
  have product : Norm.Basic.normSq exactOrdinate * Norm.Basic.normSq chartOffset ≤
      (289 / 256 : Fraction.Rational) * gapNorm ^ 2 := by
    dsimp only [exactOrdinate]
    rewrite [point_ordinate, chartOffset_eq, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    calc
      _ = gapNorm ^ 2 * (Norm.Basic.normSq (ordinateDirection 2 original) *
          Norm.Basic.normSq (baseDirection 2 original.value)) := by dsimp only [gapNorm]; ring1
      _ ≤ gapNorm ^ 2 * (289 / 256) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (parallel_ordinate_base_product_bound original) (Arithmetic.sq_nonneg_direct gapNorm)
      _ = _ := Fraction.Field.mul_comm _ _
  have ordinateUpper : Norm.Basic.normSq exactOrdinate ≤ (25 / 16 : Fraction.Rational) * gapNorm :=
    point_ordinate_normSq_le site parameter 2 original (by decide +kernel) (by decide +kernel) (by decide +kernel)
  let spatialOffset := value - (point site parameter 2 original (by decide +kernel)).base
  have spatialNorm : Norm.Basic.normSq spatialOffset ≤ (1 / 512 : Fraction.Rational) * gapNorm :=
    displacement.trans_eq (by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1)
  have endpoint : value - center site parameter = chartOffset + spatialOffset := by
    dsimp only [chartOffset, spatialOffset]
    ring1
  rewrite [endpoint]
  exact signed_square_projection exactOrdinate chartOffset spatialOffset sample gapNorm gapNonnegative
    separation contained cross product ordinateUpper spatialNorm

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
