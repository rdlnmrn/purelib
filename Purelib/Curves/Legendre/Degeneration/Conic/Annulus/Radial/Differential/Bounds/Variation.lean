module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
public import Purelib.Data.Gaussian.Norm.Reciprocal.Variation
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.Ring

/-! # Paid time variation of original odd-power parallel coefficients

The original numerator fold controls its movement along the retained curved
quarter. The exact normalized ordinate has its own positive floor and time
budget; actual cofactor readings have a separate floor and signed residual
payment. All inverse powers use their original finite exponents. The resulting
allowance separates chart width from the two actual square residuals.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Branches

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}

/-- The original scaled polynomial numerator at the same retained parallel-quarter point. -/
@[expose] def scaledPolynomial (_data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  differential.scale * differential.numerator.eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base

/-- The original scaled-polynomial magnitude uses the same retained scale and polynomial caches. -/
theorem scaledPolynomial_normSq_le (data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) : normSq (scaledPolynomial data quarter time) ≤
      data.scaleNorm * data.polynomial.value := by
  unfold scaledPolynomial
  rewrite [Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct (polynomial_value_le data quarter bound time)
    data.scaleNorm_nonnegative

/-- The original scaled numerator pays the actual curved base movement with its retained polynomial slope cache. -/
theorem scaledPolynomial_distance_le (data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (first last : Fraction.Rational) :
    normSq (scaledPolynomial data quarter first - scaledPolynomial data quarter last) ≤
      data.scaleNorm * (data.polynomial.slope * ((25 / 4) * data.gapNorm * (first - last) ^ 2)) := by
  have polynomialBound := Box.normSq_eval_sub_eval_le differential.numerator
    (point_inside site parameter 2 (Waist.direction quarter first)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) bound)
    (point_inside site parameter 2 (Waist.direction quarter last)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) bound)
  change _ ≤ (Box.denseHornerNormBounds differential.numerator (spatialBox site)).slope * _ at polynomialBound
  rewrite [← data.polynomial_eq] at polynomialBound
  have pointBound := quarter_base_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) first last
  rewrite [← data.gapNorm_eq] at pointBound
  have difference : scaledPolynomial data quarter first - scaledPolynomial data quarter last =
      differential.scale * (differential.numerator.eval
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base -
          differential.numerator.eval
            (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base) := by
    unfold scaledPolynomial
    ring1
  rewrite [difference, Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (polynomialBound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct pointBound data.polynomial_nonnegative.2))
    data.scaleNorm_nonnegative

/-- The computed parallel numerator slope uses the original fold and the actual twenty-five-quarter chart budget. -/
@[expose] def numeratorSlope (data : WaistBounds site parameter differential) : Fraction.Rational :=
  8 * data.scaleNorm * ((25 / 4) * data.polynomial.slope * data.gapNorm + data.polynomial.value)

/-- The computed original parallel numerator slope is nonnegative. -/
theorem numeratorSlope_nonnegative (data : WaistBounds site parameter differential) :
    0 ≤ numeratorSlope data := by
  unfold numeratorSlope
  exact Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel) data.scaleNorm_nonnegative)
    (Fraction.Order.add_nonnegative
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel) data.polynomial_nonnegative.2) data.gapNorm_nonnegative)
      data.polynomial_nonnegative.1)

/-- The exact original numerator and logarithmic velocity have their derived uniform parallel time-variation bound. -/
theorem numerator_distance_le (data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (first last : Fraction.Rational) :
    normSq (numerator data quarter first - numerator data quarter last) ≤
      numeratorSlope data * (first - last) ^ 2 := by
  have result := Norm.Product.difference_le
    (scaledPolynomial_distance_le data quarter bound first last)
    (Geometry.Gaussian.UnitCircle.Stereographic.Tangent.logarithmicVelocity_normSq_le first)
    (scaledPolynomial_normSq_le data quarter bound last)
    (Geometry.Gaussian.UnitCircle.Stereographic.Tangent.logarithmicVelocity_distance_le first last)
  change normSq (numerator data quarter first - numerator data quarter last) ≤ _ at result
  exact result.trans_eq (by unfold numeratorSlope; ring1)

/-- The computed chart contribution before paying the actual signed cofactor movement. -/
@[expose] def chartSlope (data : WaistBounds site parameter differential) : Fraction.Rational :=
  4 * (numeratorSlope data * (ordinateFloor data)⁻¹ ^ (2 * differential.denominatorPairs) +
    data.numeratorBound * Norm.Reciprocal.powerSensitivity (ordinateFloor data) (2 * differential.denominatorPairs) *
      ((25 / 4) * data.gapNorm)) * 16 ^ differential.denominatorExponent

/-- The computed actual cofactor-reading contribution with its original inverse-power sensitivity. -/
@[expose] def rootSlope (data : WaistBounds site parameter differential) : Fraction.Rational :=
  2 * (data.numeratorBound * (ordinateFloor data)⁻¹ ^ (2 * differential.denominatorPairs)) *
    Norm.Reciprocal.powerSensitivity (1 / 16) differential.denominatorExponent

/-- Both original parallel coefficient variation contributions are nonnegative on a regular fibre. -/
theorem slopes_nonnegative (data : WaistBounds site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 ≤ chartSlope data ∧ 0 ≤ rootSlope data := by
  have ordinatePositive := ordinateFloor_positive data regular
  have ordinateMagnitude := Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct ordinatePositive).le
    (2 * differential.denominatorPairs)
  have ordinateSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative ordinatePositive
    (2 * differential.denominatorPairs)
  have rootSensitivity := Norm.Reciprocal.powerSensitivity_nonnegative
    (by decide +kernel : (0 : Fraction.Rational) < 1 / 16) differential.denominatorExponent
  unfold chartSlope rootSlope
  constructor
  · exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.add_nonnegative
          (Arithmetic.mul_nonneg_direct (numeratorSlope_nonnegative data) ordinateMagnitude)
          (Arithmetic.mul_nonneg_direct
            (Arithmetic.mul_nonneg_direct data.numeratorBound_nonnegative ordinateSensitivity)
            (Arithmetic.mul_nonneg_direct (by decide +kernel) data.gapNorm_nonnegative))))
      (Arithmetic.pow_nonneg_direct (by decide +kernel) _)
  · exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.mul_nonneg_direct data.numeratorBound_nonnegative ordinateMagnitude)) rootSensitivity

/-- The exact residual admission for an actual cofactor reading at its original parallel-quarter point. -/
@[expose] def RootResidual (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) (root : Canonical) : Prop :=
  normSq (root * root - cofactor site parameter 2 quarter (by decide +kernel) time) ≤
    SquareRootSheets.residualTarget (cofactor site parameter 2 quarter (by decide +kernel) time)

/-- Original residual admission gives the same actual cofactor reading its uniform quadrance floor. -/
private theorem root_lower (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) {root : Canonical} (residual : RootResidual site parameter quarter time root) :
    (1 / 16 : Fraction.Rational) ≤ normSq root :=
  UnitRoot.root_normSq_lower site
    (point_inside site parameter 2 (Waist.direction quarter time)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) bound) residual

/-- Original parallel coefficient readings have separate chart and actual cofactor movement payments. -/
theorem reading_distance_le (data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter) (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (first last : Fraction.Rational) {firstRoot lastRoot : Canonical} {rootMovement : Fraction.Rational}
    (firstResidual : RootResidual site parameter quarter first firstRoot)
    (lastResidual : RootResidual site parameter quarter last lastRoot)
    (movement : normSq (firstRoot - lastRoot) ≤ rootMovement) :
    normSq (reading site parameter quarter first differential firstRoot -
      reading site parameter quarter last differential lastRoot) ≤
        chartSlope data * (first - last) ^ 2 + rootSlope data * rootMovement := by
  have ordinateMovement := quarter_ordinate_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) first last
  rewrite [← data.gapNorm_eq] at ordinateMovement
  have result := Norm.Reciprocal.coefficient_two_powers_difference_le
    (numerator_distance_le data quarter bound first last) (numerator_normSq_le data quarter bound last)
    (ordinateFloor_positive data regular) (by decide +kernel : (0 : Fraction.Rational) < 1 / 16)
    (ordinateFloor_le data quarter first) (ordinateFloor_le data quarter last)
    (root_lower quarter bound first firstResidual) (root_lower quarter bound last lastResidual)
    ordinateMovement movement (2 * differential.denominatorPairs) differential.denominatorExponent
  rewrite [show (1 / 16 : Fraction.Rational)⁻¹ = 16 by decide +kernel] at result
  rewrite [reading_eq data quarter first firstRoot, reading_eq data quarter last lastRoot]
  exact result.trans_eq (by unfold chartSlope rootSlope; ring1)

/-- The original chart-width contribution after paying the signed cofactor's actual radicand movement. -/
@[expose] def signedChartSlope (data : WaistBounds site parameter differential) :
    Fraction.Rational :=
  chartSlope data + 2 * rootSlope data * ((25 / 4) * data.gapNorm)

/-- The original two-residual contribution after paying the same signed cofactor sum floor. -/
@[expose] def residualSlope (data : WaistBounds site parameter differential) : Fraction.Rational :=
  4 * rootSlope data

/-- The final chart-width and residual contributions are nonnegative on the same original regular fibre. -/
theorem signed_slopes_nonnegative (data : WaistBounds site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 ≤ signedChartSlope data ∧ 0 ≤ residualSlope data := by
  have slopes := slopes_nonnegative data regular
  unfold signedChartSlope residualSlope
  constructor
  · exact Fraction.Order.add_nonnegative slopes.1
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel) slopes.2)
        (Arithmetic.mul_nonneg_direct (by decide +kernel) data.gapNorm_nonnegative))
  · exact Arithmetic.mul_nonneg_direct (by decide +kernel) slopes.2

/-- Two actual compatible cofactor readings pay the parallel coefficient difference by chart width and both residuals.

The original signed cofactor box separates their sum. Their actual square
residuals and the same curved radicand movement bound derive the root
movement internally, while the two independently retained readings persist.
-/
theorem signed_reading_distance_le (data : WaistBounds site parameter differential)
    (quarter : UnitCircuitQuarter) (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (first last : Fraction.Rational) {firstRoot lastRoot : Canonical}
    {firstAccuracy lastAccuracy : Fraction.Rational}
    (firstInside : (UnitRoot.box site).Contains firstRoot) (lastInside : (UnitRoot.box site).Contains lastRoot)
    (firstResidual : RootResidual site parameter quarter first firstRoot)
    (lastResidual : RootResidual site parameter quarter last lastRoot)
    (firstAccurate : normSq (firstRoot * firstRoot - cofactor site parameter 2 quarter (by decide +kernel) first) ≤
      firstAccuracy)
    (lastAccurate : normSq (lastRoot * lastRoot - cofactor site parameter 2 quarter (by decide +kernel) last) ≤
      lastAccuracy) :
    normSq (reading site parameter quarter first differential firstRoot -
      reading site parameter quarter last differential lastRoot) ≤
        signedChartSlope data * (first - last) ^ 2 + residualSlope data * (firstAccuracy + lastAccuracy) := by
  have parameterMovement := cofactor_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) first last
  rewrite [← data.gapNorm_eq] at parameterMovement
  have movement := Norm.SquareResidual.distance_le (UnitRoot.box_sum_lower site firstInside lastInside)
    firstAccurate lastAccurate parameterMovement
  have result := reading_distance_le data quarter regular bound first last firstResidual lastResidual movement
  exact result.trans_eq (by unfold signedChartSlope residualSlope; ring1)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds
