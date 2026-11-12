module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
public import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Polynomial.Quadratic.Split
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Uniform original differential bounds on the regular parallel circle

The original polynomial, scale and half-gap caches also bound the regular
parallel points. The positive normalized-ordinate floor pays every remaining
inverse power. The separate cofactor floor concerns each actual
residual-certified reading. No reading is substituted for an arithmetic
process witness, and these bounds alone assert no period derivative.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds (Data)

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.Branches

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}

/-- The original regular parallel ordinate's computed floor from the retained labelled half-gap cache. -/
@[expose] def ordinateFloor (data : Data site parameter differential) : Fraction.Rational :=
  (9 / 16) * data.gapNorm

/-- Intrinsic regularity makes the computed original normalized-ordinate floor strictly positive. -/
theorem ordinateFloor_positive (data : Data site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 < ordinateFloor data := by
  unfold ordinateFloor
  rewrite [data.gapNorm_eq]
  exact Arithmetic.mul_pos_direct (by decide +kernel)
    (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))

/-- Every original parallel point pays the same retained normalized-ordinate floor. -/
theorem ordinateFloor_le (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    ordinateFloor data ≤
      normSq (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate := by
  unfold ordinateFloor
  rewrite [data.gapNorm_eq]
  exact parallel_ordinate_lower site parameter (Waist.direction quarter time)

/-- The original numerator times logarithmic chart velocity on the same retained regular parallel point. -/
@[expose] def numerator (_data : Data site parameter differential)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  differential.scale * differential.numerator.eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base *
      Stereographic.Tangent.logarithmicVelocity time

/-- The original polynomial value cache bounds the original numerator at every admitted parallel point. -/
theorem polynomial_value_le (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) :
    normSq (differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) ≤ data.polynomial.value := by
  have result := Box.normSq_eval_le_denseEvalNormBound differential.numerator
    (point_inside site parameter 2 (Waist.direction quarter time)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) bound)
  change _ ≤ (Box.denseHornerNormBounds differential.numerator (spatialBox site)).value at result
  rewrite [← data.polynomial_eq] at result
  exact result

/-- The same cached numerator magnitude bound controls the actual regular parallel chart numerator. -/
theorem numerator_normSq_le (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) : normSq (numerator data quarter time) ≤ data.numeratorBound := by
  have polynomialBound := polynomial_value_le data quarter bound time
  have scaled : normSq (differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) ≤
      data.scaleNorm * data.polynomial.value := by
    rewrite [Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct polynomialBound data.scaleNorm_nonnegative
  unfold numerator
  rewrite [Norm.Basic.normSq_mul, data.numeratorBound_eq]
  calc
    _ ≤ (data.scaleNorm * data.polynomial.value) * 4 :=
      Arithmetic.mul_le_mul_direct scaled
        (Stereographic.Tangent.logarithmicVelocity_normSq_le time) (Norm.Basic.normSq_nonneg _)
        ((Norm.Basic.normSq_nonneg _).trans scaled)
    _ = _ := by ring1

/-- The original cached numerator and half-gap bounds give a uniform full-tangent numerator ceiling. -/
@[expose] def tangentNumeratorBound (data : Data site parameter differential) :
    Fraction.Rational := data.numeratorBound * ((25 / 16) * data.gapNorm)

/-- The retained full-tangent numerator ceiling is nonnegative. -/
theorem tangentNumeratorBound_nonnegative (data : Data site parameter differential) :
    0 ≤ tangentNumeratorBound data :=
  Arithmetic.mul_nonneg_direct data.numeratorBound_nonnegative
    (Arithmetic.mul_nonneg_direct (by decide +kernel) data.gapNorm_nonnegative)

/-- The same original cached polynomial and ellipse bounds pay the full-tangent numerator at every actual quarter time.

The original logarithmic numerator bound is multiplied by the exact
normalized ordinate. Their retained caches give a time-independent ceiling;
no future root observation, chart point owner or polynomial fold is built.
-/
theorem tangentNumerator_normSq_le (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) :
    normSq ((differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) *
        Tangent.baseVelocity site parameter 2 quarter time) ≤ tangentNumeratorBound data := by
  have numeratorBound := numerator_normSq_le data quarter bound time
  have ordinateBound := point_ordinate_normSq_le site parameter 2 (Waist.direction quarter time)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rewrite [← data.gapNorm_eq] at ordinateBound
  rewrite [Tangent.baseVelocity_eq_ordinate_mul site parameter 2 quarter (by decide +kernel) time,
    show (differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) *
        ((point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate *
          Stereographic.Tangent.logarithmicVelocity time) =
      numerator data quarter time *
        (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate by
          unfold numerator
          ring1, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_direct numeratorBound ordinateBound
    (Norm.Basic.normSq_nonneg _) data.numeratorBound_nonnegative

/-- The computed squared magnitude budget for the original odd-power parallel coefficient. -/
@[expose] def magnitude (data : Data site parameter differential) : Fraction.Rational :=
  data.numeratorBound * (ordinateFloor data)⁻¹ ^ (2 * differential.denominatorPairs) *
    16 ^ differential.denominatorExponent

/-- The computed parallel coefficient budget is nonnegative on the original regular fibre. -/
theorem magnitude_nonnegative (data : Data site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 ≤ magnitude data := by
  unfold magnitude
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct data.numeratorBound_nonnegative
      (Arithmetic.pow_nonneg_direct
        (Fraction.Order.Field.inv_pos_direct (ordinateFloor_positive data regular)).le _))
    (Arithmetic.pow_nonneg_direct (by decide +kernel) _)

/-- The displayed original coefficient is the retained chart numerator times its two separately paid inverse powers. -/
theorem reading_eq (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) (root : Canonical) :
    reading site parameter quarter time differential root = numerator data quarter time *
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate⁻¹ ^
        (2 * differential.denominatorPairs) * root⁻¹ ^ differential.denominatorExponent := rfl

/-- Every actual residual-certified cofactor reading pays the original differential's uniform parallel magnitude budget.

The exact original normalized ordinate and the independently retained cofactor
reading have separate denominator payments. The bound keeps the original
numerator, scale and odd denominator exponent, including derivative forms.
-/
theorem reading_normSq_le (data : Data site parameter differential)
    (quarter : UnitCircuitQuarter) (regular : parameter ≠ criticalValue site)
    (bound : normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) {root : Canonical}
    (residual : normSq (root * root - (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)) :
    normSq (reading site parameter quarter time differential root) ≤ magnitude data := by
  have result := Norm.Reciprocal.coefficient_two_powers_normSq_le
    (coefficient := numerator data quarter time)
    (first := (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate)
    (last := root) (budget := data.numeratorBound) (firstFloor := ordinateFloor data)
    (lastFloor := (1 / 16 : Fraction.Rational))
    (numerator_normSq_le data quarter bound time) (ordinateFloor_positive data regular) (by decide +kernel)
    (ordinateFloor_le data quarter time)
    (UnitRoot.root_normSq_lower site (root := root)
      (point_inside site parameter 2 (Waist.direction quarter time)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) bound) residual)
    (2 * differential.denominatorPairs) differential.denominatorExponent
  rewrite [show (1 / 16 : Fraction.Rational)⁻¹ = 16 by decide +kernel] at result
  rewrite [reading_eq data quarter time root]
  exact result

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds
