module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Uniform finite bounds for original waist differential coefficients

One cached polynomial fold and the original spatial cofactor clearance give
computed magnitude and variation bounds for every rational waist parameter.
The quotient estimate keeps chart movement and actual root movement separate.
Residual-certified candidates need no apartness of the cubic ordinate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches
open Purelib.Algebra.Field

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

set_option genInjectivity false in
/-- Cached magnitude and two-movement coefficient budgets for an original differential on a labelled waist.

The original site, parameter and differential remain indices. The polynomial
fold, scale and half-gap norms are computed once; all subsequent budgets are
linked to these same caches by exact equations.
-/
structure Data (site : Fin 2) (parameter : Canonical) (differential : OddPowerDifferential radicand) where
  /-- The original numerator's joint value and slope fold on the original spatial patch. -/
  polynomial : Horner
  /-- The cache is the exact original numerator fold. -/
  polynomial_eq : polynomial = Box.denseHornerNormBounds differential.numerator (spatialBox site)
  /-- The cached squared norm of the original differential scale. -/
  scaleNorm : Fraction.Rational
  /-- The scale cache belongs to the original differential. -/
  scaleNorm_eq : scaleNorm = normSq differential.scale
  /-- The cached squared norm of the original labelled half-gap. -/
  gapNorm : Fraction.Rational
  /-- The gap cache belongs to the original parameter and site. -/
  gapNorm_eq : gapNorm = normSq (halfGap site parameter)
  /-- The original cofactor's cached polynomial magnitude bound on the same spatial patch. -/
  unitBound : Fraction.Rational
  /-- The cofactor bound is the original polynomial's finite box fold. -/
  unitBound_eq : unitBound = Box.denseEvalNormBound (unitPolynomial site) (spatialBox site)
  /-- The computed squared-magnitude bound for numerator times logarithmic velocity. -/
  numeratorBound : Fraction.Rational
  /-- The numerator bound uses the same scale and polynomial value caches. -/
  numeratorBound_eq : numeratorBound = 4 * scaleNorm * polynomial.value
  /-- The computed squared-distance multiplier for numerator times logarithmic velocity. -/
  numeratorSlope : Fraction.Rational
  /-- The multiplier uses the same polynomial fold and original half-gap. -/
  numeratorSlope_eq : numeratorSlope = 8 * scaleNorm * (4 * polynomial.slope * gapNorm + polynomial.value)
  /-- The computed squared-magnitude ceiling for residual-certified cofactor candidates. -/
  rootBound : Fraction.Rational
  /-- The candidate ceiling uses the same original cofactor value bound. -/
  rootBound_eq : rootBound = 1 + 4 * unitBound
  /-- The computed coefficient multiplier for squared chart movement. -/
  parameterSlope : Fraction.Rational
  /-- The parameter contribution pays the uniform cofactor floor and cached numerator/root bounds. -/
  parameterSlope_eq : parameterSlope = 512 * numeratorSlope * rootBound
  /-- The computed coefficient multiplier for squared root movement. -/
  rootSlope : Fraction.Rational
  /-- The root contribution pays the same uniform cofactor floor. -/
  rootSlope_eq : rootSlope = 512 * numeratorBound

constructive_injectivity Data

namespace Data

open Purelib.Data.Rat.Fraction.Order

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}

/-- Compute the original polynomial fold once and derive all waist coefficient budgets from its retained caches. -/
@[expose] def build (site : Fin 2) (parameter : Canonical) (differential : OddPowerDifferential radicand) :
    Data site parameter differential :=
  let polynomial := Box.denseHornerNormBounds differential.numerator (spatialBox site)
  let scaleNorm := normSq differential.scale
  let gapNorm := normSq (halfGap site parameter)
  let unitBound := Box.denseEvalNormBound (unitPolynomial site) (spatialBox site)
  let numeratorBound := 4 * scaleNorm * polynomial.value
  let numeratorSlope := 8 * scaleNorm * (4 * polynomial.slope * gapNorm + polynomial.value)
  let rootBound := 1 + 4 * unitBound
  { polynomial, polynomial_eq := rfl
    scaleNorm, scaleNorm_eq := rfl
    gapNorm, gapNorm_eq := rfl
    unitBound, unitBound_eq := rfl
    numeratorBound, numeratorBound_eq := rfl
    numeratorSlope, numeratorSlope_eq := rfl
    rootBound, rootBound_eq := rfl
    parameterSlope := 512 * numeratorSlope * rootBound, parameterSlope_eq := rfl
    rootSlope := 512 * numeratorBound, rootSlope_eq := rfl }

/-- Both components of the retained original numerator fold are nonnegative. -/
theorem polynomial_nonnegative (data : Data site parameter differential) :
    0 ≤ data.polynomial.value ∧ 0 ≤ data.polynomial.slope := by
  rewrite [data.polynomial_eq]
  exact Box.denseHornerNormBounds_nonneg _ _

/-- The cached original scale norm is nonnegative. -/
theorem scaleNorm_nonnegative (data : Data site parameter differential) : 0 ≤ data.scaleNorm := by
  rewrite [data.scaleNorm_eq]
  exact Norm.Basic.normSq_nonneg _

/-- The cached original half-gap norm is nonnegative. -/
theorem gapNorm_nonnegative (data : Data site parameter differential) : 0 ≤ data.gapNorm := by
  rewrite [data.gapNorm_eq]
  exact Norm.Basic.normSq_nonneg _

/-- The cached original cofactor bound is nonnegative. -/
theorem unitBound_nonnegative (data : Data site parameter differential) : 0 ≤ data.unitBound := by
  rewrite [data.unitBound_eq]
  exact (Box.denseHornerNormBounds_nonneg _ _).1

/-- The cached numerator magnitude bound is nonnegative. -/
theorem numeratorBound_nonnegative (data : Data site parameter differential) : 0 ≤ data.numeratorBound := by
  rewrite [data.numeratorBound_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) data.scaleNorm_nonnegative)
    data.polynomial_nonnegative.1

/-- The cached numerator variation multiplier is nonnegative. -/
theorem numeratorSlope_nonnegative (data : Data site parameter differential) : 0 ≤ data.numeratorSlope := by
  rewrite [data.numeratorSlope_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) data.scaleNorm_nonnegative)
    ((Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel) data.polynomial_nonnegative.2)
        data.gapNorm_nonnegative) data.polynomial_nonnegative.1))

/-- The cached cofactor-candidate magnitude ceiling is nonnegative. -/
theorem rootBound_nonnegative (data : Data site parameter differential) : 0 ≤ data.rootBound := by
  rewrite [data.rootBound_eq]
  exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
    (Arithmetic.add_le_add_direct (by decide +kernel)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) data.unitBound_nonnegative))

/-- The two cached coefficient variation multipliers are nonnegative. -/
theorem slopes_nonnegative (data : Data site parameter differential) :
    0 ≤ data.parameterSlope ∧ 0 ≤ data.rootSlope := by
  rewrite [data.parameterSlope_eq, data.rootSlope_eq]
  exact ⟨Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) data.numeratorSlope_nonnegative)
      data.rootBound_nonnegative,
    Arithmetic.mul_nonneg_direct (by decide +kernel) data.numeratorBound_nonnegative⟩

variable (data : Data site parameter differential) (quarter : UnitCircuitQuarter)
variable (regular : parameter ≠ criticalValue site)
variable (bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))

/-- Evaluate the original differential numerator times the exact logarithmic chart velocity. -/
@[expose] def numerator (_data : Data site parameter differential) (time : Fraction.Rational) : Canonical :=
  differential.scale * differential.numerator.eval (point site parameter (direction quarter time) regular bound).base *
    Stereographic.Tangent.logarithmicVelocity time

/-- Divide the original chart numerator by one displayed cofactor candidate. -/
@[expose] def coefficient (time : Fraction.Rational) (root : Canonical) : Canonical :=
  data.numerator quarter regular bound time / root

/-- Every original waist numerator evaluation obeys the same retained polynomial value bound. -/
theorem polynomial_value_le (time : Fraction.Rational) :
    normSq (differential.numerator.eval (point site parameter (direction quarter time) regular bound).base) ≤
      data.polynomial.value := by
  have result := Box.normSq_eval_le_denseEvalNormBound differential.numerator
    (point_inside site parameter (direction quarter time) regular bound)
  change _ ≤ (Box.denseHornerNormBounds differential.numerator (spatialBox site)).value at result
  rewrite [← data.polynomial_eq] at result
  exact result

/-- Every original scaled numerator obeys the same cached magnitude bound before chart velocity is applied. -/
theorem scaled_polynomial_value_le (time : Fraction.Rational) :
    normSq (differential.scale *
      differential.numerator.eval (point site parameter (direction quarter time) regular bound).base) ≤
        data.scaleNorm * data.polynomial.value := by
  rewrite [Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (data.polynomial_value_le quarter regular bound time) data.scaleNorm_nonnegative

/-- The actual original chart numerator has its computed uniform squared-magnitude bound. -/
theorem numerator_normSq_le (time : Fraction.Rational) :
    normSq (data.numerator quarter regular bound time) ≤ data.numeratorBound := by
  unfold numerator
  rewrite [Norm.Basic.normSq_mul, data.numeratorBound_eq]
  calc
    _ ≤ (data.scaleNorm * data.polynomial.value) * 4 :=
      Arithmetic.mul_le_mul_direct (data.scaled_polynomial_value_le quarter regular bound time)
        (Stereographic.Tangent.logarithmicVelocity_normSq_le time) (Norm.Basic.normSq_nonneg _)
        ((Norm.Basic.normSq_nonneg _).trans (data.scaled_polynomial_value_le quarter regular bound time))
    _ = _ := by ring1

/-- Squared movement of the original chart controls the original scaled polynomial numerator. -/
theorem scaled_polynomial_distance_le (first last : Fraction.Rational) :
    normSq (differential.scale *
      differential.numerator.eval (point site parameter (direction quarter first) regular bound).base -
      differential.scale *
        differential.numerator.eval (point site parameter (direction quarter last) regular bound).base) ≤
      data.scaleNorm * (data.polynomial.slope * (4 * data.gapNorm * (first - last) ^ 2)) := by
  have polynomialBound := Box.normSq_eval_sub_eval_le differential.numerator
    (point_inside site parameter (direction quarter first) regular bound)
    (point_inside site parameter (direction quarter last) regular bound)
  change _ ≤ (Box.denseHornerNormBounds differential.numerator (spatialBox site)).slope * _ at polynomialBound
  rewrite [← data.polynomial_eq] at polynomialBound
  have pointBound := quarter_base_distance_le site parameter quarter regular bound first last
  rewrite [← data.gapNorm_eq] at pointBound
  have difference : differential.scale *
      differential.numerator.eval (point site parameter (direction quarter first) regular bound).base -
      differential.scale *
        differential.numerator.eval (point site parameter (direction quarter last) regular bound).base =
      differential.scale * (differential.numerator.eval
        (point site parameter (direction quarter first) regular bound).base - differential.numerator.eval
          (point site parameter (direction quarter last) regular bound).base) := by ring1
  rewrite [difference, Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (polynomialBound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct pointBound
      data.polynomial_nonnegative.2)) data.scaleNorm_nonnegative

/-- The actual numerator times chart velocity has its computed global squared-distance multiplier. -/
theorem numerator_distance_le (first last : Fraction.Rational) :
    normSq (data.numerator quarter regular bound first - data.numerator quarter regular bound last) ≤
      data.numeratorSlope * (first - last) ^ 2 := by
  let firstValue := differential.scale *
    differential.numerator.eval (point site parameter (direction quarter first) regular bound).base
  let lastValue := differential.scale *
    differential.numerator.eval (point site parameter (direction quarter last) regular bound).base
  let firstVelocity := Stereographic.Tangent.logarithmicVelocity first
  let lastVelocity := Stereographic.Tangent.logarithmicVelocity last
  have numeratorMovement := data.scaled_polynomial_distance_le quarter regular bound first last
  have lastMagnitude := data.scaled_polynomial_value_le quarter regular bound last
  have firstTerm : normSq ((firstValue - lastValue) * firstVelocity) ≤
      (data.scaleNorm * (data.polynomial.slope * (4 * data.gapNorm * (first - last) ^ 2))) * 4 := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct numeratorMovement
      (Stereographic.Tangent.logarithmicVelocity_normSq_le first) (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans numeratorMovement)
  have lastTerm : normSq (lastValue * (firstVelocity - lastVelocity)) ≤
      (data.scaleNorm * data.polynomial.value) * (4 * (first - last) ^ 2) := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct lastMagnitude
      (Stereographic.Tangent.logarithmicVelocity_distance_le first last) (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans lastMagnitude)
  have difference : data.numerator quarter regular bound first - data.numerator quarter regular bound last =
      (firstValue - lastValue) * firstVelocity + lastValue * (firstVelocity - lastVelocity) := by
    unfold numerator firstValue lastValue firstVelocity lastVelocity
    ring1
  rewrite [difference]
  calc
    _ ≤ 2 * (normSq ((firstValue - lastValue) * firstVelocity) +
        normSq (lastValue * (firstVelocity - lastVelocity))) := Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((data.scaleNorm * (data.polynomial.slope * (4 * data.gapNorm * (first - last) ^ 2))) * 4 +
        (data.scaleNorm * data.polynomial.value) * (4 * (first - last) ^ 2)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstTerm lastTerm) (by decide +kernel)
    _ = _ := by rewrite [data.numeratorSlope_eq]; ring1

/-- Every original residual-certified cofactor candidate obeys the same retained finite magnitude ceiling. -/
theorem root_upper (time : Fraction.Rational) {root : Canonical}
    (residual : normSq (root * root - (unitPolynomial site).eval
      (point site parameter (direction quarter time) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter time) regular bound).base)) :
    normSq root ≤ data.rootBound := by
  have unitUpper := Box.normSq_eval_le_denseEvalNormBound (unitPolynomial site)
    (point_inside site parameter (direction quarter time) regular bound)
  rewrite [← data.unitBound_eq] at unitUpper
  have targetUpper : SquareRootSheets.residualTarget ((unitPolynomial site).eval
      (point site parameter (direction quarter time) regular bound).base) ≤
      normSq ((unitPolynomial site).eval (point site parameter (direction quarter time) regular bound).base) := by
    unfold SquareRootSheets.residualTarget
    rewrite [← Norm.Basic.normSq_eq_canonical, ExplicitField.div_eq_mul_inv]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel)
      (Norm.Basic.normSq_nonneg _)).trans_eq (Fraction.Field.mul_one_direct _)
  rewrite [data.rootBound_eq]
  exact Norm.SquareResidual.normSq_le unitUpper (residual.trans targetUpper)

/-- Actual cofactor candidates give a uniform coefficient bound with separately paid chart and root movements. -/
theorem coefficient_distance_le (first last : Fraction.Rational) {firstRoot lastRoot : Canonical}
    {rootMovement : Fraction.Rational}
    (firstResidual : normSq (firstRoot * firstRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter first) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter first) regular bound).base))
    (lastResidual : normSq (lastRoot * lastRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter last) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter last) regular bound).base))
    (movement : normSq (lastRoot - firstRoot) ≤ rootMovement) :
    normSq (data.coefficient quarter regular bound first firstRoot -
      data.coefficient quarter regular bound last lastRoot) ≤
      data.parameterSlope * (first - last) ^ 2 + data.rootSlope * rootMovement := by
  have quotient := Norm.Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
    (by decide +kernel : (0 : Fraction.Rational) < 1 / 16)
    (data.numerator_distance_le quarter regular bound first last)
    (data.numerator_normSq_le quarter regular bound last)
    (data.root_upper quarter regular bound last lastResidual) movement
    (UnitRoot.root_normSq_lower site
      (point_inside site parameter (direction quarter first) regular bound) firstResidual)
    (UnitRoot.root_normSq_lower site (point_inside site parameter (direction quarter last) regular bound) lastResidual)
  apply quotient.trans_eq
  rewrite [data.parameterSlope_eq, data.rootSlope_eq]
  unfold Approximation.Rational.Budget.Quotient.quotientBound
  rewrite [ExplicitField.div_eq_mul_inv,
    show ((1 / 16 : Fraction.Rational) * (1 / 16))⁻¹ = 256 by decide +kernel]
  ring1

/-- The original chart-movement multiplier after paying the signed cofactor's radicand movement. -/
@[expose] def chartSlope (data : Data site parameter differential) : Fraction.Rational :=
  data.parameterSlope + 8 * data.rootSlope * data.gapNorm

/-- The original coefficient multiplier for the sum of two actual square-residual bounds. -/
@[expose] def residualSlope (data : Data site parameter differential) : Fraction.Rational := 4 * data.rootSlope

/-- Both derived signed-reading variation multipliers are nonnegative. -/
theorem signed_slopes_nonnegative (data : Data site parameter differential) :
    0 ≤ data.chartSlope ∧ 0 ≤ data.residualSlope := by
  exact ⟨(Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
      (Arithmetic.add_le_add_direct data.slopes_nonnegative.1
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel) data.slopes_nonnegative.2)
          data.gapNorm_nonnegative)),
    Arithmetic.mul_nonneg_direct (by decide +kernel) data.slopes_nonnegative.2⟩

/-- Two actual compatible signed readings give a coefficient estimate paid by chart movement and both square residuals.

The original signed seed box covers all rational waist parameters. Its sum
separation turns the actual radicand difference into a root difference;
neither reading is replaced by a common root or an equal finite sample.
-/
theorem signed_coefficient_distance_le (first last : Fraction.Rational) {firstRoot lastRoot : Canonical}
    {firstAccuracy lastAccuracy : Fraction.Rational}
    (firstInside : (UnitRoot.box site).Contains firstRoot) (lastInside : (UnitRoot.box site).Contains lastRoot)
    (firstResidual : normSq (firstRoot * firstRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter first) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter first) regular bound).base))
    (lastResidual : normSq (lastRoot * lastRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter last) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter last) regular bound).base))
    (firstAccurate : normSq (firstRoot * firstRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter first) regular bound).base) ≤ firstAccuracy)
    (lastAccurate : normSq (lastRoot * lastRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter last) regular bound).base) ≤ lastAccuracy) :
    normSq (data.coefficient quarter regular bound first firstRoot -
      data.coefficient quarter regular bound last lastRoot) ≤
      data.chartSlope * (first - last) ^ 2 + data.residualSlope * (firstAccuracy + lastAccuracy) := by
  have parameterMovement := cofactor_distance_le site parameter quarter regular bound last first
  rewrite [← data.gapNorm_eq, show (last - first) ^ 2 = (first - last) ^ 2 by ring1] at parameterMovement
  have movement := Norm.SquareResidual.distance_le (UnitRoot.box_sum_lower site lastInside firstInside)
    lastAccurate firstAccurate parameterMovement
  have result := data.coefficient_distance_le quarter regular bound first last firstResidual lastResidual movement
  exact result.trans_eq (by unfold chartSlope residualSlope; ring1)

end Data

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
