module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Movement
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
public import Purelib.Data.Gaussian.Norm.Reciprocal.Variation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Sum
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Ordinary coefficient variation on an actual retained physical factor query

The old curved source observation and both actual affine-query factor
observations remain unchanged. The original signed seed/refinement windows
pay denominator floors and signed sum floors. Their actual square residuals
and physical displacement bound coefficient variation between different
points, without asserting any named equivalence of different radicands.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Coefficient

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}

/-- One original numerator Horner fold on the SAME sharp source square, beside the unchanged differential budget. -/
@[expose] def Bounds (_data : Waist.Differential.Bounds.Data site parameter differential)
    (anchor : Parameter.Anchor source.lift) : Type :=
  { cache : Polynomial.Bounds.Horner //
    cache = Gaussian.Bounds.Box.denseHornerNormBounds differential.numerator (sourceBox anchor) }

namespace Bounds

/-- Compute the original numerator fold once on the actual source square, without preparing or sampling any root. -/
def build (data : Waist.Differential.Bounds.Data site parameter differential)
    (anchor : Parameter.Anchor source.lift) : Bounds data anchor :=
  let cache := Gaussian.Bounds.Box.denseHornerNormBounds differential.numerator (sourceBox anchor)
  ⟨cache, rfl⟩

variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {anchor : Parameter.Anchor source.lift}

/-- Read the complete original Horner value/slope cache retained for this unchanged source square. -/
@[expose] def cache (bounds : Bounds data anchor) : Polynomial.Bounds.Horner := bounds.val

/-- The cached fold is the original numerator/box factory, not a selected final numerical bound. -/
theorem cache_eq (bounds : Bounds data anchor) : bounds.cache =
    Gaussian.Bounds.Box.denseHornerNormBounds differential.numerator (sourceBox anchor) :=
  bounds.property

/-- The unchanged original scale cache multiplies the numerator's retained squared-magnitude ceiling. -/
@[expose] def value (bounds : Bounds data anchor) : Fraction.Rational := data.scaleNorm * bounds.cache.value

/-- The same retained scale and Horner slope compute the actual numerator squared-displacement multiplier. -/
@[expose] def slope (bounds : Bounds data anchor) : Fraction.Rational := data.scaleNorm * bounds.cache.slope

/-- Both computed scaled numerator ceilings are nonnegative. -/
theorem nonnegative (bounds : Bounds data anchor) : 0 ≤ bounds.value ∧ 0 ≤ bounds.slope := by
  have known := Gaussian.Bounds.Box.denseHornerNormBounds_nonneg
    differential.numerator (sourceBox anchor)
  change 0 ≤ (Gaussian.Bounds.Box.denseHornerNormBounds
      differential.numerator (sourceBox anchor)).value ∧
    0 ≤ (Gaussian.Bounds.Box.denseHornerNormBounds
      differential.numerator (sourceBox anchor)).slope at known
  rewrite [← bounds.cache_eq] at known
  exact ⟨Arithmetic.mul_nonneg_direct data.scaleNorm_nonnegative known.1,
    Arithmetic.mul_nonneg_direct data.scaleNorm_nonnegative known.2⟩

/-- Every actual source-square point pays the cached scaled numerator magnitude. -/
theorem normSq_le (bounds : Bounds data anchor) {point : Canonical}
    (inside : (sourceBox anchor).Contains point) :
    Norm.Basic.normSq (differential.scale * differential.numerator.eval point) ≤ bounds.value := by
  have known := Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
    differential.numerator inside
  change _ ≤ (Gaussian.Bounds.Box.denseHornerNormBounds
    differential.numerator (sourceBox anchor)).value at known
  rewrite [← bounds.cache_eq] at known
  rewrite [Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct known data.scaleNorm_nonnegative

/-- Two distinct actual points in the same square pay their original scaled numerator variation. -/
theorem difference_le (bounds : Bounds data anchor) {first last : Canonical}
    (firstInside : (sourceBox anchor).Contains first) (lastInside : (sourceBox anchor).Contains last) :
    Norm.Basic.normSq (differential.scale * differential.numerator.eval first -
      differential.scale * differential.numerator.eval last) ≤ bounds.slope * Norm.Basic.normSq (first - last) := by
  have known := Gaussian.Bounds.Box.normSq_eval_sub_eval_le
    differential.numerator firstInside lastInside
  change _ ≤ (Gaussian.Bounds.Box.denseHornerNormBounds
    differential.numerator (sourceBox anchor)).slope * Norm.Basic.normSq (first - last) at known
  rewrite [← bounds.cache_eq] at known
  have factor : differential.scale * differential.numerator.eval first -
      differential.scale * differential.numerator.eval last =
      differential.scale * (differential.numerator.eval first - differential.numerator.eval last) := by ring1
  rewrite [factor, Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct known data.scaleNorm_nonnegative).trans_eq
    (by unfold slope; ring1)

end Bounds

variable {anchor : Parameter.Anchor source.lift} {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Segment.Reading completed time inside}
variable {sourceAccuracy unitAccuracy normalAccuracy : AccuracyRequest}

/-- The actual physical affine query's scalar uses its original point and unchanged two factor observations. -/
@[expose] def queryValue (differential : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) : Canonical :=
  differential.scale * differential.numerator.eval (segment.pointAt time) *
    samples.normal.reading⁻¹ ^ differential.denominatorExponent *
      samples.unit.reading⁻¹ ^ differential.denominatorExponent

/-- Actual displacement from the original curved source to this original physical affine query. -/
@[expose] def distance : Fraction.Rational :=
  Norm.Basic.normSq ((Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base -
    segment.pointAt time)

/-- The exact source ordinate and the actual normalized query reading retain their original signed sum payment. -/
@[expose] def normalMovement (anchor : Parameter.Anchor source.lift) (accuracy : AccuracyRequest)
    (displacement : Fraction.Rational) : Fraction.Rational :=
  (4 * accuracy.tolerance +
    2 * ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter) * displacement)) /
      (9 * anchor.seed.separation.radius ^ 2)

/-- Both unchanged cofactor requests and the actual distinct-point displacement pay cofactor movement. -/
@[expose] def unitMovement (sourceAccuracy targetAccuracy : AccuracyRequest)
    (displacement : Fraction.Rational) : Fraction.Rational :=
  4 * (sourceAccuracy.tolerance + targetAccuracy.tolerance) + 2 * displacement

/-- The retained source cofactor observation remains in its original labelled signed square. -/
theorem source_unit_inside
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy) :
    (UnitRoot.box site).Contains sample.reading :=
  source.signed.contains (sample.reading_in_initial_box source.lift.unitOwner source.lift.unitRoot_eq)

/-- The exact source ordinate and actual normalized query witness pay movement without sharing a radicand. -/
theorem normal_distance_le (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    Norm.Basic.normSq ((Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
      samples.normal.reading) ≤
      normalMovement anchor normalAccuracy (distance (segment := segment) (time := time)) := by
  have physical := segment.pointAt_contains within time inside
  have sourcePhysical := Clearance.point_inside_box site parameter (Waist.direction quarter reference) anchor.regular
  have sumLower := anchor.seed.separation.center_sum_normSq_lower
    (samples.normal_inside samples.normal.reading_possible)
  have exactSquare := (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).quadratic
  rewrite [← (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).coordinate_base] at exactSquare
  have sourceResidual : Norm.Basic.normSq
      ((Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate *
        (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
        Clearance.normalizedRadicand site parameter
          (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base) ≤ 0 := by
    unfold Clearance.normalizedRadicand
    rewrite [← exactSquare]
    have zero : (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate *
        (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
        (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2 = 0 := by ring1
    rewrite [zero, Norm.Basic.normSq_zero]
    exact Fraction.Order.Basic.le_refl 0
  have targetResidual := samples.normal.residual_lt samples.normal.observation.witness_possible
  have radicands := Clearance.normalized_distance_le site parameter (Waist.direction quarter reference) anchor.regular
    sourcePhysical physical
  have paid := Norm.SquareResidual.distance_le_of_sum_lower
    (Arithmetic.mul_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 9)
      (Arithmetic.pow_pos_direct anchor.seed.separation.positive 2))
    sumLower sourceResidual targetResidual.le radicands
  exact paid.trans_eq (by unfold normalMovement; rewrite [Fraction.Field.zero_add]; rfl)

/-- The two actual cofactor observations pay movement between their distinct original physical radicands. -/
theorem unit_distance_le
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    Norm.Basic.normSq (sample.reading - samples.unit.reading) ≤
      unitMovement sourceAccuracy unitAccuracy (distance (site := site) (segment := segment) (time := time)) := by
  have sourceResidual := sample.residual_lt sample.observation.witness_possible
  have targetResidual := samples.unit.residual_lt samples.unit.observation.witness_possible
  exact Norm.SquareResidual.distance_le
    (UnitRoot.box_sum_lower site (source_unit_inside sample) (samples.unit_inside samples.unit.reading_possible))
    sourceResidual.le targetResidual.le
    (Clearance.cofactor_distance site
      (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base (segment.pointAt time)).le

/-- The original normalized seed's actual squared radius is a positive denominator floor. -/
theorem normalFloor_positive (anchor : Parameter.Anchor source.lift) : 0 < anchor.seed.separation.radius ^ 2 :=
  Arithmetic.pow_pos_direct anchor.seed.separation.positive 2

/-- The exact source and actual normalized query retain the SAME original seed's denominator floor. -/
theorem normal_lower (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    anchor.seed.separation.radius ^ 2 ≤
        Norm.Basic.normSq (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate ∧
      anchor.seed.separation.radius ^ 2 ≤ Norm.Basic.normSq samples.normal.reading := by
  have centerInside := Geometry.Rational.Box.Square.Centered.centeredSquare_contains_center
    (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate
    anchor.seed.separation.radius anchor.seed.separation.positive.le
  have first := anchor.seed.separation.zero.margin_le_normSq_sub centerInside
  have last := anchor.seed.separation.zero.margin_le_normSq_sub (samples.normal_inside samples.normal.reading_possible)
  rewrite [anchor.seed.separation.zero_margin, Basic.sub_zero] at first last
  exact ⟨first, last⟩

/-- The original labelled cofactor square pays both old and query denominator floors. -/
theorem unit_lower
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq sample.reading ∧
      (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq samples.unit.reading := by
  have first := (UnitRoot.zeroSide site).margin_le_normSq_sub (source_unit_inside sample)
  have last := (UnitRoot.zeroSide site).margin_le_normSq_sub (samples.unit_inside samples.unit.reading_possible)
  rewrite [UnitRoot.zeroSide_margin, Basic.sub_zero] at first last
  exact ⟨first, last⟩

/-- The cached numerator and original inverse-power sensitivities compute the distinct-point coefficient bound. -/
@[expose] def variationBound {data : Waist.Differential.Bounds.Data site parameter differential}
    (bounds : Bounds data anchor) (sourceAccuracy unitAccuracy normalAccuracy : AccuracyRequest)
    (displacement : Fraction.Rational) : Fraction.Rational :=
  let floor := anchor.seed.separation.radius ^ 2
  let exponent := differential.denominatorExponent
  2 * (2 * ((bounds.slope * displacement) * floor⁻¹ ^ exponent +
      bounds.value * (Norm.Reciprocal.powerSensitivity floor exponent *
        normalMovement anchor normalAccuracy displacement)) * (1 / 4 : Fraction.Rational)⁻¹ ^ exponent +
    (bounds.value * floor⁻¹ ^ exponent) *
      (Norm.Reciprocal.powerSensitivity (1 / 4 : Fraction.Rational) exponent *
        unitMovement sourceAccuracy unitAccuracy displacement))

/-- The SAME old curved scalar and actual distinct-point query coefficient obey their internally derived finite payment.

The original numerator, scale, full odd exponent, old cofactor sample and
actual physical-query samples remain inputs. Each signed margin comes from
its original retained refinement, and every residual is the actual original
request. The points and radicands can differ; no NamedEquivalent or desired
coefficient discrepancy is supplied as an assumption.
-/
theorem variation_le {data : Waist.Differential.Bounds.Data site parameter differential}
    (bounds : Bounds data anchor)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference sample.reading -
      queryValue differential samples) ≤
      variationBound bounds sourceAccuracy unitAccuracy normalAccuracy
        (distance (segment := segment) (time := time)) := by
  have sourcePhysical := Clearance.point_inside_box site parameter (Waist.direction quarter reference) anchor.regular
  have physical := segment.pointAt_contains within time inside
  have numeratorClose := bounds.difference_le sourcePhysical physical
  have numeratorBound := bounds.normSq_le physical
  have normalLower := normal_lower samples
  have unitLower := unit_lower sample samples
  exact Norm.Reciprocal.coefficient_two_powers_difference_le numeratorClose numeratorBound
    (normalFloor_positive anchor) (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 4)
    normalLower.1 normalLower.2 unitLower.1 unitLower.2
    (normal_distance_le samples) (unit_distance_le sample samples)
    differential.denominatorExponent differential.denominatorExponent

end Coefficient

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
