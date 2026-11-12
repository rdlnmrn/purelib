module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Root
import Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
import Purelib.Algebra.Field.Inverse
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Power

/-! # Scalar coefficient bounds on the same retained full-product candidates

The old curved scalar and the actual physical factor observations remain
unchanged. Every candidate of the prepared root returns to their identical
paired state. Its actual visible radius and the original full-product floor
pay reciprocal-power variation, separately from spatial variation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Segment.Reading completed time inside}
variable {sourceAccuracy unitAccuracy normalAccuracy : AccuracyRequest}
variable {differential : Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential
  (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- The actual factor scalar is the same ordinary coefficient on their literal stored full-product witness. -/
theorem queryValue_product (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) :
    queryValue differential samples = differential.scale * differential.numerator.eval (segment.pointAt time) *
      samples.product.value⁻¹ ^ differential.denominatorExponent := by
  have product := congrArg Equivalence.Observation.Reading.value samples.product_eq
  have productValue := product.trans (CertifiedSquareRoot.Sampling.ResidualObservation.productReading_value
    samples.unit samples.normal reading.values.value reading.values.value_eq)
  rewrite [productValue, Algebra.Field.Inverse.inverse_product samples.unit.reading_nonzero
    samples.normal.reading_nonzero, Power.mul_pow]
  unfold queryValue
  ring1

/-- The actual old product radius pays candidate variation through the retained positive full-ordinate floor. -/
@[expose] def candidateBound (bounds : Bounds data anchor)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) : Fraction.Rational :=
  bounds.value * Norm.Reciprocal.powerSensitivity (anchor.seed.separation.radius ^ 2 / 4)
    differential.denominatorExponent * (4 * samples.product.radius)

/-- An arbitrary full-product candidate pays its ordinary coefficient distance from the SAME old factor witnesses. -/
theorem candidate_close (bounds : Bounds data anchor)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) {candidate : Canonical}
    (possible : reading.values.value.name.process.Possible samples.product.state candidate) :
    Norm.Basic.normSq (queryValue differential samples -
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        candidate⁻¹ ^ differential.denominatorExponent) ≤ candidateBound bounds samples := by
  have close := Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq
    (reading.values.value.name.process.possible_inside samples.product.possible)
    (reading.values.value.name.process.possible_inside possible)
  rewrite [← samples.product.radius_eq] at close
  have power := Norm.Reciprocal.power_difference_le Segment.Reading.Samples.productFloor_positive
    (samples.candidate_normSq_lower samples.product.possible) (samples.candidate_normSq_lower possible)
    close differential.denominatorExponent
  have numerator := bounds.normSq_le (segment.pointAt_contains within time inside)
  rewrite [queryValue_product samples,
    show differential.scale * differential.numerator.eval (segment.pointAt time) *
        samples.product.value⁻¹ ^ differential.denominatorExponent -
        differential.scale * differential.numerator.eval (segment.pointAt time) *
          candidate⁻¹ ^ differential.denominatorExponent =
      (differential.scale * differential.numerator.eval (segment.pointAt time)) *
        (samples.product.value⁻¹ ^ differential.denominatorExponent -
          candidate⁻¹ ^ differential.denominatorExponent) by ring1,
    Norm.Basic.normSq_mul]
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct numerator power (Norm.Basic.normSq_nonneg _)
    bounds.nonnegative.1).trans_eq (by unfold candidateBound; ring1)

/-- The SAME old spatial variation and actual product radius compute the prepared-candidate coefficient budget. -/
@[expose] def preparedBound (bounds : Bounds data anchor)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy) : Fraction.Rational :=
  2 * (variationBound bounds sourceAccuracy unitAccuracy normalAccuracy
    (distance (segment := segment) (time := time)) + candidateBound bounds samples)

/-- Every candidate of the actual same-state prepared full cubic pays the old curved scalar discrepancy internally. -/
theorem prepared_close (bounds : Bounds data anchor)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)
    (samples : Segment.Reading.Samples reading unitAccuracy normalAccuracy)
    (retained : Segment.Reading.Samples.Root samples)
    {state : retained.certificate.value.name.process.State} {candidate : Canonical}
    (possible : retained.certificate.value.name.process.Possible state candidate) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference sample.reading -
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        candidate⁻¹ ^ differential.denominatorExponent) ≤ preparedBound (sourceAccuracy := sourceAccuracy)
          bounds samples :=
  (Norm.Bounds.normSq_sub_le_via _ (queryValue differential samples) _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (variation_le bounds sample samples)
        (candidate_close bounds samples (retained.candidate_at_product possible)))
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient

end
