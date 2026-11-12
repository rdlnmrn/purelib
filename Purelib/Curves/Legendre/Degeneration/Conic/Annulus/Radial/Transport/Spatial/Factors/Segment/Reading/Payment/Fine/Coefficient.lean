module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fine
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples.Arithmetic
import Purelib.Algebra.Field.Inverse
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Sum
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Power

/-! # Fine scalar coefficient payments on the same actual primary factor states

The retained fine requests pay every candidate of the actual later primary
states. Their original signed windows select the sheet. Both actual factor
states, the old curved observation and the prepared full-product/arithmetic
caches are preserved; the original coarse request indices are unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fine

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Reading completed time inside}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {bounds : Coefficient.Bounds data anchor} {target : AccuracyRequest}
variable (fine : Fine reading bounds target) {oldAccuracy : AccuracyRequest}
variable (old : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot oldAccuracy)

/-- The exact source ordinate and every actual primary normalized candidate pay the NEW retained fine residual. -/
theorem normal_distance_le {candidate : Canonical}
    (possible : reading.values.normalRoot.value.name.process.Possible fine.selected.samples.normal.state candidate) :
    Norm.Basic.normSq ((Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
      candidate) ≤ Coefficient.normalMovement anchor fine.work
        (Coefficient.distance (segment := segment) (time := time)) := by
  have physical := segment.pointAt_contains within time inside
  have sourcePhysical := Clearance.point_inside_box site parameter (Waist.direction quarter reference) anchor.regular
  have sum := anchor.seed.separation.center_sum_normSq_lower (fine.selected.samples.normal_inside possible)
  have sourceSquare := (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).quadratic
  rewrite [← (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).coordinate_base] at sourceSquare
  have exactResidual : Norm.Basic.normSq
      ((Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate *
        (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
        Clearance.normalizedRadicand site parameter
          (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base) ≤ 0 := by
    unfold Clearance.normalizedRadicand
    rewrite [← sourceSquare]
    rewrite [show (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate *
      (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate -
      (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2 = 0 by ring1,
      Norm.Basic.normSq_zero]
    exact Fraction.Order.Basic.le_refl _
  have targetResidual := fine.normal_residual_lt (by
    rewrite [fine.selected.samples.normal.observation_eq]
    exact possible)
  have radicands := Clearance.normalized_distance_le site parameter (Waist.direction quarter reference) anchor.regular
    sourcePhysical physical
  have paid := Norm.SquareResidual.distance_le_of_sum_lower
    (Arithmetic.mul_pos_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) < 9)
      (Coefficient.normalFloor_positive anchor)) sum exactResidual targetResidual.le radicands
  exact paid.trans_eq (by unfold Coefficient.normalMovement; rewrite [Fraction.Field.zero_add]; rfl)

/-- The unchanged old cofactor and actual primary query candidate pay both OLD and NEW actual residual requests. -/
theorem unit_distance_le {candidate : Canonical}
    (possible : reading.values.unitRoot.value.name.process.Possible fine.selected.samples.unit.state candidate) :
    Norm.Basic.normSq (old.reading - candidate) ≤ Coefficient.unitMovement oldAccuracy fine.work
      (Coefficient.distance (segment := segment) (time := time)) := by
  have targetResidual := fine.unit_residual_lt (by
    rewrite [fine.selected.samples.unit.observation_eq]
    exact possible)
  exact Norm.SquareResidual.distance_le
    (UnitRoot.box_sum_lower site (Coefficient.source_unit_inside old) (fine.selected.samples.unit_inside possible))
    old.reading_residual_lt.le targetResidual.le
    (Clearance.cofactor_distance site
      (Parameter.sourcePoint site parameter (Waist.direction quarter reference)).base (segment.pointAt time)).le

/-- Every candidate in the SAME actual full-product state obeys the fine distinct-point coefficient bound. -/
theorem candidate_coefficient_le {candidate : Canonical}
    (possible : reading.values.value.name.process.Possible fine.selected.samples.product.state candidate) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference old.reading -
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        candidate⁻¹ ^ differential.denominatorExponent) ≤
      Coefficient.variationBound bounds oldAccuracy fine.work fine.work
        (Coefficient.distance (segment := segment) (time := time)) := by
  have paired := possible
  rewrite [fine.selected.samples.product_eq,
    CertifiedSquareRoot.Sampling.ResidualObservation.productReading_state] at paired
  rcases fine.selected.samples.unit.product_components fine.selected.samples.normal reading.values.value
      reading.values.value_eq paired with ⟨unit, normal, unitPossible, normalPossible, equality⟩
  have normalLower := anchor.seed.separation.zero.margin_le_normSq_sub
    (fine.selected.samples.normal_inside normalPossible)
  rewrite [anchor.seed.separation.zero_margin, Basic.sub_zero] at normalLower
  have unitLower := (UnitRoot.zeroSide site).margin_le_normSq_sub
    (fine.selected.samples.unit_inside unitPossible)
  rewrite [UnitRoot.zeroSide_margin, Basic.sub_zero] at unitLower
  have normalNonzero : normal ≠ 0 := by
    intro zero
    rewrite [zero, Norm.Basic.normSq_zero] at normalLower
    exact (not_le_of_gt (Coefficient.normalFloor_positive anchor)) normalLower
  have unitNonzero : unit ≠ 0 := by
    intro zero
    rewrite [zero, Norm.Basic.normSq_zero] at unitLower
    exact (not_le_of_gt (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 4)) unitLower
  have sourcePhysical := Clearance.point_inside_box site parameter (Waist.direction quarter reference) anchor.regular
  have physical := segment.pointAt_contains within time inside
  have numerator := bounds.difference_le sourcePhysical physical
  have magnitude := bounds.normSq_le physical
  have paid := Norm.Reciprocal.coefficient_two_powers_difference_le numerator magnitude
    (Coefficient.normalFloor_positive anchor) (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 4)
    (Coefficient.normal_lower fine.selected.samples).1 normalLower
    (Coefficient.unit_lower old fine.selected.samples).1 unitLower
    (fine.normal_distance_le normalPossible) (fine.unit_distance_le old unitPossible)
    differential.denominatorExponent differential.denominatorExponent
  have scalar : differential.scale * differential.numerator.eval (segment.pointAt time) *
      candidate⁻¹ ^ differential.denominatorExponent =
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        normal⁻¹ ^ differential.denominatorExponent * unit⁻¹ ^ differential.denominatorExponent := by
    rewrite [equality, Algebra.Field.Inverse.inverse_product unitNonzero normalNonzero, Power.mul_pow]
    ring1
  rewrite [scalar]
  exact paid

variable (root : Samples.Root fine.selected.samples)

/-- Every prepared full-cubic candidate returns to the SAME newly fine-paid primary product state. -/
theorem prepared_coefficient_le {state : root.certificate.value.name.process.State} {candidate : Canonical}
    (possible : root.certificate.value.name.process.Possible state candidate) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference old.reading -
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        candidate⁻¹ ^ differential.denominatorExponent) ≤
      Coefficient.variationBound bounds oldAccuracy fine.work fine.work
        (Coefficient.distance (segment := segment) (time := time)) :=
  fine.candidate_coefficient_le old (root.candidate_at_product possible)

/-- Actual displacement pays the fine coefficient bound while preserving the OLD source request separately. -/
theorem prepared_coefficient_le_work {state : root.certificate.value.name.process.State} {candidate : Canonical}
    (possible : root.certificate.value.name.process.Possible state candidate)
    (physicalPaid : Coefficient.distance (segment := segment) (time := time) ≤ fine.work.tolerance) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference old.reading -
      differential.scale * differential.numerator.eval (segment.pointAt time) *
        candidate⁻¹ ^ differential.denominatorExponent) ≤
      Coefficient.Allocation.sourceCoefficient bounds * oldAccuracy.tolerance +
        (Coefficient.Allocation.sourceCoefficient bounds + Coefficient.Allocation.normalCoefficient bounds +
          Coefficient.Allocation.spatialCoefficient bounds) * fine.work.tolerance := by
  have variation := fine.prepared_coefficient_le old root possible
  rewrite [Coefficient.Allocation.variation_eq] at variation
  have movement := Arithmetic.mul_le_mul_of_nonneg_left_direct physicalPaid
    (Coefficient.Allocation.coefficients_nonnegative bounds).2.2
  exact variation.trans ((Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl _) movement).trans_eq (by ring1))

/-- A scalar four-term payment identity keeps coefficient normalization independent of all retained cache terms. -/
private theorem payment_identity (old moving arithmetic work : Fraction.Rational) :
    2 * (2 * (old + moving * work + arithmetic * work) + (7 / 2 : Fraction.Rational) * work) =
      4 * old + (4 * moving + 4 * arithmetic + 7) * work := by
  calc
    _ = 4 * old + (4 * moving + 4 * arithmetic) * work + (2 * (7 / 2 : Fraction.Rational)) * work := by
      ring1
    _ = _ := by
      rewrite [show (2 : Fraction.Rational) * (7 / 2) = 7 by decide +kernel]
      ring1

variable {frame : Paths.Frame parameter} {liftedStart liftedFinish : LiftedPoint 2}
variable {lifted : LiftedCell liftedStart liftedFinish} {cell : CellModel} {fraction : Fraction.Rational}
variable (uniform : UniformObservation (Fibre.frameCurve frame) differential lifted cell fraction)
variable (arithmetic : Samples.Arithmetic root differential fine.work)

/-- The actual polynomial query pays a chosen free target plus the unchanged OLD source-observation cost.

Both actual candidate costs and the new arithmetic error are derived from
the stored fine comparisons. The original model allowance must be paid at
its actual source stage, and the physical displacement must fit its actual
width certificate; neither old quantity is relabelled as a smaller request.
-/
theorem polynomial_error_le
    (compared : UniformObservation.ArithmeticComparison uniform arithmetic.numeric.original arithmetic.identity)
    (physicalPaid : Coefficient.distance (segment := segment) (time := time) ≤ fine.work.tolerance)
    (allowancePaid : cell.localAllowance ≤ fine.work.tolerance) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference old.reading -
      Polynomial.Ascending.Gaussian.Evaluation.eval cell.polynomial ⟨fraction, 0⟩) ≤
        4 * (Coefficient.Allocation.sourceCoefficient bounds * oldAccuracy.tolerance) + target.tolerance := by
  have spatial := fine.prepared_coefficient_le_work old root arithmetic.rootSample.reading_possible physicalPaid
  have factor := Observation.Cache.errorBound_le_factor differential (segment.pointAt time)
    root.certificate arithmetic.rootSample (Samples.productFloor_positive (anchor := anchor))
  have ceiling := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Coefficient.Allocation.allowance_le bounds
      (segment.pointAt_contains within time inside) root.certificate) fine.work.positive.le
  have actual := arithmetic.numeric.reading_close.le.trans (factor.trans ceiling)
  rewrite [Norm.Bounds.normSq_sub_symm] at actual
  have first := (Norm.Bounds.normSq_sub_le_via _
    (Observation.scalarReading differential (segment.pointAt time) arithmetic.rootSample.observation) _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct spatial actual)
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
  have polynomial := compared.polynomial_error_le_tolerance allowancePaid
  have total := (Norm.Bounds.normSq_sub_le_via _ arithmetic.numeric.reading _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct first polynomial)
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
  have scalar := payment_identity
    (Coefficient.Allocation.sourceCoefficient bounds * oldAccuracy.tolerance)
    (Coefficient.Allocation.sourceCoefficient bounds + Coefficient.Allocation.normalCoefficient bounds +
      Coefficient.Allocation.spatialCoefficient bounds) (Coefficient.Allocation.arithmeticCeiling bounds)
    fine.work.tolerance
  have normalized := total.trans_eq scalar
  exact normalized.trans
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) fine.work_payment)

end Reading.Payment.Fine

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
