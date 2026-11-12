module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Product
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Square.Centered.Separation
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Paid movement of actual retained physical factor products

Two actual spatial-factor queries, including queries from separate physical
preparations at a shared corner, retain separate paid observations on their
original normalized and cofactor certificates. Their unchanged signed source
squares pay the two sum denominators. Both original residuals and physical
spatial displacement bound movement of every independently possible product
at those exact paired states; no full-cubic endpoint agreement is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

/-- Original paid factor observations and the one retained full-product Reading on their identical paired states. -/
@[expose] def Samples (reading : Reading completed time inside)
    (unitAccuracy normalAccuracy : Approximation.AccuracyRequest) :=
  Σ unit : ResidualObservation reading.values.unitRoot unitAccuracy,
    Σ normal : ResidualObservation reading.values.normalRoot normalAccuracy,
      { product : Equivalence.Observation.Reading reading.values.value //
          product = unit.productReading normal reading.values.value reading.values.value_eq }

namespace Samples

variable {reading : Reading completed time inside}
variable {unitAccuracy normalAccuracy : Approximation.AccuracyRequest}

/-- Request each supplied original factor once and retain its actual paired-product state, witness and radius. -/
def build (reading : Reading completed time inside)
    (unitAccuracy normalAccuracy : Approximation.AccuracyRequest) : Samples reading unitAccuracy normalAccuracy :=
  let unit := CertifiedSquareRoot.Sampling.request reading.values.unitRoot unitAccuracy
  let normal := CertifiedSquareRoot.Sampling.request reading.values.normalRoot normalAccuracy
  let product := unit.productReading normal reading.values.value reading.values.value_eq
  ⟨unit, normal, product, rfl⟩

/-- Read the identical original cofactor residual observation and its complete comparison/state cache. -/
@[expose] def unit (samples : Samples reading unitAccuracy normalAccuracy) := samples.1

/-- Read the separately retained original normalized residual observation with its own actual process state. -/
@[expose] def normal (samples : Samples reading unitAccuracy normalAccuracy) := samples.2.1

/-- Read the one stored full-product observation on those same two actual factor states. -/
@[expose] def product (samples : Samples reading unitAccuracy normalAccuracy) := samples.2.2.val

/-- The entire original product-reading cache is the factory on the identical supplied factor observations. -/
theorem product_eq (samples : Samples reading unitAccuracy normalAccuracy) :
    samples.product = samples.unit.productReading samples.normal reading.values.value reading.values.value_eq :=
  samples.2.2.property

/-- Every actual cofactor candidate remains in the unchanged original signed reference-root square. -/
theorem unit_inside (samples : Samples reading unitAccuracy normalAccuracy)
    {state : optParam reading.values.unitRoot.value.name.process.State samples.unit.state} {candidate : Canonical}
    (possible : reading.values.unitRoot.value.name.process.Possible state candidate) :
    (UnitRoot.box site).Contains candidate := by
  have initial := CertifiedSquareRoot.Sampling.candidate_in_initial_box reading.unit reading.values.unitRoot_eq possible
  have original := reading.unit_refines.contains initial
  rewrite [actual.data.source_eq, UnitRoot.Transport.source_box] at original
  exact original

/-- Every actual normalized candidate retains the exact original seed's signed-square containment. -/
theorem normal_inside (samples : Samples reading unitAccuracy normalAccuracy)
    {state : optParam reading.values.normalRoot.value.name.process.State samples.normal.state} {candidate : Canonical}
    (possible : reading.values.normalRoot.value.name.process.Possible state candidate) :
    (Box.Square.Centered.Affine.centeredSquare
      (Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate
      anchor.seed.separation.radius anchor.seed.separation.positive.le).Contains candidate := by
  have initial := CertifiedSquareRoot.Sampling.candidate_in_initial_box reading.normal
    reading.values.normalRoot_eq possible
  have original := reading.normal_refines.contains initial
  rewrite [anchor.seed.box_eq] at original
  exact original

/-- The same actual normalized candidate has a twenty-radius-squared norm ceiling from the retained source square. -/
theorem normal_normSq_le (samples : Samples reading unitAccuracy normalAccuracy) {candidate : Canonical}
    (possible : reading.values.normalRoot.value.name.process.Possible samples.normal.state candidate) :
    Norm.Basic.normSq candidate ≤ 20 * anchor.seed.separation.radius ^ 2 := by
  let center := (Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate
  have displacement := Box.Square.Centered.centeredSquare_normSq_sub_center_le center
    anchor.seed.separation.positive.le (samples.normal_inside possible)
  have sum := Norm.Bounds.normSq_add_le_two (candidate - center) center
  rewrite [show candidate - center + center = candidate by ring1] at sum
  exact (sum.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct displacement anchor.seed.separation.norm_le)
    (by decide +kernel))).trans_eq (by ring1)

/-- The actual cofactor candidate obeys the original signed square's endpoint-based norm ceiling. -/
theorem unit_normSq_le (samples : Samples reading unitAccuracy normalAccuracy) {candidate : Canonical}
    (possible : reading.values.unitRoot.value.name.process.Possible samples.unit.state candidate) :
    Norm.Basic.normSq candidate ≤ (UnitRoot.box site).normSqBound :=
  Box.normSq_le_normSqBound (samples.unit_inside possible)

/-- Every actual candidate in the stored paired-product state has the same positive full-ordinate norm floor. -/
theorem candidate_normSq_lower (samples : Samples reading unitAccuracy normalAccuracy) {candidate : Canonical}
    (possible : reading.values.value.name.process.Possible samples.product.state candidate) :
    anchor.seed.separation.radius ^ 2 / 4 ≤ Norm.Basic.normSq candidate := by
  rewrite [samples.product_eq, ResidualObservation.productReading_state] at possible
  rcases samples.unit.product_components samples.normal reading.values.value reading.values.value_eq possible with
    ⟨unit, normal, unitPossible, normalPossible, equality⟩
  have unitLower := (UnitRoot.zeroSide site).margin_le_normSq_sub (samples.unit_inside unitPossible)
  rewrite [UnitRoot.zeroSide_margin, Basic.sub_zero] at unitLower
  have normalLower := anchor.seed.separation.zero.margin_le_normSq_sub (samples.normal_inside normalPossible)
  rewrite [anchor.seed.separation.zero_margin, Basic.sub_zero] at normalLower
  rewrite [equality, Norm.Basic.normSq_mul]
  have lower := Arithmetic.mul_le_mul_direct unitLower normalLower
    (Arithmetic.sq_nonneg_direct _) (Norm.Basic.normSq_nonneg _)
  exact (show anchor.seed.separation.radius ^ 2 / 4 =
    (1 / 4 : Fraction.Rational) * anchor.seed.separation.radius ^ 2 by
      rewrite [Fraction.Field.div_eq_mul_inv_direct (anchor.seed.separation.radius ^ 2) 4,
        Fraction.Field.div_eq_mul_inv_direct 1 4, Fraction.Field.one_mul]
      exact Fraction.Field.mul_comm _ _).trans_le lower

end Samples

variable {lastTime : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside lastTime}
variable {firstReading : Reading completed time inside} {lastReading : Reading completed lastTime lastInside}
variable {firstUnit firstNormal lastUnit lastNormal : Approximation.AccuracyRequest}

/-- The paid cofactor movement includes both original residual tolerances and the actual spatial displacement. -/
@[expose] def unitMovement : Fraction.Rational :=
  4 * (firstUnit.tolerance + lastUnit.tolerance) +
    2 * Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime)

/-- The normalized movement retains both paid residuals, the actual spatial sensitivity and the original sum floor. -/
@[expose] def normalMovement : Fraction.Rational :=
  (4 * (firstNormal.tolerance + lastNormal.tolerance) +
    2 * ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter) *
      Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime))) /
        (4 * anchor.seed.separation.radius ^ 2)

/-- The full-product movement budget uses the same original two factor movements and signed-square magnitude bounds. -/
@[expose] def productMovement : Fraction.Rational :=
  2 * ((UnitRoot.box site).normSqBound *
    normalMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
      (firstNormal := firstNormal) (lastNormal := lastNormal) +
      (20 * anchor.seed.separation.radius ^ 2) *
        unitMovement (time := time) (lastTime := lastTime) (segment := segment)
          (firstUnit := firstUnit) (lastUnit := lastUnit))

namespace Samples

section PreviousSegment

variable {previousBudgets : Budgets anchor} {previousStart previousFinish : Canonical}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  previousStart previousFinish}
variable {previousWithin : previousSegment.WithinAmbient}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
variable {previousReading : Reading previousCompleted previousTime previousInside}

/-- Original cofactor readings from distinct physical preparations pay movement on the retained target segment.

The first observation remains indexed by its separate original Reading. Only
its exact spatial coordinate is identified with the target segment parameter;
its process state, certificate and residual payment are never retagged.
-/
theorem unit_distance_le_from (leftSamples : Samples previousReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal)
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt time)
    {firstCandidate lastCandidate : Canonical}
    (firstPossible : previousReading.values.unitRoot.value.name.process.Possible leftSamples.unit.state firstCandidate)
    (lastPossible : lastReading.values.unitRoot.value.name.process.Possible rightSamples.unit.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      unitMovement (time := time) (lastTime := lastTime) (segment := segment)
        (firstUnit := firstUnit) (lastUnit := lastUnit) := by
  have firstResidual := leftSamples.unit.residual_lt (by rewrite [leftSamples.unit.observation_eq]; exact firstPossible)
  have lastResidual := rightSamples.unit.residual_lt (by rewrite [rightSamples.unit.observation_eq]; exact lastPossible)
  exact Norm.SquareResidual.distance_le
    (UnitRoot.box_sum_lower site (leftSamples.unit_inside firstPossible) (rightSamples.unit_inside lastPossible))
    firstResidual.le lastResidual.le (by
      have radicands := (Clearance.cofactor_distance site
        (previousSegment.pointAt previousTime) (segment.pointAt lastTime)).le
      have displacement := congrArg
        (fun point : Canonical => Norm.Basic.normSq (point - segment.pointAt lastTime)) point_eq
      exact radicands.trans_eq displacement)

/-- Distinct physical preparations retain the same normalized signed Seed floor and paid spatial movement. -/
theorem normal_distance_le_from (leftSamples : Samples previousReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal)
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt time)
    {firstCandidate lastCandidate : Canonical}
    (firstPossible : previousReading.values.normalRoot.value.name.process.Possible
      leftSamples.normal.state firstCandidate)
    (lastPossible : lastReading.values.normalRoot.value.name.process.Possible rightSamples.normal.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      normalMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
        (firstNormal := firstNormal) (lastNormal := lastNormal) := by
  have firstResidual := leftSamples.normal.residual_lt (by
    rewrite [leftSamples.normal.observation_eq]
    exact firstPossible)
  have lastResidual := rightSamples.normal.residual_lt (by
    rewrite [rightSamples.normal.observation_eq]
    exact lastPossible)
  exact Norm.SquareResidual.distance_le_of_sum_lower
    (Arithmetic.mul_pos_direct (by decide +kernel)
      (Arithmetic.pow_pos_direct anchor.seed.separation.positive 2))
    (anchor.seed.separation.sum_normSq_lower
      (leftSamples.normal_inside firstPossible) (rightSamples.normal_inside lastPossible))
    firstResidual.le lastResidual.le
    (by
      have radicands := Clearance.normalized_distance_le site parameter (Waist.direction quarter first) anchor.regular
        (previousSegment.pointAt_contains previousWithin previousTime previousInside)
        (segment.pointAt_contains within lastTime lastInside)
      have displacement := congrArg
        (fun point : Canonical =>
          (Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter) *
            Norm.Basic.normSq (point - segment.pointAt lastTime)) point_eq
      exact radicands.trans_eq displacement)

/-- Actual products from distinct physical preparations obey the retained target segment movement.

The original multiplication possibility witnesses supply both actual factor
readings. Both unchanged cached residual observations and their shared
original signed-square bounds pay the estimate. No independently acquired
root owner or final comparison certificate appears among the inputs.
-/
theorem candidates_distance_le_from (leftSamples : Samples previousReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal)
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt time)
    {firstCandidate lastCandidate : Canonical}
    (firstPossible : previousReading.values.value.name.process.Possible leftSamples.product.state firstCandidate)
    (lastPossible : lastReading.values.value.name.process.Possible rightSamples.product.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
        (firstUnit := firstUnit) (firstNormal := firstNormal) (lastUnit := lastUnit) (lastNormal := lastNormal) := by
  rewrite [leftSamples.product_eq, ResidualObservation.productReading_state] at firstPossible
  rewrite [rightSamples.product_eq, ResidualObservation.productReading_state] at lastPossible
  rcases leftSamples.unit.product_components leftSamples.normal previousReading.values.value
    previousReading.values.value_eq firstPossible with
      ⟨firstCofactor, firstOrdinate, firstCofactorPossible, firstOrdinatePossible, firstEq⟩
  rcases rightSamples.unit.product_components rightSamples.normal lastReading.values.value
    lastReading.values.value_eq lastPossible with
      ⟨lastCofactor, lastOrdinate, lastCofactorPossible, lastOrdinatePossible, lastEq⟩
  have unitClose := leftSamples.unit_distance_le_from rightSamples point_eq
    firstCofactorPossible lastCofactorPossible
  have normalClose := leftSamples.normal_distance_le_from rightSamples point_eq
    firstOrdinatePossible lastOrdinatePossible
  have firstUpper := leftSamples.unit_normSq_le firstCofactorPossible
  have lastUpper := rightSamples.normal_normSq_le lastOrdinatePossible
  have difference : firstCandidate - lastCandidate =
      firstCofactor * (firstOrdinate - lastOrdinate) + (firstCofactor - lastCofactor) * lastOrdinate := by
    rewrite [firstEq, lastEq]
    ring1
  rewrite [difference]
  have triangle := Norm.Bounds.normSq_add_le_two
    (firstCofactor * (firstOrdinate - lastOrdinate)) ((firstCofactor - lastCofactor) * lastOrdinate)
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul] at triangle
  have normalTerm := Arithmetic.mul_le_mul_direct firstUpper normalClose
    (Norm.Basic.normSq_nonneg _) ((Norm.Basic.normSq_nonneg _).trans firstUpper)
  have unitTerm := Arithmetic.mul_le_mul_direct unitClose lastUpper
    (Norm.Basic.normSq_nonneg _) ((Norm.Basic.normSq_nonneg _).trans unitClose)
  exact (triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct normalTerm unitTerm) (by decide +kernel))).trans_eq (by
      unfold productMovement
      ring1)

end PreviousSegment

/-- Independently possible original cofactor readings obey the movement budget paid on their identical observations. -/
theorem unit_distance_le (leftSamples : Samples firstReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal) {firstCandidate lastCandidate : Canonical}
    (firstPossible : firstReading.values.unitRoot.value.name.process.Possible leftSamples.unit.state firstCandidate)
    (lastPossible : lastReading.values.unitRoot.value.name.process.Possible rightSamples.unit.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      unitMovement (time := time) (lastTime := lastTime) (segment := segment)
        (firstUnit := firstUnit) (lastUnit := lastUnit) :=
  unit_distance_le_from (previousSegment := segment) (previousCompleted := completed)
    (previousTime := time) leftSamples rightSamples rfl firstPossible lastPossible

/-- Independently possible normalized readings obey their paid movement with the original signed-seed sum floor. -/
theorem normal_distance_le (leftSamples : Samples firstReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal) {firstCandidate lastCandidate : Canonical}
    (firstPossible : firstReading.values.normalRoot.value.name.process.Possible leftSamples.normal.state firstCandidate)
    (lastPossible : lastReading.values.normalRoot.value.name.process.Possible rightSamples.normal.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      normalMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
        (firstNormal := firstNormal) (lastNormal := lastNormal) :=
  normal_distance_le_from (previousSegment := segment) (previousCompleted := completed)
    (previousTime := time) leftSamples rightSamples rfl firstPossible lastPossible

/-- Every independently possible pair of actual full products obeys the computed physical product movement.

The original multiplication possibility witnesses supply both actual factor
readings. Their same cached residual observations and signed-square bounds
pay the estimate. No independently acquired root owner or final comparison
certificate appears among the inputs.
-/
theorem candidates_distance_le (leftSamples : Samples firstReading firstUnit firstNormal)
    (rightSamples : Samples lastReading lastUnit lastNormal) {firstCandidate lastCandidate : Canonical}
    (firstPossible : firstReading.values.value.name.process.Possible leftSamples.product.state firstCandidate)
    (lastPossible : lastReading.values.value.name.process.Possible rightSamples.product.state lastCandidate) :
    Norm.Basic.normSq (firstCandidate - lastCandidate) ≤
      productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
        (firstUnit := firstUnit) (firstNormal := firstNormal) (lastUnit := lastUnit) (lastNormal := lastNormal) :=
  candidates_distance_le_from (previousSegment := segment) (previousCompleted := completed)
    (previousTime := time) leftSamples rightSamples rfl firstPossible lastPossible

section IndependentSources

variable {otherQuarter : UnitCircuitQuarter} {otherPositive : (0 : Fraction.Rational) < 2}
variable {otherActual : Transport.Quarter site parameter 2 otherQuarter otherPositive}
variable {otherReference : Fraction.Rational} {otherReferenceInside : FixedRootBoxPath.Inside otherReference}
variable {otherSource : Transport.Reading otherActual otherReference otherReferenceInside}
variable {otherAnchor : Parameter.Anchor otherSource.lift} {otherBudgets : Budgets otherAnchor}
variable {otherStart otherFinish : Canonical}
variable {otherSegment : ClearSegment (Paths.polynomial parameter) (sourceBox otherAnchor) otherStart otherFinish}
variable {otherWithin : otherSegment.WithinAmbient} {otherCompleted : Segment otherBudgets otherSegment otherWithin}
variable {otherTime : Fraction.Rational} {otherInside : FixedRootBoxPath.Inside otherTime}
variable {otherReading : Reading otherCompleted otherTime otherInside}

/-- Independent original signed normalized states have a positive sum floor at the same physical point.

Each possible reading stays in its own original source seed's signed square.
The common physical point lies in both retained clear regions, so the
normalized projection bound applies without identifying either root Owner,
process state, anchor or independently prepared factor certificate.
-/
theorem normal_sum_lower (firstSamples : Samples firstReading firstUnit firstNormal)
    (otherSamples : Samples otherReading lastUnit lastNormal)
    (point_eq : segment.pointAt time = otherSegment.pointAt otherTime)
    {firstState : firstReading.values.normalRoot.value.name.process.State}
    {otherState : otherReading.values.normalRoot.value.name.process.State}
    {firstCandidate otherCandidate : Canonical}
    (firstPossible : firstReading.values.normalRoot.value.name.process.Possible firstState firstCandidate)
    (otherPossible : otherReading.values.normalRoot.value.name.process.Possible otherState otherCandidate) :
    (1 / 4096 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq (firstCandidate + otherCandidate) := by
  have firstRegion := segment.pointAt_contains within time inside
  have otherRegion := otherSegment.pointAt_contains otherWithin otherTime otherInside
  have sharedRegion : (sourceBox otherAnchor).Contains (segment.pointAt time) := point_eq.symm ▸ otherRegion
  exact Clearance.normalized_sum_lower site parameter (Waist.direction quarter first)
    (Waist.direction otherQuarter otherReference) anchor.regular anchor.seed.separation otherAnchor.seed.separation
    (firstSamples.normal_inside firstPossible) (otherSamples.normal_inside otherPossible) firstRegion sharedRegion

end IndependentSources

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
