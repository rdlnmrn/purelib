module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Product.Request
public import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Transport
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Trace
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Advance
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Original factor observations paying the actual cubic advance budget

The computed original requests retain both residual ceilings and the product
radius payment. Each supplied physical factor query is sampled once on those
exact requests. A previous segment's target observations can remain the next
segment's source input at their exact common spatial point. The actual product
radius, prepared reading radius, original trace diameter and separately paid physical width imply the full signed-sum
budget. No target relation or replacement covered owner is an input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint StepRequest CachedSource)
open Purelib.Riemann.Paths (PreparedTraceBudget)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

variable {previousBudgets : Budgets anchor} {previousStart previousFinish : Canonical}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  previousStart previousFinish}
variable {previousWithin : previousSegment.WithinAmbient}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
variable {previousReading : Reading previousCompleted previousTime previousInside}

/-- The original product and prepared readings' positive common visible-radius request. -/
@[expose] def radiusOutput (anchor : Parameter.Anchor source.lift) : AccuracyRequest :=
  ⟨floor anchor / Fraction.Cast.fromInt 1024,
    Fraction.Order.Field.div_pos_direct (floor_positive anchor) (by decide +kernel)⟩

/-- The original source/prepared comparison's positive target on the same actual source floor. -/
@[expose] def comparisonTarget (anchor : Parameter.Anchor source.lift) : AccuracyRequest :=
  ⟨floor anchor / Fraction.Cast.fromInt 256,
    Fraction.Order.Field.div_pos_direct (floor_positive anchor) (by decide +kernel)⟩

/-- Original computed factor requests and the complete supplied Samples on those same exact request indices. -/
@[expose] def RequestedSamples (reading : Reading completed time inside) :=
  Σ requests : { retained : ProductRequests reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor) //
      retained = ProductRequests.build reading.values.unitRoot reading.values.normalRoot
        (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor) },
    Samples reading requests.val.first requests.val.last

namespace RequestedSamples

variable {reading : Reading completed time inside}

/-- Retain original requests and existing Samples without changing their observations or request indices.

The complete Samples input already retains its original factor observations,
selected states, residual comparisons and actual paired-product cache. This
constructor also accepts original after-stage observations at these same
requests; it never calls another sampling or refinement procedure.
-/
@[expose] def ofCompleted
    (requests : ProductRequests reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor))
    (requests_eq : requests = ProductRequests.build reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor))
    (samples : Samples reading requests.first requests.last) : RequestedSamples (anchor := anchor) reading :=
  ⟨⟨requests, requests_eq⟩, samples⟩

/-- Compute both factor requests once, then sample each original certificate once and retain the product Reading. -/
def build (reading : Reading completed time inside) : RequestedSamples (anchor := anchor) reading :=
  let requests := ProductRequests.build reading.values.unitRoot reading.values.normalRoot
    (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor)
  let samples := Samples.build reading requests.first requests.last
  ofCompleted requests rfl samples

/-- Read the same original two-factor request cache, including its common multiplication input. -/
@[expose] def requests (retained : RequestedSamples (anchor := anchor) reading) := retained.1.val

/-- Read the same actual original factor Samples and complete full-product Reading. -/
@[expose] def samples (retained : RequestedSamples (anchor := anchor) reading) :
    Samples reading retained.requests.first retained.requests.last := retained.2

/-- The request cache is the original complete constructor on the same supplied geometric certificates. -/
theorem requests_eq (retained : RequestedSamples (anchor := anchor) reading) : retained.requests =
    ProductRequests.build reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor) := retained.1.property

/-- The completed-cache constructor retains the identical Samples with all its actual observations. -/
theorem ofCompleted_samples
    (requests : ProductRequests reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor))
    (requests_eq : requests = ProductRequests.build reading.values.unitRoot reading.values.normalRoot
      (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor))
    (samples : Samples reading requests.first requests.last) :
    (ofCompleted requests requests_eq samples).samples = samples := rfl

/-- The actual stored product radius is paid on the same two retained factor-observation states. -/
theorem product_radius_lt (retained : RequestedSamples (anchor := anchor) reading) :
    retained.samples.product.radius < (radiusOutput anchor).tolerance := by
  rewrite [retained.samples.product_eq]
  exact retained.requests.product_radius_lt retained.samples.unit retained.samples.normal
    reading.values.value reading.values.value_eq

variable {lastTime : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside lastTime}
variable {lastReading : Reading completed lastTime lastInside}

/-- Distinct physical preparation request caches pay the same original target segment movement. -/
theorem movement_le_from (first : RequestedSamples (anchor := anchor) previousReading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (width : (time - lastTime) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
      (firstUnit := first.requests.first) (firstNormal := first.requests.last)
      (lastUnit := last.requests.first) (lastNormal := last.requests.last) ≤ floor anchor / 4 :=
  Payment.movement_le first.requests.first_residual_lt.le last.requests.first_residual_lt.le
    first.requests.last_residual_lt.le last.requests.last_residual_lt.le (spatial_paid_of_width width)

/-- These exact two original request caches and a paid physical width imply the product's quarter-floor movement. -/
theorem movement_le (first : RequestedSamples (anchor := anchor) reading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (width : (time - lastTime) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
      (firstUnit := first.requests.first) (firstNormal := first.requests.last)
      (lastUnit := last.requests.first) (lastNormal := last.requests.last) ≤ floor anchor / 4 :=
  movement_le_from (previousSegment := segment) (previousCompleted := completed)
    (previousTime := time) first last width

/-- The actual original source/product and prepared request radii pay one sixteenth of the full-product floor.

The comparison target is the same original positive request. The bound uses
the actual retained source product radius and actual prepared Reading radius,
without replacing either observation or using an independently chosen pair.
-/
theorem comparison_bound_le (retained : RequestedSamples (anchor := anchor) reading)
    {rootParameter : Canonical} {root : CertifiedSquareRoot.Certificate rootParameter}
    (prepared : Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance) :
    16 * (retained.samples.product.radius + prepared.reading.radius) +
      4 * (comparisonTarget anchor).tolerance ≤ floor anchor / 16 := by
  have radii := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct retained.product_radius_lt.le prepared.radius_lt.le)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
  have scaled := Arithmetic.add_le_add_direct radii
    (Fraction.Order.Basic.le_refl (4 * (comparisonTarget anchor).tolerance))
  apply scaled.trans
  change 16 * (floor anchor / Fraction.Cast.fromInt 1024 + floor anchor / Fraction.Cast.fromInt 1024) +
    4 * (floor anchor / Fraction.Cast.fromInt 256) ≤ floor anchor / 16
  simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
  calc
    _ = (16 * (2 * (Fraction.Cast.fromInt 1024)⁻¹) + 4 * (Fraction.Cast.fromInt 256)⁻¹) * floor anchor := by ring1
    _ ≤ (16 : Fraction.Rational)⁻¹ * floor anchor :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide +kernel : (16 * (2 * (Fraction.Cast.fromInt 1024)⁻¹) +
          4 * (Fraction.Cast.fromInt 256)⁻¹ : Fraction.Rational) ≤ (16 : Fraction.Rational)⁻¹)
        (floor_positive anchor).le
    _ = _ := Fraction.Field.mul_comm _ _

end RequestedSamples

variable {current : Endpoint} {request : StepRequest}
variable {firstReading : Reading completed current.parameter current.inside}
variable {lastReading : Reading completed request.endpoint.parameter request.endpoint.inside}
variable {left right : Endpoint}

/-- Original cross-segment observations, trace fit and physical width pay the same actual cached-advance sum bound.

The original prepared box is paid by the unchanged trace budget. Both actual
factor request/Samples caches pay residual movement and product radius,
including an unchanged source observation from a different preparation. The
prepared request consumes the original supplied full-cubic certificate. The
only additional geometric condition is the stated width of this same
physical segment step, which the computed finite depth can supply.
-/
theorem advance_payment_le_from
    (first : RequestedSamples (anchor := anchor) previousReading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (budget : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ budget.rootDiameter)
    {root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (prepared : Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    CachedSource.advancePayment first.samples.product prepared.reading (comparisonTarget anchor).tolerance
      cached.preparedOwner.track.initial.box.diagonalSq
      (productMovement (time := current.parameter) (lastTime := request.endpoint.parameter)
        (anchor := anchor) (segment := segment) (firstUnit := first.requests.first) (firstNormal := first.requests.last)
        (lastUnit := last.requests.first) (lastNormal := last.requests.last)) ≤ floor anchor := by
  have comparison := first.comparison_bound_le prepared
  have diameter := Clearance.prepared_diameter_le anchor segment within budget current owner request cached requestFit
  have movement := first.movement_le_from (time := current.parameter) last width
  have comparisonScaled := Arithmetic.mul_le_mul_of_nonneg_left_direct comparison
    (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
  have diameterScaled := Arithmetic.mul_le_mul_of_nonneg_left_direct diameter
    (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
  have movementScaled := Arithmetic.mul_le_mul_of_nonneg_left_direct movement
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  exact (Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct comparisonScaled diameterScaled) movementScaled).trans_eq (by
      change 4 * (floor anchor / 16) + 4 * (floor anchor / 16) + 2 * (floor anchor / 4) = floor anchor
      simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
      calc
        _ = (4 * (16 : Fraction.Rational)⁻¹ + 4 * (16 : Fraction.Rational)⁻¹ + 2 * (4 : Fraction.Rational)⁻¹) *
            floor anchor := by ring1
        _ = _ := by
          rewrite [show (4 * (16 : Fraction.Rational)⁻¹ + 4 * (16 : Fraction.Rational)⁻¹ +
            2 * (4 : Fraction.Rational)⁻¹) = 1 by decide +kernel]
          exact Fraction.Field.one_mul _)

/-- Original trace fit, computed observations and physical-width payment pay the complete cached-advance sum bound.

The original prepared box is paid by the unchanged trace budget. Both actual
factor request/Samples caches pay residual movement and product radius. The
prepared request consumes the original supplied full-cubic certificate. The
only additional geometric condition is the stated width of this same
physical segment step, which the computed finite depth can supply.
-/
theorem advance_payment_le
    (first : RequestedSamples (anchor := anchor) firstReading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (budget : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ budget.rootDiameter)
    {root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (prepared : Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    CachedSource.advancePayment first.samples.product prepared.reading (comparisonTarget anchor).tolerance
      cached.preparedOwner.track.initial.box.diagonalSq
      (productMovement (time := current.parameter) (lastTime := request.endpoint.parameter)
        (anchor := anchor) (segment := segment) (firstUnit := first.requests.first) (firstNormal := first.requests.last)
        (lastUnit := last.requests.first) (lastNormal := last.requests.last)) ≤ floor anchor :=
  advance_payment_le_from (previousSegment := segment) (previousCompleted := completed)
    (previousTime := current.parameter) first last owner cached budget requestFit prepared width

namespace RequestedSamples

/-- Derive the next actual cubic advance with the previous segment's unchanged terminal observations.

The exact physical-point equation identifies the previous Reading with the
new segment's current coordinate while preserving its entire Samples cache.
The source relation concerns the current original Owner. Its actual retained
preparation and reading are consumed unchanged. Original trace fit and the
computed factor requests pay the entire scalar sum bound internally, so no
separate budget inequality or desired target relation is supplied.
-/
def advanceAgreementFrom
    (first : RequestedSamples (anchor := anchor) previousReading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceAgreement : NamedEquivalent previousReading.values.value.name
      (owner.certificate owner.parameterNonzero).value.name)
    (budget : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ budget.rootDiameter)
    (root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (prepared : Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    CachedSource.AdvanceAgreement cached within small previousReading.values.value lastReading.values.value
      first.samples.product last.samples.product sourceAgreement root root_eq prepared.reading
      (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive :=
  Samples.advanceAgreementFrom first.samples last.samples point_eq owner cached small sourceAgreement
    root root_eq prepared.reading
    (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive
    (Payment.advance_payment_le_from first last owner cached budget requestFit prepared width)

/-- Derive actual cached-advance agreement from the original observation caches and a paid physical step width.

The source relation concerns the current original Owner. Its actual retained
preparation and reading are consumed unchanged. Original trace fit and the
computed factor requests pay the entire scalar sum bound internally, so no
separate budget inequality or desired target relation is supplied.
-/
def advanceAgreement
    (first : RequestedSamples (anchor := anchor) firstReading)
    (last : RequestedSamples (anchor := anchor) lastReading)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceAgreement : NamedEquivalent firstReading.values.value.name
      (owner.certificate owner.parameterNonzero).value.name)
    (budget : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ budget.rootDiameter)
    (root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (prepared : Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    CachedSource.AdvanceAgreement cached within small firstReading.values.value lastReading.values.value
      first.samples.product last.samples.product sourceAgreement root root_eq prepared.reading
      (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive :=
  Samples.advanceAgreement first.samples last.samples owner cached small sourceAgreement root root_eq prepared.reading
    (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive
    (Payment.advance_payment_le first last owner cached budget requestFit prepared width)

end RequestedSamples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
