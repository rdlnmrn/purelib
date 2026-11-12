module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Movement
public import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Transport
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Actual full-cubic advance agreement from retained physical factors

Both source and target factor queries and observations remain their original
physical-preparation inputs. The source may be the unchanged terminal
observation of a different segment at the same actual physical point. Their
internally derived full-product floor and movement supply the actual cached cubic advance comparison. Only the stated
finite scalar payment remains additional evidence; no target agreement or
canonical-cycle correspondence is supplied as a field.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint StepRequest CachedSource)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {current : Endpoint} {request : StepRequest}
variable {firstReading : Reading completed current.parameter current.inside}
variable {lastReading : Reading completed request.endpoint.parameter request.endpoint.inside}
variable {firstUnit firstNormal lastUnit lastNormal : Approximation.AccuracyRequest}

section PreviousSegment

variable {previousBudgets : Budgets anchor} {previousStart previousFinish : Canonical}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  previousStart previousFinish}
variable {previousWithin : previousSegment.WithinAmbient}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
variable {previousReading : Reading previousCompleted previousTime previousInside}

/-- Advance the current full-cubic Owner using an unchanged source observation from another physical segment.

The exact source-point equation identifies the previous original Reading
with the current physical coordinate. Its complete Samples remain unchanged.
The source relation concerns the current original Owner, obtained from the
initial attachment or a preceding accepted advance. Root preparation retains
its own supplied complete certificate and actual reading.
The normalized seed and cofactor observations derive source norm and target
movement internally; the remaining scalar inequality refers to those exact
observations and the actual cached prepared box, rather than a desired final
equivalence.
-/
def advanceAgreementFrom (firstSamples : Samples previousReading firstUnit firstNormal)
    (lastSamples : Samples lastReading lastUnit lastNormal)
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceAgreement : NamedEquivalent previousReading.values.value.name
      (owner.certificate owner.parameterNonzero).value.name)
    (root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (preparedReading : Equivalence.Observation.Reading root.value)
    (comparisonTarget : Fraction.Rational) (comparisonPositive : 0 < comparisonTarget)
    (payment : CachedSource.advancePayment firstSamples.product preparedReading comparisonTarget
      cached.preparedOwner.track.initial.box.diagonalSq
      (productMovement (time := current.parameter) (lastTime := request.endpoint.parameter)
        (anchor := anchor) (segment := segment) (firstUnit := firstUnit) (firstNormal := firstNormal)
        (lastUnit := lastUnit) (lastNormal := lastNormal)) ≤ anchor.seed.separation.radius ^ 2 / 4) :
    CachedSource.AdvanceAgreement cached within small previousReading.values.value lastReading.values.value
      firstSamples.product lastSamples.product sourceAgreement root root_eq preparedReading
      comparisonTarget comparisonPositive :=
  cached.advanceAgreement within small previousReading.values.value lastReading.values.value
    firstSamples.product lastSamples.product sourceAgreement root root_eq preparedReading lastReading.values.square
    (anchor.seed.separation.radius ^ 2 / 4)
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct anchor.seed.separation.positive 2) (by decide +kernel))
    (firstSamples.candidate_normSq_lower firstSamples.product.possible)
    (productMovement (time := current.parameter) (lastTime := request.endpoint.parameter)
      (anchor := anchor) (segment := segment) (firstUnit := firstUnit) (firstNormal := firstNormal)
      (lastUnit := lastUnit) (lastNormal := lastNormal))
    comparisonTarget comparisonPositive
    (fun possible => firstSamples.candidates_distance_le_from lastSamples point_eq
      firstSamples.product.possible possible) payment

end PreviousSegment

/-- Derive the actual cubic advance agreement using the same two paid physical-factor observation caches.

The source relation concerns the original current Owner and may be obtained
from the original initial attachment or a preceding accepted advance. Root preparation retains
its own supplied complete certificate and actual reading.
The normalized seed and cofactor observations derive source norm and target
movement internally; the remaining scalar inequality refers to those exact
observations and the actual cached prepared box, rather than a desired final
equivalence.
-/
def advanceAgreement (firstSamples : Samples firstReading firstUnit firstNormal)
    (lastSamples : Samples lastReading lastUnit lastNormal)
    (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (cached : CachedSource segment current owner request)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceAgreement : NamedEquivalent firstReading.values.value.name
      (owner.certificate owner.parameterNonzero).value.name)
    (root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (preparedReading : Equivalence.Observation.Reading root.value)
    (comparisonTarget : Fraction.Rational) (comparisonPositive : 0 < comparisonTarget)
    (payment : CachedSource.advancePayment firstSamples.product preparedReading comparisonTarget
      cached.preparedOwner.track.initial.box.diagonalSq
      (productMovement (time := current.parameter) (lastTime := request.endpoint.parameter)
        (anchor := anchor) (segment := segment) (firstUnit := firstUnit) (firstNormal := firstNormal)
        (lastUnit := lastUnit) (lastNormal := lastNormal)) ≤ anchor.seed.separation.radius ^ 2 / 4) :
    CachedSource.AdvanceAgreement cached within small firstReading.values.value lastReading.values.value
      firstSamples.product lastSamples.product sourceAgreement root root_eq preparedReading
      comparisonTarget comparisonPositive :=
  advanceAgreementFrom (previousSegment := segment) (previousCompleted := completed)
    (previousTime := current.parameter) firstSamples lastSamples rfl owner cached small sourceAgreement
    root root_eq preparedReading comparisonTarget comparisonPositive payment

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples
