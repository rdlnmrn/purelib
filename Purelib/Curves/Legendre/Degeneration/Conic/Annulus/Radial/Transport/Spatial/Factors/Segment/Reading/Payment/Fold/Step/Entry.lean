module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step

import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Transport

/-! # Original factor observations entering another physical segment

The source Reading and its RequestedSamples are unchanged inputs from the
preceding physical preparation. One actual new-segment request target is
queried and sampled. The complete original prepared-root request and paid
cross-segment comparison remain cached with their factory identities.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
namespace Reading.Payment.Fold.Step.Entry

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint StepRequest CachedSource prepared advance)
open Purelib.Riemann.Paths (PreparedTraceBudget)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets previousBudgets : Budgets anchor}
variable {start finish previousStart previousFinish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  previousStart previousFinish}
variable {within : segment.WithinAmbient} {previousWithin : previousSegment.WithinAmbient}
variable {completed : Segment budgets segment within}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
variable {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current owner request}
variable (first : Reading previousCompleted previousTime previousInside)
variable (firstSamples : RequestedSamples (anchor := anchor) first)
variable (point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
variable (agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner))
variable (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound)
variable {left right : Endpoint}
variable (trace : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ trace.rootDiameter)
variable (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance)

-- Keep the exact affine coordinate atomic while elaborating dependent owner/cache indices.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The actual first advance keeps both original product observations, prepared-root cache and source relation. -/
@[expose] def Compared (last : TargetReading (completed := completed) (request := request))
    (lastSamples : RequestedSamples (anchor := anchor) last)
    (root : PreparedRoot (segment := segment) (current := current))
    (root_eq : RootCache (cached := cached) root) (observed : PreparedRequest (anchor := anchor) root) :=
  CachedSource.AdvanceAgreement cached within (cachedSmall (cached := cached) small)
    first.values.value last.values.value firstSamples.samples.product lastSamples.samples.product agreement
    root (by unfold RootCache at root_eq; exact root_eq) observed.reading
    (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive

/-- The entire stored comparison is the original paid factory on the unchanged preceding observations. -/
@[irreducible, expose] def ComparedCache (last : TargetReading (completed := completed) (request := request))
    (lastSamples : RequestedSamples (anchor := anchor) last)
    (root : PreparedRoot (segment := segment) (current := current))
    (root_eq : RootCache (cached := cached) root) (observed : PreparedRequest (anchor := anchor) root)
    (compared : Compared first firstSamples agreement small last lastSamples root root_eq observed) : Prop :=
  compared = firstSamples.advanceAgreementFrom
    (previousSegment := previousSegment) (previousCompleted := previousCompleted)
    (previousTime := previousTime) (previousInside := previousInside) (completed := completed)
    (current := current) (request := request) lastSamples point_eq owner cached
    (cachedSmall (cached := cached) small) agreement trace requestFit root
      (by unfold RootCache at root_eq; exact root_eq) observed width

/-- Complete target, prepared and comparison caches for the original first cross-segment request.

The preceding Reading/Samples stay exact source indices. The target belongs
to the separate actual new-segment preparation. All newly constructed data
are retained with whole factory equations; no source observation is sampled
again or retagged as an observation of the new preparation.
-/
@[expose] def Cache :=
  Σ last : { reading : TargetReading (completed := completed) (request := request) // TargetCache reading },
    Σ samples : { retained : RequestedSamples (anchor := anchor) last.val // SamplesCache last.val retained },
      Σ root : { retained : PreparedRoot (segment := segment) (current := current) //
          RootCache (cached := cached) retained },
        Σ observed : { retained : PreparedRequest (anchor := anchor) root.val // RequestCache root.val retained },
          { compared : Compared first firstSamples agreement small last.val samples.val root.val root.property
              observed.val // ComparedCache first firstSamples point_eq agreement small trace requestFit width
                last.val samples.val root.val root.property observed.val compared }

namespace Cache

/-- Retain the complete target and comparison caches without repeating any query, observation or comparison. -/
@[expose] def ofCompleted
    (last : TargetReading (completed := completed) (request := request)) (last_eq : TargetCache last)
    (lastSamples : RequestedSamples (anchor := anchor) last) (samples_eq : SamplesCache last lastSamples)
    (root : PreparedRoot (segment := segment) (current := current)) (root_eq : RootCache (cached := cached) root)
    (observed : PreparedRequest (anchor := anchor) root) (observed_eq : RequestCache root observed)
    (compared : Compared first firstSamples agreement small last lastSamples root root_eq observed)
    (compared_eq : ComparedCache first firstSamples point_eq agreement small trace requestFit width
      last lastSamples root root_eq observed compared) :
    Cache (completed := completed) (cached := cached) first firstSamples point_eq agreement small trace
      requestFit width :=
  ⟨⟨last, last_eq⟩, ⟨⟨lastSamples, samples_eq⟩, ⟨⟨root, root_eq⟩,
    ⟨⟨observed, observed_eq⟩, ⟨compared, compared_eq⟩⟩⟩⟩⟩

/-- Query only the new target, then retain its exact Samples and original prepared-root comparison factory. -/
def build : Cache (completed := completed) (cached := cached) first firstSamples point_eq agreement small trace
      requestFit width :=
  let last := Reading.build completed request.endpoint.parameter request.endpoint.inside
  let samples := RequestedSamples.build last
  let root := cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero
  let observed := Equivalence.Observation.Request.build root.value (radiusOutput anchor).tolerance
    (radiusOutput anchor).positive
  let compared := firstSamples.advanceAgreementFrom
    (previousSegment := previousSegment) (previousCompleted := previousCompleted)
    (previousTime := previousTime) (previousInside := previousInside) (completed := completed)
    (current := current) (request := request) samples point_eq owner cached
    (cachedSmall (cached := cached) small) agreement trace requestFit root rfl observed width
  ofCompleted first firstSamples point_eq agreement small trace requestFit width last
    (by unfold TargetCache; rfl) samples (by unfold SamplesCache; rfl) root (by unfold RootCache; rfl)
    observed (by unfold RequestCache; rfl) compared (by unfold ComparedCache; rfl)

variable {first : Reading previousCompleted previousTime previousInside}
variable {firstSamples : RequestedSamples (anchor := anchor) first}
variable {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
variable {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound}
variable {trace : PreparedTraceBudget segment left right} {requestFit : request.rootDiameter ≤ trace.rootDiameter}
variable {width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance}
variable (cache : Cache (completed := completed) (cached := cached) first firstSamples point_eq agreement small trace
  requestFit width)

/-- Read the identical complete target Reading from the actual new physical preparation. -/
@[expose] def last := cache.1.val

/-- Read the same target RequestedSamples handed unchanged into the following original same-segment fold. -/
@[expose] def lastSamples : RequestedSamples (anchor := anchor) cache.last := cache.2.1.val

/-- Read the identical prepared-root certificate of this actual original CachedSource. -/
@[expose] def root := cache.2.2.1.val

/-- The retained full-cubic certificate is the same original actual CachedSource certificate. -/
theorem root_eq : cache.root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero := by
  have retained := cache.2.2.1.property
  unfold RootCache at retained
  exact retained

/-- Read the exact actual observation request on that retained prepared-root certificate. -/
@[expose] def observed : PreparedRequest (anchor := anchor) cache.root := cache.2.2.2.1.val

/-- Read the complete original cross-segment comparison, retaining both actual product observations. -/
@[expose] def compared := cache.2.2.2.2.val

/-- The target Reading is the identical physical preparation query at the actual request endpoint. -/
theorem last_eq : cache.last = Reading.build completed request.endpoint.parameter request.endpoint.inside := by
  have retained := cache.1.property
  unfold TargetCache at retained
  exact retained

/-- The target Samples are the original complete factory on the same cached target Reading. -/
theorem lastSamples_eq : cache.lastSamples = RequestedSamples.build cache.last := by
  have retained := cache.2.1.property
  unfold SamplesCache at retained
  exact retained

/-- The prepared-root request is the exact complete original request on the retained certificate. -/
theorem observed_eq : cache.observed = Equivalence.Observation.Request.build cache.root.value
    (radiusOutput anchor).tolerance (radiusOutput anchor).positive := by
  have retained := cache.2.2.2.1.property
  unfold RequestCache at retained
  exact retained

/-- The stored cross-segment comparison is the same original paid factory on both actual product observations. -/
theorem compared_eq : cache.compared = firstSamples.advanceAgreementFrom
    (previousSegment := previousSegment) (previousCompleted := previousCompleted)
    (previousTime := previousTime) (previousInside := previousInside) (completed := completed)
    (current := current) (request := request) cache.lastSamples point_eq owner cached
    (cachedSmall (cached := cached) small) agreement trace requestFit cache.root cache.root_eq
      cache.observed width := by
  have retained := cache.2.2.2.2.property
  unfold ComparedCache at retained
  exact retained

/-- The cached comparison derives agreement with the exact original canonical tail Owner.

Only the original advanceCached_eq_advance law transports the finishing
Owner name. The original target Reading and all its observation caches
remain unchanged throughout that exact endpoint transport.
-/
@[irreducible, expose] def nextAgreement :
    SourceAgreement (current := request.endpoint) (completed := completed)
      (owner := advance segment within current owner request small) cache.last := by
  have compared := CachedSource.AdvanceAgreement.canonicalEquivalent
    (cached := cached) (within := within) (small := cachedSmall (cached := cached) small)
    (sourceChannel := first.values.value) (targetChannel := cache.last.values.value)
    (sourceReading := firstSamples.samples.product) (targetReading := cache.lastSamples.samples.product)
    (sourceAgreement := agreement) (root := cache.root) (root_eq := cache.root_eq)
    (preparedReading := cache.observed.reading) (comparisonTarget := (comparisonTarget anchor).tolerance)
    (comparisonPositive := (comparisonTarget anchor).positive) cache.compared small
  exact compared.symm

end Cache

end Reading.Payment.Fold.Step.Entry
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
