module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Observations
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Branches.PreparedSheetContinuation

/-! # Cached physical factors at one actual subdivision step

The current physical Reading and its RequestedSamples are retained inputs.
The target is queried and sampled once, and the original cached full-cubic
prepared Owner supplies one new certificate/request cache. The paid actual
advance comparison derives its endpoint relation. Exact original
cached/canonical advancement equality supplies the next source relation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold

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
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current owner request}

/-- The original current factor channel agrees with the same nominal full-cubic source Owner. -/
@[expose] def SourceAgreement (reading : Reading completed current.parameter current.inside) :=
  NamedEquivalent reading.values.value.name (ownerRootName owner.parameterNonzero owner)

/-- Original canonical readiness transports to the identical retained prepared Owner's clearance. -/
theorem cachedSmall (small : ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter < (prepared segment current owner request).track.initial.clearance.bound) :
    ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound := by
  rewrite [cached.preparedOwner_eq]
  exact small

namespace Step

variable (first : Reading completed current.parameter current.inside)
variable (firstSamples : RequestedSamples (anchor := anchor) first)
variable (sourceAgreement : SourceAgreement (owner := owner) first)
variable (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound)

/-- The exact complete original target physical Reading type at this same retained request endpoint. -/
@[expose] def TargetReading := Reading completed request.endpoint.parameter request.endpoint.inside

/-- The complete target query is the same physical factor preparation's original requested-time factory. -/
@[irreducible, expose] def TargetCache (reading : TargetReading (completed := completed) (request := request)) : Prop :=
  reading = Reading.build completed request.endpoint.parameter request.endpoint.inside

/-- The complete supplied target Samples use the original request factory on that identical cached Reading. -/
@[irreducible, expose] def SamplesCache (reading : TargetReading (completed := completed) (request := request))
    (samples : RequestedSamples (anchor := anchor) reading) : Prop := samples = RequestedSamples.build reading

/-- The original retained prepared full-cubic Owner supplies the exact current certificate type. -/
@[expose] def PreparedRoot := CertifiedSquareRoot.Certificate
  ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))

/-- The complete prepared certificate belongs to this exact original cached Owner and source radicand. -/
@[irreducible, expose] def RootCache (root : PreparedRoot (segment := segment) (current := current)) : Prop :=
  root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero

/-- The original prepared-root observation request at the same internally paid visible-radius tolerance. -/
@[expose] def PreparedRequest (root : PreparedRoot (segment := segment) (current := current)) :=
  Equivalence.Observation.Request root.value (radiusOutput anchor).tolerance

/-- The actual prepared request is the original complete observation factory on the supplied certificate. -/
@[irreducible, expose] def RequestCache (root : PreparedRoot (segment := segment) (current := current))
    (observed : PreparedRequest (anchor := anchor) root) : Prop :=
  observed = Equivalence.Observation.Request.build root.value (radiusOutput anchor).tolerance
    (radiusOutput anchor).positive

variable {left right : Endpoint}
variable (trace : PreparedTraceBudget segment left right) (requestFit : request.rootDiameter ≤ trace.rootDiameter)
variable (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance)

/-- The actual advance comparison retains these same source, target and prepared observation caches. -/
@[expose] def Compared (last : TargetReading (completed := completed) (request := request))
    (lastSamples : RequestedSamples (anchor := anchor) last)
    (root : PreparedRoot (segment := segment) (current := current))
    (root_eq : RootCache (cached := cached) root) (observed : PreparedRequest (anchor := anchor) root) :=
  CachedSource.AdvanceAgreement cached within (cachedSmall (cached := cached) small)
    first.values.value last.values.value firstSamples.samples.product lastSamples.samples.product sourceAgreement
    root (by unfold RootCache at root_eq; exact root_eq) observed.reading
    (comparisonTarget anchor).tolerance (comparisonTarget anchor).positive

/-- The stored comparison is the complete paid original advance-agreement factory on those same retained inputs. -/
@[irreducible, expose] def ComparedCache (last : TargetReading (completed := completed) (request := request))
    (lastSamples : RequestedSamples (anchor := anchor) last)
    (root : PreparedRoot (segment := segment) (current := current))
    (root_eq : RootCache (cached := cached) root) (observed : PreparedRequest (anchor := anchor) root)
    (compared : Compared first firstSamples sourceAgreement small last lastSamples root root_eq observed) : Prop :=
  compared = firstSamples.advanceAgreement lastSamples owner cached (cachedSmall (cached := cached) small)
    sourceAgreement trace requestFit root (by unfold RootCache at root_eq; exact root_eq) observed width

end Step

/-- Complete once-built target factor queries, Samples, prepared observation and actual advance comparison at one step.

The original request, CachedSource, source Reading/Samples and source relation
remain indices. Whole factory equations retain all newly completed caches.
The actual original full-cubic prepared Owner remains distinct from both
independently constructed physical product channels.
-/
@[expose] def Step
    (first : Reading completed current.parameter current.inside)
    (firstSamples : RequestedSamples (anchor := anchor) first)
    (sourceAgreement : SourceAgreement (owner := owner) first)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound)
    {left right : Endpoint} (trace : PreparedTraceBudget segment left right)
    (requestFit : request.rootDiameter ≤ trace.rootDiameter)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :=
  Σ last : { reading : Step.TargetReading (completed := completed) (request := request) // Step.TargetCache reading },
    Σ samples : { retained : RequestedSamples (anchor := anchor) last.val // Step.SamplesCache last.val retained },
      Σ root : { retained : Step.PreparedRoot (segment := segment) (current := current) //
          Step.RootCache (cached := cached) retained },
        Σ observed : { retained : Step.PreparedRequest (anchor := anchor) root.val //
            Step.RequestCache root.val retained },
          { compared : Step.Compared first firstSamples sourceAgreement small last.val samples.val root.val
              root.property observed.val // Step.ComparedCache first firstSamples sourceAgreement small trace requestFit
                width last.val samples.val root.val root.property observed.val compared }

namespace Step

variable {first : Reading completed current.parameter current.inside}
variable {firstSamples : RequestedSamples (anchor := anchor) first}
variable {sourceAgreement : SourceAgreement (owner := owner) first}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound}
variable {left right : Endpoint} {trace : PreparedTraceBudget segment left right}
variable {requestFit : request.rootDiameter ≤ trace.rootDiameter}
variable {width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance}

/-- Retain completed target, prepared and comparison caches at the same source step without rebuilding them. -/
@[expose] def ofCompleted
    (last : TargetReading (completed := completed) (request := request)) (last_eq : TargetCache last)
    (lastSamples : RequestedSamples (anchor := anchor) last) (samples_eq : SamplesCache last lastSamples)
    (root : PreparedRoot (segment := segment) (current := current)) (root_eq : RootCache (cached := cached) root)
    (observed : PreparedRequest (anchor := anchor) root) (observed_eq : RequestCache root observed)
    (compared : Compared first firstSamples sourceAgreement small last lastSamples root root_eq observed)
    (compared_eq : ComparedCache first firstSamples sourceAgreement small trace requestFit width last lastSamples
      root root_eq observed compared) : Step (cached := cached) first firstSamples sourceAgreement small trace
        requestFit width :=
  ⟨⟨last, last_eq⟩, ⟨⟨lastSamples, samples_eq⟩, ⟨⟨root, root_eq⟩,
    ⟨⟨observed, observed_eq⟩, ⟨compared, compared_eq⟩⟩⟩⟩⟩

/-- Query and sample the target once, retaining the prepared certificate/request and paid actual comparison. -/
def build (first : Reading completed current.parameter current.inside)
    (firstSamples : RequestedSamples (anchor := anchor) first)
    (sourceAgreement : SourceAgreement (owner := owner) first)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound)
    {left right : Endpoint} (trace : PreparedTraceBudget segment left right)
    (requestFit : request.rootDiameter ≤ trace.rootDiameter)
    (width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    Step (cached := cached) first firstSamples sourceAgreement small trace requestFit width :=
  let last := Reading.build completed request.endpoint.parameter request.endpoint.inside
  let samples := RequestedSamples.build last
  let root := cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero
  let observed := Equivalence.Observation.Request.build root.value (radiusOutput anchor).tolerance
    (radiusOutput anchor).positive
  let compared := firstSamples.advanceAgreement samples owner cached (cachedSmall (cached := cached) small)
    sourceAgreement trace requestFit root rfl observed width
  ofCompleted last (by unfold TargetCache; rfl) samples (by unfold SamplesCache; rfl)
    root (by unfold RootCache; rfl) observed (by unfold RequestCache; rfl) compared (by unfold ComparedCache; rfl)

variable (step : Step (cached := cached) first firstSamples sourceAgreement small trace requestFit width)

/-- Read the identical complete target factor Reading retained by the step. -/
@[expose] def last := step.1.val

/-- Read the identical complete target RequestedSamples cache passed unchanged to the next source. -/
@[expose] def lastSamples : RequestedSamples (anchor := anchor) step.last := step.2.1.val

/-- Read the complete prepared certificate of the actual original cached full-cubic Owner. -/
@[expose] def root := step.2.2.1.val

/-- Read the same actual paid prepared-root request and complete retained original observation. -/
@[expose] def observed : PreparedRequest (anchor := anchor) step.root := step.2.2.2.1.val

/-- Read the complete actual advance comparison with its source comparison and target based cache. -/
@[expose] def compared := step.2.2.2.2.val

/-- The completed-cache constructor retains the identical whole target Reading. -/
theorem ofCompleted_last
    (last : TargetReading (completed := completed) (request := request)) (last_eq : TargetCache last)
    (lastSamples : RequestedSamples (anchor := anchor) last) (samples_eq : SamplesCache last lastSamples)
    (root : PreparedRoot (segment := segment) (current := current)) (root_eq : RootCache (cached := cached) root)
    (observed : PreparedRequest (anchor := anchor) root) (observed_eq : RequestCache root observed)
    (compared : Compared first firstSamples sourceAgreement small last lastSamples root root_eq observed)
    (compared_eq : ComparedCache first firstSamples sourceAgreement small trace requestFit width last lastSamples
      root root_eq observed compared) :
    (ofCompleted last last_eq lastSamples samples_eq root root_eq observed observed_eq compared compared_eq).last =
      last := rfl

/-- The completed-cache constructor retains the identical whole target Samples and both actual factor observations. -/
theorem ofCompleted_lastSamples
    (last : TargetReading (completed := completed) (request := request)) (last_eq : TargetCache last)
    (lastSamples : RequestedSamples (anchor := anchor) last) (samples_eq : SamplesCache last lastSamples)
    (root : PreparedRoot (segment := segment) (current := current)) (root_eq : RootCache (cached := cached) root)
    (observed : PreparedRequest (anchor := anchor) root) (observed_eq : RequestCache root observed)
    (compared : Compared first firstSamples sourceAgreement small last lastSamples root root_eq observed)
    (compared_eq : ComparedCache first firstSamples sourceAgreement small trace requestFit width last lastSamples
      root root_eq observed compared) :
    (ofCompleted last last_eq lastSamples samples_eq root root_eq observed observed_eq compared
      compared_eq).lastSamples =
      lastSamples := rfl

/-- The target Reading is the original factory on the same physical preparation and request endpoint. -/
theorem last_eq : step.last = Reading.build completed request.endpoint.parameter request.endpoint.inside := by
  have cache := step.1.property
  unfold TargetCache at cache
  exact cache

/-- The complete target Samples retain the original factory on that identical target Reading. -/
theorem lastSamples_eq : step.lastSamples = RequestedSamples.build step.last := by
  have cache := step.2.1.property
  unfold SamplesCache at cache
  exact cache

/-- The step's complete prepared certificate retains its exact original nominal Owner/cache identity. -/
theorem root_eq : step.root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero := by
  have cache := step.2.2.1.property
  unfold RootCache at cache
  exact cache

/-- The observed prepared-root request is the identical completed original request factory. -/
theorem observed_eq : step.observed = Equivalence.Observation.Request.build step.root.value
    (radiusOutput anchor).tolerance (radiusOutput anchor).positive := by
  have cache := step.2.2.2.1.property
  unfold RequestCache at cache
  exact cache

/-- The advance comparison is the complete original paid factory on the retained observations and geometric payments. -/
theorem compared_eq : step.compared = firstSamples.advanceAgreement step.lastSamples owner cached
    (cachedSmall (cached := cached) small) sourceAgreement trace requestFit step.root step.root_eq
      step.observed width := by
  have cache := step.2.2.2.2.property
  unfold ComparedCache at cache
  exact cache

/-- The original cached/canonical advance equality transports the derived endpoint relation to the exact tail Owner.

The same stored comparison supplies its actual cached-advance endpoint
relation. Exact original Owner equality reindexes only that endpoint name;
the independently constructed target channel remains the same actual input.
-/
@[irreducible, expose] def nextAgreement :
    SourceAgreement (owner := advance segment within current owner request small) step.last := by
  have compared := CachedSource.AdvanceAgreement.canonicalEquivalent
    (cached := cached) (within := within) (small := cachedSmall (cached := cached) small)
    (sourceChannel := first.values.value) (targetChannel := step.last.values.value)
    (sourceReading := firstSamples.samples.product) (targetReading := step.lastSamples.samples.product)
    (sourceAgreement := sourceAgreement) (root := step.root) (root_eq := step.root_eq)
    (preparedReading := step.observed.reading) (comparisonTarget := (comparisonTarget anchor).tolerance)
    (comparisonPositive := (comparisonTarget anchor).positive) step.compared small
  exact compared.symm

end Step

end Reading.Payment.Fold

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
