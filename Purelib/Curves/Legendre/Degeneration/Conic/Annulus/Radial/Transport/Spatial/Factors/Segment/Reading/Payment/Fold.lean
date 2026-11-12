module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step
public import Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.Width
import Purelib.Riemann.Branches.PreparedSheetContinuation

/-! # Physical factor comparison along the actual subdivision spine

Structural recursion follows the original Subdivision with its actual
CachedSources and advances. A step's complete target Reading and Samples
become the next source inputs unchanged. Original trace and physical-width
certificates pay each comparison. The terminal comparison is derived from
the initial source relation; no final agreement is supplied as evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation
  (Owner Endpoint StepRequest CachedSource Subdivision prepared advance)
open Purelib.Riemann.Paths (PreparedTraceBudget)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {left right current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable (trace : PreparedTraceBudget segment left right)

/-- The original trace fit on this exact supplied subdivision's unchanged request spine. -/
@[expose] def TraceFits (subdivision : Subdivision segment within current owner) : Prop :=
  trace.RequestsFit current subdivision.requests

/-- Physical widths are paid on the same actual requests and original endpoint parameters. -/
@[expose] def Widths (subdivision : Subdivision segment within current owner) : Prop :=
  Subdivision.WidthsFit (widthRequest anchor segment).tolerance current subdivision.requests

/-- Actual terminal factor Reading, retained Samples and derived relation to the original terminal full-cubic Owner. -/
@[expose] def Terminal (subdivision : Subdivision segment within current owner) :=
  Σ last : Reading completed subdivision.endpoint.parameter subdivision.endpoint.inside,
    RequestedSamples (anchor := anchor) last ×
      NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
        last.values.value.name

variable {request : StepRequest} {cached : CachedSource segment current owner request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint (advance segment within current owner request small)}

/-- The current retained request inherits the original trace diameter payment without changing its CachedSource. -/
theorem trace_head (fits : TraceFits trace (.next current owner request cached ordered small remaining)) :
    request.rootDiameter ≤ trace.rootDiameter := by
  unfold TraceFits at fits
  rewrite [Subdivision.requests_next] at fits
  exact fits.1

/-- Original trace fit passes to the identical remaining subdivision at the exact request endpoint. -/
theorem trace_tail (fits : TraceFits trace (.next current owner request cached ordered small remaining)) :
    TraceFits trace remaining := by
  unfold TraceFits at fits ⊢
  rewrite [Subdivision.requests_next] at fits
  exact fits.2.2

/-- The head of the actual original request spine supplies the physical-width payment for this same advance. -/
theorem width_head (paid : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)) :
    (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance := by
  unfold Widths at paid
  rewrite [Subdivision.requests_next] at paid
  exact paid.head

/-- The same remaining original requests keep their width payment at the identical head endpoint. -/
theorem width_tail (paid : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)) :
    Widths (anchor := anchor) remaining := by
  unfold Widths at paid ⊢
  rewrite [Subdivision.requests_next] at paid
  exact paid.tail

-- The retained affine point is an atomic owner index in this dependent cache.
-- Its coordinate formula is not needed by these constructors or projections.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- A cache spine indexed by the exact original subdivision and its already retained source observations.

Each nonempty node retains one entire Step and follows the original remaining
subdivision. Its exact target Reading/Samples and derived next-source relation
are the child indices. The stopped node retains those same final inputs and
their derived original-terminal comparison.
-/
@[expose] def Cache (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (first : Reading completed current.parameter current.inside)
      (_samples : RequestedSamples (anchor := anchor) first)
      (_agreement : SourceAgreement (owner := owner) first)
      (_fits : TraceFits trace subdivision) (_widths : Widths (anchor := anchor) subdivision), Type 1
  | _, _, .stop current owner, _first, _samples, _agreement, _fits, _widths =>
      Terminal (current := current) (owner := owner) (completed := completed) (.stop current owner)
  | _, _, .next current owner request cached _ordered small remaining,
      first, samples, agreement, fits, widths =>
      Σ step : Step (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths),
        let last := Step.last (current := current) (owner := owner) (request := request) (cached := cached)
          (first := first) (firstSamples := samples) (sourceAgreement := agreement) (small := small)
          (trace := trace) (requestFit := trace_head trace fits) (width := width_head widths) step
        let lastSamples := Step.lastSamples (current := current) (owner := owner) (request := request)
          (cached := cached) (first := first) (firstSamples := samples) (sourceAgreement := agreement)
          (small := small) (trace := trace) (requestFit := trace_head trace fits) (width := width_head widths) step
        let nextAgreement := Step.nextAgreement (current := current) (owner := owner) (request := request)
          (cached := cached) (first := first) (firstSamples := samples) (sourceAgreement := agreement)
          (small := small) (trace := trace) (requestFit := trace_head trace fits) (width := width_head widths) step
        Cache trace remaining last lastSamples nextAgreement (trace_tail trace fits) (width_tail widths)

namespace Cache

/-- Complete a stopped original subdivision with the same supplied final Reading/Samples and source comparison. -/
@[expose] def nil (first : Reading completed current.parameter current.inside)
    (samples : RequestedSamples (anchor := anchor) first) (agreement : SourceAgreement (owner := owner) first)
    (fits : TraceFits trace (.stop current owner)) (widths : Widths (anchor := anchor) (.stop current owner)) :
    Cache trace (.stop current owner) first samples agreement fits widths := ⟨first, samples, agreement.symm⟩

/-- Retain one completed actual Step and the cache on the identical original remaining subdivision. -/
@[expose] def cons
    {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (owner := owner) first}
    {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
    {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}
    (step : Step (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths))
    (tail : Cache trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits)
      (width_tail widths)) :
    Cache trace (.next current owner request cached ordered small remaining) first samples agreement fits widths :=
  ⟨step, tail⟩

/-- Read the entire completed Step at the head of this actual original subdivision node. -/
@[expose] def head
    {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (owner := owner) first}
    {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
    {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}
    (cache : Cache trace (.next current owner request cached ordered small remaining) first samples agreement
      fits widths) : Step (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths) := cache.1

/-- Read the exact remaining cache whose source is the identical head target Reading/Samples. -/
@[expose] def tail
    {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (owner := owner) first}
    {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
    {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}
    (cache : Cache trace (.next current owner request cached ordered small remaining) first samples agreement
      fits widths) :
    Cache trace remaining (head trace cache).last (head trace cache).lastSamples (head trace cache).nextAgreement
      (trace_tail trace fits) (width_tail widths) := cache.2

/-- Prepending completed caches retains the identical whole head Step, including both original observation states. -/
theorem cons_head
    {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (owner := owner) first}
    {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
    {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}
    (step : Step (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths))
    (rest : Cache trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits)
      (width_tail widths)) :
    head (ordered := ordered) (fits := fits) (widths := widths) trace
      (cons (ordered := ordered) (fits := fits) (widths := widths) trace step rest) = step := rfl

/-- Prepending completed caches retains the identical tail and its same exact head-target source indices. -/
theorem cons_tail
    {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (owner := owner) first}
    {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
    {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}
    (step : Step (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths))
    (rest : Cache trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits)
      (width_tail widths)) :
    tail (ordered := ordered) (fits := fits) (widths := widths) trace
      (cons (ordered := ordered) (fits := fits) (widths := widths) trace step rest) = rest := rfl

/-- Build comparisons over the original subdivision, querying and sampling each new target only once.

The first Reading/Samples are supplied complete inputs. Every Step stores its
new target and passes that identical data into the recursive tail, preserving
the original CachedSource and actual canonical advanced-owner index. No
replacement subdivision or Source attachment is built. Existing comparison
procedures retain their own execution behavior.
-/
def build (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (first : Reading completed current.parameter current.inside) (samples : RequestedSamples (anchor := anchor) first)
      (agreement : SourceAgreement (owner := owner) first)
      (fits : TraceFits trace subdivision) (widths : Widths (anchor := anchor) subdivision),
      Cache trace subdivision first samples agreement fits widths
  | _, _, .stop _current _owner, first, samples, agreement, fits, widths =>
      nil trace first samples agreement fits widths
  | _, _, .next current owner request cached _ordered small remaining,
      first, samples, agreement, fits, widths =>
      let step := Step.build (current := current) (owner := owner) (request := request) (cached := cached)
        first samples agreement small trace (trace_head trace fits) (width_head widths)
      let tail := build trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits)
        (width_tail widths)
      cons (ordered := _ordered) (fits := fits) (widths := widths) trace step tail
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Read the terminal cache by following the same retained Step spine, without querying or sampling again. -/
@[expose] def terminal (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {first : Reading completed current.parameter current.inside} {samples : RequestedSamples (anchor := anchor) first}
      {agreement : SourceAgreement (owner := owner) first} {fits : TraceFits trace subdivision}
      {widths : Widths (anchor := anchor) subdivision},
      Cache trace subdivision first samples agreement fits widths → Terminal (completed := completed) subdivision
  | _, _, .stop _current _owner, _, _, _, _, _, cache => cache
  | _, _, .next _current _owner _request _cached _ordered _small _remaining, _, _, _, _, _, cache =>
      terminal trace (subdivision := _remaining) cache.2
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

variable {subdivision : Subdivision segment within current owner}
variable {first : Reading completed current.parameter current.inside}
variable {samples : RequestedSamples (anchor := anchor) first}
variable {agreement : SourceAgreement (owner := owner) first} {fits : TraceFits trace subdivision}
variable {widths : Widths (anchor := anchor) subdivision}

/-- Read the complete original final physical factor query retained by the terminal node. -/
@[expose] def last (cache : Cache trace subdivision first samples agreement fits widths) := (terminal trace cache).1

/-- Read the same complete final Samples already used by the last actual advance. -/
@[expose] def lastSamples (cache : Cache trace subdivision first samples agreement fits widths) :
    RequestedSamples (anchor := anchor) (last trace cache) := (terminal trace cache).2.1

/-- Read the derived full-cubic endpoint comparison with both original owners and actual final channel retained. -/
@[expose] def equivalent (cache : Cache trace subdivision first samples agreement fits widths) :
    NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
      (last trace cache).values.value.name := (terminal trace cache).2.2

end Cache

end Reading.Payment.Fold

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
