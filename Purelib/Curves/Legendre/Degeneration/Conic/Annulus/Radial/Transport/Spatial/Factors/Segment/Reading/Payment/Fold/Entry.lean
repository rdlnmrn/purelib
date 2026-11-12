module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Entry

import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence.Observation

/-! # Original endpoint observations carried across a physical edge corner

The original subdivision is matched once at entry. A stopped subdivision
keeps its previous physical Reading and complete Samples as the actual
output origin. A nonempty subdivision constructs one cross-segment Step,
then passes its exact target caches into the original same-segment tail fold.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
namespace Reading.Payment.Fold.Entry

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
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
variable {budgets previousBudgets : Budgets anchor}
variable {start finish previousStart previousFinish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  previousStart previousFinish}
variable {within : segment.WithinAmbient} {previousWithin : previousSegment.WithinAmbient}
variable {completed : Segment budgets segment within}
variable {previousCompleted : Segment previousBudgets previousSegment previousWithin}
variable {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
variable (first : Reading previousCompleted previousTime previousInside)
variable (firstSamples : RequestedSamples (anchor := anchor) first)
variable {left right : Endpoint} (trace : PreparedTraceBudget segment left right)

-- Keep original affine coordinates atomic in dependent comparison/cache indices.
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
-- Owner names are retained indices; this cache does not inspect root-state histories.
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original first cross-segment Step and the identical same-segment tail, or an unchanged stationary entry.

The complete previous Reading/Samples remain input indices. The nonempty
case uses the actual original request, CachedSource and canonical advance;
its exact target Reading/Samples and derived relation index the retained tail.
-/
@[expose] def Cache (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (_point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
      (_agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner))
      (_fits : TraceFits trace subdivision) (_widths : Widths (anchor := anchor) subdivision), Type 1
  | _, _, .stop _current _owner, _point_eq, _agreement, _fits, _widths => PUnit
  | _, _, .next current owner request cached _ordered small remaining,
      point_eq, agreement, fits, widths =>
      Σ step : Step.Entry.Cache (completed := completed) (current := current) (owner := owner)
          (request := request) (cached := cached) first firstSamples point_eq agreement small trace
          (trace_head trace fits) (width_head widths),
        Fold.Cache (completed := completed) (current := request.endpoint)
          (owner := advance segment within current owner request small)
          trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits) (width_tail widths)

variable {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}

/-- Actual terminal data retain either the preceding original samples or the newly queried tail's full terminal cache.

The first alternative retains a physical endpoint equality and exact whole
Samples identity. It never constructs a Reading of the separate preparation.
The second alternative is the original Fold.Terminal, retaining its actual
new-segment Reading, Samples and derived full-cubic endpoint comparison.
-/
@[expose] def Exit (subdivision : Subdivision segment within current owner) :=
  { retained : RequestedSamples (anchor := anchor) first ×
      NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
        first.values.value.name //
      previousSegment.pointAt previousTime = segment.pointAt subdivision.endpoint.parameter ∧
        retained.1 = firstSamples } ⊕
    Terminal (current := current) (owner := owner) (completed := completed) subdivision

namespace Cache

/-- Cache the actual first target once, then delegate the unchanged remaining subdivision to its original fold. -/
def build (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
      (agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner))
      (fits : TraceFits trace subdivision) (widths : Widths (anchor := anchor) subdivision),
      Cache (completed := completed) first firstSamples trace subdivision point_eq agreement fits widths
  | _, _, .stop _current _owner, _point_eq, _agreement, _fits, _widths => PUnit.unit
  | _, _, .next current owner request cached _ordered small remaining,
      point_eq, agreement, fits, widths =>
      let step := Step.Entry.Cache.build (completed := completed) (current := current) (owner := owner)
        (request := request) (cached := cached) first firstSamples point_eq agreement small trace
        (trace_head trace fits) (width_head widths)
      let following := Fold.Cache.build (completed := completed) (current := request.endpoint)
        (owner := advance segment within current owner request small)
        trace remaining step.last step.lastSamples step.nextAgreement (trace_tail trace fits) (width_tail widths)
      ⟨step, following⟩

/-- Read the actual terminal cache without querying either endpoint or replacing its original observation owner. -/
@[expose] def output (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
      {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision},
      Cache (completed := completed) first firstSamples trace subdivision point_eq agreement fits widths →
        Exit (completed := completed) first firstSamples subdivision
  | _, _, .stop _current _owner, point_eq, agreement, _, _, _cache =>
      .inl ⟨⟨firstSamples, agreement.symm⟩, point_eq, rfl⟩
  | _, _, .next _current _owner _request _cached _ordered _small remaining, _, _, _, _, cache =>
      .inr (Fold.Cache.terminal (completed := completed) trace (subdivision := remaining) cache.2)

/-- Stopping at entry returns the identical preceding Samples and its original channel comparison. -/
theorem output_stop
    (point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter)
    (agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner))
    (fits : TraceFits (within := within) trace (.stop current owner))
    (widths : Widths (anchor := anchor) (within := within) (.stop current owner)) :
    output (completed := completed) first firstSamples trace
      (subdivision := .stop current owner) (point_eq := point_eq) (agreement := agreement)
      (fits := fits) (widths := widths)
      (build (completed := completed) first firstSamples trace (.stop current owner) point_eq agreement fits widths) =
        .inl ⟨⟨firstSamples, agreement.symm⟩, point_eq, rfl⟩ := rfl

variable {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
variable {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
variable {request : StepRequest} {cached : CachedSource segment current owner request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (prepared segment current owner request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint (advance segment within current owner request small)}
variable {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
variable {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}

/-- Retain an already completed cross-segment head and identical original tail without rebuilding either. -/
@[expose] def cons
    (step : Step.Entry.Cache (completed := completed) (current := current) (owner := owner)
      (request := request) (cached := cached) first firstSamples point_eq agreement small trace
      (trace_head trace fits) (width_head widths))
    (following : Fold.Cache (completed := completed) (current := request.endpoint)
      (owner := advance segment within current owner request small) trace remaining
      step.last step.lastSamples step.nextAgreement (trace_tail trace fits) (width_tail widths)) :
    Cache (completed := completed) first firstSamples trace (.next current owner request cached ordered small remaining)
      point_eq agreement fits widths := ⟨step, following⟩

/-- Read the original completed first cross-segment Step from the same retained subdivision head. -/
@[expose] def head
    (cache : Cache (completed := completed) first firstSamples trace
      (.next current owner request cached ordered small remaining)
      point_eq agreement fits widths) :
    Step.Entry.Cache (completed := completed) (current := current) (owner := owner)
      (request := request) (cached := cached) first firstSamples point_eq agreement small trace
      (trace_head trace fits) (width_head widths) :=
  cache.1

/-- Read the identical original tail fold indexed by the first Step's unchanged target Reading and Samples. -/
@[expose] def tail
    (cache : Cache (completed := completed) first firstSamples trace
      (.next current owner request cached ordered small remaining)
      point_eq agreement fits widths) :
    Fold.Cache (completed := completed) (current := request.endpoint)
      (owner := advance segment within current owner request small) trace remaining
      (head first firstSamples trace cache).last (head first firstSamples trace cache).lastSamples
      (head first firstSamples trace cache).nextAgreement (trace_tail trace fits) (width_tail widths) := cache.2

/-- The completed-cache constructor keeps the identical whole first cross-segment Step. -/
theorem cons_head
    (step : Step.Entry.Cache (completed := completed) (current := current) (owner := owner)
      (request := request) (cached := cached) first firstSamples point_eq agreement small trace
      (trace_head trace fits) (width_head widths))
    (following : Fold.Cache (completed := completed) (current := request.endpoint)
      (owner := advance segment within current owner request small) trace remaining
      step.last step.lastSamples step.nextAgreement (trace_tail trace fits) (width_tail widths)) :
    head (ordered := ordered) (fits := fits) (widths := widths) first firstSamples trace
      (cons (ordered := ordered) (fits := fits) (widths := widths) first firstSamples trace step following) =
        step := rfl

/-- The completed-cache constructor keeps the identical original tail indexed by that exact target. -/
theorem cons_tail
    (step : Step.Entry.Cache (completed := completed) (current := current) (owner := owner)
      (request := request) (cached := cached) first firstSamples point_eq agreement small trace
      (trace_head trace fits) (width_head widths))
    (following : Fold.Cache (completed := completed) (current := request.endpoint)
      (owner := advance segment within current owner request small) trace remaining
      step.last step.lastSamples step.nextAgreement (trace_tail trace fits) (width_tail widths)) :
    tail (ordered := ordered) (fits := fits) (widths := widths) first firstSamples trace
      (cons (ordered := ordered) (fits := fits) (widths := widths) first firstSamples trace step following) =
        following := rfl

end Cache

namespace Exit

variable {first : Reading previousCompleted previousTime previousInside}
variable {firstSamples : RequestedSamples (anchor := anchor) first}
variable {subdivision : Subdivision segment within current owner}

/-- Read the unchanged full-product channel of the actual retained output Reading. -/
@[expose] def channel (output : Exit (completed := completed) first firstSamples subdivision) : CoherentNamed :=
  match output with
  | .inl _retained => first.values.value
  | .inr retained => retained.1.values.value

/-- Read the original channel's complete actual product observation, preserving its process and paired state. -/
@[expose] def observed (output : Exit (completed := completed) first firstSamples subdivision) :
    Equivalence.Observation.Reading output.channel :=
  match output with
  | .inl retained => retained.val.1.samples.product
  | .inr retained => retained.2.1.samples.product

/-- The original subdivision's full-cubic terminal Owner agrees with the actual retained output channel. -/
@[expose] def equivalent (output : Exit (completed := completed) first firstSamples subdivision) :
    NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
      output.channel.name :=
  match output with
  | .inl retained => retained.val.2
  | .inr retained => retained.2.2

/-- Read the actual physical coordinate of the retained Reading without changing its preparation origin. -/
@[expose] def point (output : Exit (completed := completed) first firstSamples subdivision) : Canonical :=
  match output with
  | .inl _retained => previousSegment.pointAt previousTime
  | .inr _retained => segment.pointAt subdivision.endpoint.parameter

/-- Both original output alternatives have the exact physical endpoint of this same retained subdivision. -/
theorem point_eq (output : Exit (completed := completed) first firstSamples subdivision) :
    output.point = segment.pointAt subdivision.endpoint.parameter := by
  cases output with
  | inl retained => exact retained.property.1
  | inr _retained => rfl

/-- A stationary entry retains the same entire original Samples cache, including both actual factor observations. -/
theorem stationary_samples_eq
    (retained : { value : RequestedSamples (anchor := anchor) first ×
        NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
          first.values.value.name //
        previousSegment.pointAt previousTime = segment.pointAt subdivision.endpoint.parameter ∧
          value.1 = firstSamples }) : retained.val.1 = firstSamples := retained.property.2

end Exit

end Reading.Payment.Fold.Entry
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
