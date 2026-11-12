module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
public import Purelib.Riemann.Integration.PreparedConstantModels.RootPath.Query
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Source/reference alignments of one retained subdivision comparison cache

The original comparison cache already stores every accepted edge, actual trace
view and following reference. This additional finite spine derives each cached
prepared-source comparison once from the original incoming relation and the
same local RootPath. It reuses the actual moving and remaining Owners, including
reserve retention, without another source preparation or advancement.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Topology
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (edgeOfStep)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

/-- A finite spine of derived prepared-source agreements on the SAME stored comparison cache.

Each head keeps the actual cached prepared Owner and the independently
retained incoming reference as separate indices. Its tail follows exactly
the original cache and next-reference occurrence; no path or Owner is copied.
-/
@[expose] def Alignment : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (_retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (_reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter))), Type
  | _, _, .stop _ _, _, _, _, _ => PUnit
  | _, _, .next _ _ _ cached _ _ _, _, _, retained, reference =>
      NamedEquivalent (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner)
        (ownerRootName reference.parameterNonzero reference) ×
      Alignment retained.2.2.2 retained.2.2.1.val
termination_by structural _ _ subdivision _ _ _ _ => subdivision

namespace Alignment

section RetainedAlignmentTypes

/- Compare the actual stored Owner arguments before expanding the original
   operational relation or its root-name constructor. -/
attribute [local irreducible] NamedEquivalent ownerRootName

/-- Derive all actual prepared-source/reference agreements before any interior endpoint callback.

The same RootPath compares the actual moving Owner with its reference.
The actual stationary source/retention links derive both handoffs; exact
stored-source equality retains the unchanged following subdivision. No
reserve-retention factory is repeated by this alignment construction.
-/
def build : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter)))
    (_refines : reference.track.initial.box.Refines referenceOwner.track.initial.box),
    NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
      (ownerRootName reference.parameterNonzero reference) → Alignment retained reference
  | _, _, .stop _ _, _, _, _, _, _, _ => PUnit.unit
  | _, _, .next current inherited _request cached _ _ remaining, _fits, trace, retained, reference, refines, initial =>
      let view := retained.1
      let originalSource := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
      let cachedPrepared : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) :=
        NamedEquivalent.transport (by unfold ownerRootName; rfl)
          ((by unfold ownerRootName; rfl :
            OwnerTraceReadings.ownerName view.source.owner =
              ownerRootName view.source.owner.parameterNonzero view.source.owner).trans view.source_name_eq)
          originalSource
      let head := cachedPrepared.symm.trans initial
      let moved := retained.2.1.finishEquivalent reference refines retained.2.2.1.val retained.2.2.1.refines
        initial view.movingOwner view.movingOwner_eq
      let originalRetention := view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
        (view.tail_point.trans view.moving_point.symm)
      let movingName : ownerRootName view.movingOwner.parameterNonzero view.movingOwner =
          ownerRootName view.moving.owner.parameterNonzero view.moving.owner :=
        PreparedBankRootChains.ownerName_eq_of_heq
          (congrArg curve.polynomial.eval view.moving_point).symm view.movingOwner_heq
      let retention : NamedEquivalent (ownerRootName view.movingOwner.parameterNonzero view.movingOwner)
          (ownerRootName remaining.sourceOwner.parameterNonzero remaining.sourceOwner) :=
        NamedEquivalent.transport
          ((by unfold ownerRootName; rfl :
            OwnerTraceReadings.ownerName view.moving.owner =
              ownerRootName view.moving.owner.parameterNonzero view.moving.owner).trans movingName.symm)
          ((by unfold ownerRootName; rfl :
            OwnerTraceReadings.ownerName view.tail.owner =
              ownerRootName view.tail.owner.parameterNonzero view.tail.owner).trans view.tail_name_eq)
          originalRetention
      let actualRemaining := retention.symm.trans moved
      let tailInitial := Eq.mp (congrArg
        (fun owner => NamedEquivalent (ownerRootName owner.parameterNonzero owner)
          (ownerRootName retained.2.2.1.val.parameterNonzero retained.2.2.1.val))
        remaining.sourceOwner_eq) actualRemaining
      let tail := build retained.2.2.2 retained.2.2.1.val retained.2.2.1.refines tailInitial
      ⟨head, tail⟩
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

end RetainedAlignmentTypes

/-- Derive the actual head-edge interior query comparison from the already cached source alignment.

The SAME actual direct query and retained independent Owner are supplied.
Their initial-box refinements and the cached RootPath derive signed root
agreement; no desired query relation is supplied by the consumer.
-/
def queryEquivalent {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {request : PreparedSheetContinuation.StepRequest}
    {cached : PreparedSheetContinuation.CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
    {retained : Cache curve differential budget sheet second movement
      (Subdivision.next current inherited request cached ordered small remaining) fits trace}
    {reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    (aligned : Alignment retained reference)
    (refines : reference.track.initial.box.Refines referenceOwner.track.initial.box)
    {time : Rational} {inside : Inside time}
    (query : Integration.PreparedConstantModels.PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet) time inside)
    (atTime : Owner (curve.polynomial.eval
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).point time)))
    (atTimeRefines : atTime.track.initial.box.Refines referenceOwner.track.initial.box) :
    NamedEquivalent
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).rootName
        time inside)
      (ownerRootName atTime.parameterNonzero atTime) :=
  retained.2.1.queryEquivalent query reference refines aligned.1 atTime atTimeRefines

end Alignment

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

end
