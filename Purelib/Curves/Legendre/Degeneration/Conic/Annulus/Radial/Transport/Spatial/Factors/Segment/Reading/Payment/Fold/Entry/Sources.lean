module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Sources
public import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Observation
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Actual source origins at retained cross-segment child occurrences

An original corner Entry keeps its previous complete Reading/Samples.
The first nonempty child still uses those OLD source caches. Later children
read the same retained ordinary Fold tail. A Sum preserves the actual origin
instead of constructing a Reading of another segment's preparation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Entry.Cache

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

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
variable {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- An actual old source origin and its signed child-query relation at an original bounded moving occurrence.

The left branch keeps the previous preparation's exact Reading as an index
and retains its complete old Samples. The right branch keeps an actual
new-segment Reading and its complete Samples. Both comparisons refer to
the literal original child query; the two possible owners stay distinct.
-/
@[expose] def SourceAt {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) :=
  (RequestedSamples (anchor := anchor) first ×
    NamedEquivalent
      (((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt).edge.rootName 0
        ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.baseInside)
      first.values.value.name) ⊕
    (Σ reading : Reading completed
      ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).parameterEdge.left.parameter
      ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).parameterEdge.left.inside,
      RequestedSamples (anchor := anchor) reading ×
        NamedEquivalent
          (((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.rootName 0
            ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.baseInside)
          reading.values.value.name)

/-- Read the original source occurrence without replaying its old Reading, Samples or accepted advance.

A head returns the previous origin unchanged and composes its retained
source agreement with the child's actual CachedSource. A successor reads
only the SAME already completed ordinary Fold tail. An empty subdivision
has no moving source occurrence and cannot fabricate a new origin.
-/
@[expose] def sourceAt :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
      {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision},
      Cache (current := current) (owner := owner) (completed := completed)
        first firstSamples trace subdivision point_eq agreement fits widths →
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) →
      SourceAt (current := current) (owner := owner) (subdivision := subdivision)
        (completed := completed) first centers index
  | _, _, .stop _ _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next current owner request cached ordered small remaining,
      _, agreement, _, _, retained, centers, index =>
      Fin.cases
        (let edge := edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached
           ordered small sheet
         have prepared : NamedEquivalent (ownerRootName owner.parameterNonzero owner)
             (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) := by
           unfold ownerRootName
           exact cached.sourceEquivalent
         Sum.inl ⟨firstSamples, NamedEquivalent.transport edge.rootName_zero_eq_cached.symm rfl
           (prepared.symm.trans agreement.symm)⟩)
        (fun next => Sum.inr
          ⟨Fold.Cache.sourceReadingAt (frame := frame) (basis := basis) (sheet := sheet)
              (completed := completed) trace (subdivision := remaining) retained.2 centers.2 next,
            Fold.Cache.sourceSamplesAt (frame := frame) (basis := basis) (sheet := sheet)
              (completed := completed) trace (subdivision := remaining) retained.2 centers.2 next,
            Fold.Cache.sourceEquivalentAt (frame := frame) (basis := basis) (sheet := sheet)
              (completed := completed) trace (subdivision := remaining) retained.2 centers.2 next⟩) index

variable {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : PreparedSheetContinuation.StepRequest}
variable {cached : PreparedSheetContinuation.CachedSource segment current owner request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current owner request small)}
variable {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
variable {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
variable {fits : TraceFits trace (.next current owner request cached ordered small remaining)}
variable {widths : Widths (anchor := anchor) (.next current owner request cached ordered small remaining)}

/-- The first retained moving source returns the SAME complete previous Samples and cannot select the new origin. -/
theorem sourceAt_zero_samples
    (retained : Cache (current := current) (owner := owner) (completed := completed)
      first firstSamples trace (.next current owner request cached ordered small remaining)
      point_eq agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet
      (.next current owner request cached ordered small remaining)) :
    match sourceAt first firstSamples trace retained centers ⟨0, Nat.zero_lt_succ _⟩ with
    | .inl previous => previous.1 = firstSamples
    | .inr _ => False := by rfl

namespace SourceAt

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

variable {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision}
variable {index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length}

/-- Read the literal physical point of the selected old origin without changing its preparation family. -/
@[expose] def point (origin : SourceAt (completed := completed) first centers index) : Canonical :=
  match origin with
  | .inl _ => previousSegment.pointAt previousTime
  | .inr _ => segment.pointAt
      ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).parameterEdge.left.parameter

/-- Read the identical full-cubic product channel of the actual retained previous or current source Reading. -/
@[expose] def channel (origin : SourceAt (completed := completed) first centers index) : CoherentNamed :=
  match origin with
  | .inl _ => first.values.value
  | .inr current => current.1.values.value

/-- Read the SAME OLD product observation, with its actual original state, request and radius unchanged. -/
@[expose] def product (origin : SourceAt (completed := completed) first centers index) :
    Approximation.Gaussian.Equivalence.Observation.Reading (channel first origin) :=
  match origin with
  | .inl previous => previous.1.samples.product
  | .inr current => current.2.1.samples.product

/-- Read the actual retained signed child-query relation without constructing another comparison or root. -/
@[expose] def equivalent (origin : SourceAt (completed := completed) first centers index) :
    NamedEquivalent
      (((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt).edge.rootName 0
        ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.baseInside)
      (channel first origin).name :=
  match origin with
  | .inl previous => previous.2
  | .inr current => current.2.2

end SourceAt

/-- The certified first source occurrence retains the exact previous original full-product channel.

The actual sourceAt cache is consumed without a new query. A stopped
subdivision has no bounded occurrence; an actual first child uses the
original preceding Reading, not a new-segment Reading of the same point.
-/
theorem sourceAt_first_channel
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
    {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
    {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
    (retained : Cache (current := current) (owner := owner) (completed := completed)
      first firstSamples trace subdivision point_eq agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length)
    (atFirst : index.val = 0) :
    SourceAt.channel first (sourceAt (completed := completed) first firstSamples trace retained centers index) =
      first.values.value := by
  cases subdivision with
  | stop endpoint owner => exact Fin.elim0 index
  | next current owner request cached ordered small remaining =>
      cases index with
      | mk value bounded =>
          cases atFirst
          rfl

/-- The actual first source origin retains the WHOLE preceding product observation with its original state and radius.

The original SourceAt channel is an index of that observation. Heterogeneous
equality preserves the complete original value across this exact channel
readback, including its old factor requests and possible-reading evidence.
-/
theorem sourceAt_first_product_heq
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
    {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
    {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
    (retained : Cache (current := current) (owner := owner) (completed := completed)
      first firstSamples trace subdivision point_eq agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length)
    (atFirst : index.val = 0) :
    HEq (SourceAt.product first
      (sourceAt (completed := completed) first firstSamples trace retained centers index))
      firstSamples.samples.product := by
  cases subdivision with
  | stop endpoint owner => exact Fin.elim0 index
  | next current owner request cached ordered small remaining =>
      cases index with
      | mk value bounded =>
          cases atFirst
          rfl

/-- The actual source-origin getter preserves the literal original moving child's physical point.

At the first child, the stored corner equality identifies the previous
Reading's actual point; it does not create a Reading of the new preparation.
At later children, the original edge-zero law reads the unchanged tail's
source coordinate. No physical equality is inferred from a root name.
-/
theorem sourceAt_point_eq
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
    {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
    {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
    (retained : Cache (current := current) (owner := owner) (completed := completed)
      first firstSamples trace subdivision point_eq agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) :
    SourceAt.point first (sourceAt (completed := completed) first firstSamples trace retained centers index) =
      ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.point 0 := by
  cases subdivision with
  | stop endpoint owner => exact Fin.elim0 index
  | next current owner request cached ordered small remaining =>
      refine Data.Fin.cases_induction ?_ (fun next => ?_) index
      · change previousSegment.pointAt previousTime =
          (edgeOfStep (Fibre.frameCurve frame) basis segment within current owner
            request cached ordered small sheet).point 0
        exact point_eq.trans
          (Riemann.Integration.PreparedSubdivisionModelCore.edgeOfStep_point_zero
            (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet).symm
      · change segment.pointAt
          ((centeredEdges (Fibre.frameCurve frame) basis sheet
          remaining centers.2)[next.val]'next.isLt).parameterEdge.left.parameter =
          ((centeredEdges (Fibre.frameCurve frame) basis sheet remaining centers.2)[next.val]'next.isLt).edge.point 0
        exact (Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_point_zero
          (Fibre.frameCurve frame) basis sheet remaining centers.2 _ (List.getElem_mem next.isLt)).symm

end Reading.Payment.Fold.Entry.Cache

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
