module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Endpoints
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison.EndpointQueries
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Direct endpoint-query incidence on the same materialized paid Trace

One finite lookup reads the original View at each necessary prefix, then
follows its identical tailTrace. The selected View supplies its source,
moving and retention query comparisons together. No independent fixed-box
budget, comparison bank, trace factory or source/query replay is needed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

namespace PreparedTraceBudget.Trace

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint StepRequest CachedSource)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenteredEdge CenterStates centeredEdges centeredEdges_length edgeOfStep)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}

/-- The three existing original query-comparison functions at one actual centered-parent occurrence.

The result is an existing product, not a stored View bank or another trace
or Owner cache. Its functions consume supplied queries unchanged and retain
the selected original inherited, moving and post-retention Owners.
-/
@[expose] def EndpointComparisons (parent : CenteredEdge curve differential) :=
  Comparison.Cache.SourceComparison parent ×
    Comparison.Cache.EndpointComparison parent × Comparison.Cache.EndpointComparison parent

section Accepted

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}

namespace View

variable (view : View budget current inherited request cached ordered small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep curve differential segment within current inherited request cached ordered small sheet))

/-- Consume this SAME actual View for all endpoint comparisons, retaining its distinct signed occurrences.

Original endpoint equations justify only exact nominal Owner casts.
The original source and retention links derive the signed relations;
coordinate equality is not used to identify two Owners.
-/
def endpointComparisons : EndpointComparisons
    (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet, center⟩ :
      CenteredEdge curve differential) :=
  let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
  let moving : Comparison.Cache.EndpointComparison (⟨edge, center⟩ : CenteredEdge curve differential) :=
    fun query =>
      let equal := congrArg curve.polynomial.eval (view.moving_point.trans edge.point_one.symm)
      let actual := castOwnerParameter equal view.moving.owner
      let compared := view.queryMovingEquivalent query
      have nameEq : ownerName actual = ownerName view.moving.owner :=
        ownerRootName_castOwnerParameter equal view.moving.owner
      ⟨actual, NamedEquivalent.transport rfl nameEq.symm compared⟩
  let kept : Comparison.Cache.EndpointComparison (⟨edge, center⟩ : CenteredEdge curve differential) :=
    fun query =>
      let equal := congrArg curve.polynomial.eval (view.tail_point.trans edge.point_one.symm)
      let actual := castOwnerParameter equal view.tail.owner
      let compared := view.queryRetainedEquivalent query
      have nameEq : ownerName actual = ownerName view.tail.owner :=
        ownerRootName_castOwnerParameter equal view.tail.owner
      ⟨actual, NamedEquivalent.transport rfl nameEq.symm compared⟩
  ⟨fun _query => view.sourceEquivalent sheet, moving, kept⟩

/-- The selected moving-result Owner is the whole original moving suffix Owner under its exact endpoint cast. -/
theorem endpointComparisons_moving_owner_heq
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    HEq ((view.endpointComparisons center).2.1 query).1 view.moving.owner := by
  unfold endpointComparisons
  exact castOwnerParameter_heq _ _

/-- The selected reset-result Owner remains the distinct whole original tail Owner under its exact endpoint cast. -/
theorem endpointComparisons_retained_owner_heq
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      1 (of_decide_eq_true rfl)) :
    HEq ((view.endpointComparisons center).2.2 query).1 view.tail.owner := by
  unfold endpointComparisons
  exact castOwnerParameter_heq _ _

end View

end Accepted

universe u v

namespace View

/-- Consume an actual accepted View and its exact center at that original centered-parent index.

The universally quantified head keeps its whole cached source, request,
fit certificate and materialized Trace. The result family changes no
Owner, subdivision or center; it supplies the operation at that head.
-/
@[expose] def Consumer (result : CenteredEdge curve differential → Type u) :=
  ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits},
    View budget current inherited request cached ordered small remaining fits trace →
      (center : PreparedEdge.CenterState
        (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)) →
      result (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet,
        center⟩ : CenteredEdge curve differential)

/-- A retained payload indexed by the SAME materialized Trace and its original center family.

The family may retain observations and prepared source tails. Its exact
indices prevent a successor from substituting another trace, center bank
or Owner merely because their base coordinates agree.
-/
@[expose] def Payload :=
  ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests},
    Trace budget subdivision fits → CenterStates curve differential sheet subdivision → Type v

/-- One accepted original View returns its head result and the exact payload for that SAME View's tailTrace.

The complete center family and retained input payload are consumed once.
The pair is formed before the original finite branch selection; expensive
new work can stay deferred inside the head result, as with endpoint crops.
-/
@[expose] def ThreadConsumer (payload : Payload (budget := budget) (within := within) (sheet := sheet))
    (result : CenteredEdge curve differential → Type u) :=
  ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits},
    (view : View budget current inherited request cached ordered small remaining fits trace) →
    (centers : CenterStates curve differential sheet
      (Subdivision.next current inherited request cached ordered small remaining)) →
    payload trace centers →
      result (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet,
        centers.1⟩ : CenteredEdge curve differential) × payload view.tailTrace centers.2

end View

/-- Locate one accepted View while threading the SAME retained payload through its ordered tail.

The stop branch has no child. Every visited prefix extracts View once,
forms its callback pair once, then uses the original Fin.cases. A successor
receives that exact pair's following payload and View.tailTrace, preserving
the original branch order and all stationary or repeated occurrences.
-/
def atParentWith (payload : View.Payload (budget := budget) (within := within) (sheet := sheet))
    (result : CenteredEdge curve differential → Type u)
    (consume : View.ThreadConsumer (budget := budget) (within := within) (sheet := sheet) payload result)
    {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision)
    (retained : payload trace centers) :
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
    result ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      payload trace centers →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      result ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt))
    subdivision
    (fun _ _ _ _ _ _ index => Fin.elim0 index)
    (fun current inherited request cached ordered small remaining _fits trace centers retained index =>
      let view := View.build trace
      let selected := consume view centers retained
      Fin.cases
        (motive := fun index => result
          ((centeredEdges curve differential sheet
            (Subdivision.next current inherited request cached ordered small remaining) centers)[index.val]'index.isLt))
        selected.1
        (fun next => atParentWith payload result consume view.tailTrace centers.2 selected.2 next) index)
    fits trace centers retained
termination_by structural subdivision

/-- Locate one actual accepted View with the original ordered finite traversal and consume it once.

The stop branch has no child. At each accepted prefix View.build extracts
the three actual stored suffixes once; a successor receives the identical
view.tailTrace and centers.2. Each visited head constructs its callback
result before the original Fin.cases selects the retained result. Callers
defer query work inside the returned operation; no query or source producer
is replayed by the traversal.
-/
def atParent (result : CenteredEdge curve differential → Type u)
    (consume : View.Consumer (budget := budget) (within := within) (sheet := sheet) result)
    {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision) :
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
    result ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt) :=
  atParentWith (fun {_ _ _ _} _ _ => PUnit.{1}) result
    (fun view centers _ => (consume view centers.1, PUnit.unit)) trace centers PUnit.unit

/-- Locate one accepted child directly in the SAME paid Trace and consume its literal actual View.

Each visited prefix extracts its three original suffixes once. Only the
selected head returns comparison functions; a successor receives the SAME
view.tailTrace and original centers.2. No comparison/reference bank or
second budget is constructed, and no following subtree is selected by a
coordinate or signed label.
-/
def endpointsAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision) :
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
    EndpointComparisons ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt) :=
  atParent EndpointComparisons
    (fun view center => view.endpointComparisons center) trace centers

/-- Retain the literal raw accepted-step index of the SAME centered child, with only its original count transport. -/
@[expose] def rawIndex {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) : Fin subdivision.stepCount :=
  ⟨index.val, Eq.mp (congrArg (fun size : Nat => index.val < size)
    (centeredEdges_length curve differential sheet subdivision centers)) index.isLt⟩

/-- Raw-to-centered bound transport preserves the exact original occurrence coordinate. -/
theorem rawIndex_val {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length) :
    (rawIndex subdivision centers index).val = index.val := by
  rfl

/-- A stopped materialized trace is the SAME literal nil path on its original terminal/source Owner.

The whole trace factory equation supplies this value equality. No parent,
query, comparison or new terminal Owner is fabricated for an empty word.
-/
theorem stop_path {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {fits : budget.RequestsFit current (Subdivision.stop (segment := segment) (within := within)
      current inherited).requests}
    (trace : Trace budget (Subdivision.stop current inherited) fits) :
    trace.path = OwnerPath.nil (segment.pointAt current.parameter) inherited :=
  trace.path_eq

section Readbacks

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable (trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits)
variable (centers : CenterStates curve differential sheet
  (Subdivision.next current inherited request cached ordered small remaining))

/-- The payload lookup returns the complete head result from the SAME actual View and retained input. -/
theorem atParentWith_head (payload : View.Payload (budget := budget) (within := within) (sheet := sheet))
    (result : CenteredEdge curve differential → Type u)
    (consume : View.ThreadConsumer (budget := budget) (within := within) (sheet := sheet) payload result)
    (retained : payload trace centers) :
    atParentWith payload result consume trace centers retained ⟨0, Nat.zero_lt_succ _⟩ =
      (consume (View.build trace) centers retained).1 := by
  unfold atParentWith
  rfl

/-- A successor payload lookup reuses the identical retained tail payload and original View.tailTrace. -/
theorem atParentWith_succ (payload : View.Payload (budget := budget) (within := within) (sheet := sheet))
    (result : CenteredEdge curve differential → Type u)
    (consume : View.ThreadConsumer (budget := budget) (within := within) (sheet := sheet) payload result)
    (retained : payload trace centers)
    (index : Fin (centeredEdges curve differential sheet remaining centers.2).length) :
    atParentWith payload result consume trace centers retained index.succ =
      atParentWith payload result consume (View.build trace).tailTrace centers.2
        (consume (View.build trace) centers retained).2 index := by
  conv_lhs => unfold atParentWith
  rfl

/-- The shared lookup consumes the complete actual head View with its exact original center. -/
theorem atParent_head (result : CenteredEdge curve differential → Type u)
    (consume : View.Consumer (budget := budget) (within := within) (sheet := sheet) result) :
    atParent result consume trace centers ⟨0, Nat.zero_lt_succ _⟩ =
      consume (View.build trace) centers.1 := by
  unfold atParent
  rfl

/-- A successor shared lookup retains the literal View tailTrace and center tail. -/
theorem atParent_succ (result : CenteredEdge curve differential → Type u)
    (consume : View.Consumer (budget := budget) (within := within) (sheet := sheet) result)
    (index : Fin (centeredEdges curve differential sheet remaining centers.2).length) :
    atParent result consume trace centers index.succ =
      atParent result consume (View.build trace).tailTrace centers.2 index := by
  conv_lhs => unfold atParent
  rfl

/-- The head lookup is the complete three-function comparison product on this SAME actual extracted View. -/
theorem endpointsAt_head : endpointsAt trace centers ⟨0, Nat.zero_lt_succ _⟩ =
    (View.build trace).endpointComparisons centers.1 := by
  unfold endpointsAt
  rfl

/-- A successor lookup passes the exact original View tailTrace and identical center tail, without reconstruction. -/
theorem endpointsAt_succ
    (index : Fin (centeredEdges curve differential sheet remaining centers.2).length) :
    endpointsAt trace centers index.succ = endpointsAt (View.build trace).tailTrace centers.2 index := by
  conv_lhs => unfold endpointsAt
  rfl

end Readbacks

end PreparedTraceBudget.Trace

end Purelib.Riemann.Paths.PreparedSubdivisionTrace

end
