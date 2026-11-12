module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Cached
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Cached.Primitive
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Queries

/-! # Old View observations compared on GIVEN cached-endpoint child geometry

The actual View supplies its whole original source/moving Owners and old
observations. The GIVEN endpoint queries retain those same Owners. Only
whole-owner/physical-index transports align the old Vertices; the cached
source comparison then consumes the original successful inspection and
already derived root chain, without acquiring any geometry or Owner.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right current : PreparedSheetContinuation.Endpoint}
    {budget : PreparedTraceBudget segment left right} {sheet : Fin 2}
variable {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : PreparedTraceBudget.Trace budget
  (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (view : PreparedTraceBudget.Trace.View
  budget current inherited request cached ordered small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
variable (endpoints : view.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet)
variable (row : Row) {accuracy : AccuracyRequest}
variable (old : Primitive.Spine (row.expression parameter) accuracy trace.path) (parts : view.Observations old)
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}

/-- The exact original edge/center pair for this SAME original accepted moving request. -/
@[expose] def parent : CenteredEdge (Fibre.frameCurve frame) basis :=
  ⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
    center⟩

variable (safe : EndpointSafeBlock (parent center))
variable (inspected : CoveredParents.Inspection (count := count) safe.block.children)
variable (covered : CoveredParents.Inspection.Success inspected)
variable (queryRoots : {value : RootChain safe.block.children
    ((parent center).edge.rootName 0 (parent center).edge.baseInside)
    ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
  value = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe endpoints.queries})
variable (comparisonRequest : AccuracyRequest)

/-- The actual given query-root certificate and source comparison at BOTH actual cached endpoint Owners.

The old Vertex factories are exact whole-owner transports of their
literal moving head. Their original requests and values stay unchanged.
The input root certificate is the actual cached-query geometry factory,
not a desired period/closing relation. Geometry and Targets are GIVEN,
so this constructor neither refines again nor selects an old accuracy.
-/
@[expose] def OnCover :=
  (_roots : {value : {value : RootChain safe.block.children
        ((parent center).edge.rootName 0 (parent center).edge.baseInside)
        ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
      value = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe endpoints.queries} //
    value = queryRoots}) ×
  {value : Points.Cached.Compared (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets)
      row (parent center) endpoints.source endpoints.moving safe inspected covered
      (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val //
    value = Points.Cached.compare (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets)
      row (parent center) endpoints.source endpoints.moving safe inspected covered
      (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val}

/-- Compare the literal old moving observations on the SAME GIVEN child cover and actual cached endpoint query Owners.

Both actual Owners are passed as data through endpointQuery.owner, never
synthesized from TargetVertex's computed transported-owner type. The same
source constructor is shared with the original uncached entry. All input
geometry and endpoint-query caches remain the caller's retained originals.
-/
def compareGivenCover : OnCover (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts safe inspected covered queryRoots comparisonRequest :=
  let first := endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts
  let last := endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts
  let compared := Points.Cached.compare (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row (parent center) endpoints.source endpoints.moving safe inspected covered
    first last comparisonRequest queryRoots.val
  ⟨⟨queryRoots, rfl⟩, ⟨compared, rfl⟩⟩

/-- Compare the original moving observations using the SAME already retained six-channel source product.

Both old Vertices use the original whole-Owner endpoint transports.
The cached-query comparison consumes this supplied source product and
retains its complete original factory without preparing sources again.
-/
def compareGivenPreparedCover
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    OnCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe inspected covered queryRoots comparisonRequest :=
  let first := endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts
  let last := endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts
  let compared := Points.Cached.comparePrepared (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row (parent center) endpoints.source endpoints.moving safe inspected covered
    first last comparisonRequest queryRoots.val shared
  have factory := Points.Cached.comparePrepared_eq_compare (frame := frame) (basis := basis)
    (count := count) (floor := floor) (targets := targets)
    row (parent center) endpoints.source endpoints.moving safe inspected covered
    first last comparisonRequest queryRoots.val shared
  ⟨⟨queryRoots, rfl⟩, ⟨compared, factory⟩⟩

/-- The supplied-source moving comparison has the original complete SAME-Owner and SAME-Vertex factory. -/
theorem compareGivenPreparedCover_eq_compareGivenCover
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    compareGivenPreparedCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe inspected covered queryRoots comparisonRequest shared =
    compareGivenCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe inspected covered queryRoots comparisonRequest := by
  let actual := compareGivenPreparedCover (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts safe inspected covered queryRoots comparisonRequest shared
  let expected := compareGivenCover (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts safe inspected covered queryRoots comparisonRequest
  have same : actual.2 = expected.2 := by
    apply Subtype.ext
    exact Points.Cached.comparePrepared_eq_compare (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets)
      row (parent center) endpoints.source endpoints.moving safe inspected covered
      (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val shared
  exact congrArg (fun result => (⟨⟨queryRoots, rfl⟩, result⟩ :
    OnCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe inspected covered queryRoots comparisonRequest)) same

namespace OnCover

variable {view center endpoints row old parts safe inspected covered queryRoots comparisonRequest}
variable (retained : OnCover (count := count) (floor := floor) (targets := targets)
  view center endpoints row old parts safe inspected covered queryRoots comparisonRequest)

/-- Read the actual cached-query root-chain certificate returned by the original given-geometry stage. -/
@[expose] def queryCertificate : {value : RootChain safe.block.children
    ((parent center).edge.rootName 0 (parent center).edge.baseInside)
    ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
  value = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe endpoints.queries} :=
  retained.1.val

/-- The actual root certificate is the SAME given original cached-query construction outcome. -/
theorem queryCertificate_eq : retained.queryCertificate = queryRoots := retained.1.property

/-- Read the complete SAME-cover comparison on both actual cached endpoint Owners and unchanged old Vertices. -/
@[expose] def compared : Points.Cached.Compared (count := count) (floor := floor) (targets := targets)
    row (parent center) endpoints.source endpoints.moving
    safe inspected covered (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
    (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val :=
  retained.2.val

/-- The actual complete comparison is the shared cached-source construction on those SAME original inputs. -/
theorem compared_eq : retained.compared = Points.Cached.compare
    (count := count) (floor := floor) (targets := targets) row (parent center) endpoints.source endpoints.moving
    safe inspected covered (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
    (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val :=
  retained.2.property

/-- Read the SAME actual selected source-integral samples in original child order. -/
@[expose] def integrals : List Canonical := retained.compared.integrals

/-- Read actual signed endpoint/source residuals from the SAME cached-owner comparison. -/
@[expose] def errors : List Canonical := retained.compared.errors

/-- Read the exact actual refined child count at this original old moving occurrence. -/
@[expose] def childCount : Nat := retained.compared.childCount

/-- Read the derived charge, preserving both actual preselected old endpoint tolerances. -/
@[expose] def charge : Data.Rat.Fraction.Rational := retained.compared.charge

/-- The actual residual count preserves every refined child and the real endpoint comparison. -/
theorem errors_length : retained.errors.length = 2 * retained.childCount + 1 := retained.compared.errors_length

/-- Whole-owner transports preserve the literal old moving increment in the SAME refined-source telescope. -/
theorem sum_errors : Norm.Sum.Basic.gaussianSum retained.errors =
    parts.moving.before.last.value - parts.moving.before.first.value -
      Norm.Sum.Basic.gaussianSum retained.integrals :=
  retained.compared.sum_errors.trans (congrArg₂ (fun first last : Canonical =>
    last - first - Norm.Sum.Basic.gaussianSum retained.integrals)
      (endpoints.sourceVertex_value (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex_value (curve := Fibre.frameCurve frame) old parts))

/-- The SAME actual old requests and new source/join caches pay the full retained norm sum. -/
theorem normSum_le : Norm.Sum.Basic.gaussianNormSqSum retained.errors ≤ retained.charge :=
  retained.compared.normSum_le

end OnCover

/-- The original moving-Owner given-source comparison reads exactly that SAME actual source-model list. -/
theorem compareGivenPreparedCover_integrals
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    (compareGivenPreparedCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe inspected covered queryRoots comparisonRequest shared).integrals =
      Points.Cache.sourceIntegrals row covered.val shared.val := by
  unfold compareGivenPreparedCover OnCover.integrals OnCover.compared
  exact Points.Cached.comparePrepared_integrals (frame := frame) (basis := basis)
    (count := count) (floor := floor) (targets := targets)
    row (parent center) endpoints.source endpoints.moving safe inspected covered
    (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
    (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest queryRoots.val shared

/-- Compare the SAME old moving endpoints on GIVEN zero-width root data, retaining its real requested comparison.

The actual endpoint QueryAt Owner values feed Cache.build explicitly.
No source cell or geometry acquisition is fabricated; both old Vertices
retain their literal original requests through whole-owner transports.
-/
def compareGivenEmpty
    (same : current.parameter = request.endpoint.parameter) (fixedBudget : ParentBudget (parent center).edge)
    (givenRoots : {value : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
        ((parent center).edge.rootName 0 (parent center).edge.baseInside)
        ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
      value = PrimitiveCover.stationaryRootsFromQueries (parent center) endpoints.queries same fixedBudget})
    (comparisonRequest : AccuracyRequest) :
    Points.Cached.EmptyCompared (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row (parent center) endpoints.source endpoints.moving
      (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest same givenRoots.val :=
  let first := endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts
  let last := endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts
  Points.Cached.compareEmpty (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row (parent center) endpoints.source endpoints.moving first last comparisonRequest same givenRoots.val

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

end
