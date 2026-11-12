module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Cached.Completed
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Append
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Actual old heads and cached endpoint refinement at one retained occurrence

One View and its three original observation splits are read from the GIVEN
materialized trace. Both actual query records and the complete source
refinement outcome are retained once. The next trace and old observation
are the original stored suffix, not a canonical path execution.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace renaming View -> TraceView
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
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
variable (center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
variable (row : Row) {accuracy : AccuracyRequest}
variable (old : Primitive.Spine (row.expression parameter) accuracy trace.path)
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}
variable (diameter : Fraction.Rational) (positive : 0 < diameter) (comparisonRequest : AccuracyRequest)

namespace Entry

/-- Original View, endpoint queries and actual rooted child geometry before any primitive observation.

The exact existing dependent products retain each complete cache with its
factory. The primitive-cover acquisition keeps all original mesh, cover
and signed-root owners while source targets and old accuracy are absent.
-/
@[expose] def Geometry :=
  Σ view : {value : TraceView
      budget current inherited request cached ordered small remaining fits trace //
    value = TraceView.build trace},
  Σ endpoints : {value : view.val.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet //
    value = TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) view.val sheet},
  {value : PrimitiveCover.Acquisition (count := count) (parent center) endpoints.val.queries diameter positive //
    value = PrimitiveCover.Acquisition.build (count := count)
      (parent center) endpoints.val.queries diameter positive}

namespace Geometry

/-- Retain this actual old View, both endpoint Owners and complete child geometry before choosing requests. -/
def build : Geometry (trace := trace) (count := count) center diameter positive :=
  let view : {value : TraceView
      budget current inherited request cached ordered small remaining fits trace //
    value = TraceView.build trace} :=
    ⟨TraceView.build trace, rfl⟩
  let endpoints : {value : view.val.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet //
    value = TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) view.val sheet} :=
    ⟨TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) view.val sheet, rfl⟩
  let acquisition : {value : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.val.queries diameter positive //
    value = PrimitiveCover.Acquisition.build (count := count)
      (parent center) endpoints.val.queries diameter positive} :=
    ⟨PrimitiveCover.Acquisition.build (count := count)
      (parent center) endpoints.val.queries diameter positive, rfl⟩
  ⟨view, endpoints, acquisition⟩

variable {center diameter positive}
variable (retained : Geometry (trace := trace) (count := count) center diameter positive)

/-- Read the complete View on the same original supplied raw Trace. -/
@[expose] def view : TraceView
    budget current inherited request cached ordered small remaining fits trace := retained.1.val

/-- The retained View has the original whole View factory. -/
theorem view_eq : retained.view = TraceView.build trace := retained.1.property

/-- Read both original cached endpoint queries and their actual Owner records. -/
@[expose] def endpoints : retained.view.EndpointQueries
    (curve := Fibre.frameCurve frame) (differential := basis) sheet := retained.2.1.val

/-- The same endpoint pair has its original complete query-cache factory. -/
theorem endpoints_eq : retained.endpoints = TraceView.EndpointQueries.build
    (curve := Fibre.frameCurve frame) (differential := basis) retained.view sheet := retained.2.1.property

/-- Read the original complete stationary or refined primitive-cover outcome. -/
@[expose] def acquisition : PrimitiveCover.Acquisition (count := count)
    (parent center) retained.endpoints.queries diameter positive := retained.2.2.val

/-- The actual acquired geometry has its complete original endpoint-query factory. -/
theorem acquisition_eq : retained.acquisition = PrimitiveCover.Acquisition.build (count := count)
    (parent center) retained.endpoints.queries diameter positive := retained.2.2.property

/-- Read the actual original following Trace without an observation or a canonical trace construction. -/
@[expose] def nextTrace : PreparedTraceBudget.Trace budget remaining fits.2.2 := retained.view.tailTrace

/-- Count the literal actual children before selecting primitive or source requests. -/
@[expose] def childCount : Nat := retained.acquisition.childCount

/-- The complete row-independent numeric source bank on this SAME retained geometry acquisition. -/
@[expose] def Sources := Completed.Sources (count := count) (floor := floor) (targets := targets)
  retained.view center retained.endpoints diameter positive retained.acquisition

namespace Sources

/-- Prepare all six physical source channels once on this SAME geometry before primitive observations. -/
def build : Sources (count := count) (floor := floor) (targets := targets) retained :=
  Completed.Sources.build (count := count) (floor := floor) (targets := targets)
    retained.view center retained.endpoints diameter positive retained.acquisition

/-- Read one literal numerical source-cell list from the GIVEN shared bank and unchanged geometric outcome. -/
@[expose] def cells (channel : Fin 6)
    (shared : Sources (count := count) (floor := floor) (targets := targets) retained) :
    List CellModel :=
  Completed.Sources.cells (count := count) (floor := floor) (targets := targets)
    retained.view center retained.endpoints diameter positive channel retained.acquisition shared

/-- Read the actual row-model integral list from the SAME given geometry and full source bank. -/
@[expose] def integrals (row : Row)
    (shared : Sources (count := count) (floor := floor) (targets := targets) retained) : List Canonical :=
  Completed.Sources.integrals (count := count) (floor := floor) (targets := targets)
    retained.view center retained.endpoints diameter positive row retained.acquisition shared

/-- The actual row sample is the exact original combination of the SAME six retained numerical source lists. -/
theorem combine_eq (row : Row)
    (shared : Sources (count := count) (floor := floor) (targets := targets) retained) :
    gaussianSum (integrals (count := count) (floor := floor) (targets := targets) retained row shared) =
      Row.combine parameter row (fun channel =>
        (PathModel.mk (cells (count := count) (floor := floor) (targets := targets)
          retained channel shared)).integralSample) :=
  Completed.Sources.combine_eq (count := count) (floor := floor) (targets := targets)
    retained.view center retained.endpoints diameter positive row retained.acquisition shared

end Sources

end Geometry

end Entry

/-- One original pre-observation geometry cache and the actual old Head/source comparison on those same owners.

The complete original View, endpoint queries and acquisition are retained
once. Both old stationary roles remain around the actual moving-source
comparison. The numerical factory consumes the given geometry directly;
it does not execute a second primitive-cover acquisition.
-/
@[expose] def Entry :=
  Σ geometry : Entry.Geometry (trace := trace) (count := count) center diameter positive,
  Σ parts : {value : geometry.view.Observations old // value = geometry.view.observations old},
  {value : Completed (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest //
    value = Completed.fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
        geometry.acquisition}

namespace Entry

/-- Attach source comparisons to already retained geometry and actual old Head splits without preparing either again. -/
private def fromParts (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (parts : {value : geometry.view.Observations old // value = geometry.view.observations old}) :
    Entry (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest :=
  let completed := Completed.fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
    geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest geometry.acquisition
  ⟨geometry, parts, ⟨completed, rfl⟩⟩

/-- Split the given old observations once and compare on the same geometry retained before those observations.

The old Spine and its original request stay unchanged. This operation
reads its three original Heads once and consumes the given View, endpoint
queries, checked mesh, cover and root chain without executing their factories.
-/
def fromGeometry (geometry : Geometry (trace := trace) (count := count) center diameter positive) :
    Entry (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest :=
  let parts : {value : geometry.view.Observations old // value = geometry.view.observations old} :=
    ⟨geometry.view.observations old, rfl⟩
  fromParts (count := count) (floor := floor) (targets := targets)
    center row old diameter positive comparisonRequest geometry parts

/-- Split only the GIVEN row observations and consume the SAME retained six-channel source bank.

The actual View, both cached endpoint queries and primitive-cover outcome
remain unchanged. This operation runs no geometry, source preparation or
query factory; both old stationary roles survive in the original Entry.
-/
def fromSources (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets) geometry) :
    Entry (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest :=
  let parts : {value : geometry.view.Observations old // value = geometry.view.observations old} :=
    ⟨geometry.view.observations old, rfl⟩
  let completed : {value : Completed (count := count) (floor := floor) (targets := targets)
        geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest //
      value = Completed.fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
        geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
          geometry.acquisition} :=
    ⟨Completed.fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
      geometry.acquisition shared,
    Completed.fromSources_eq_fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
      geometry.acquisition shared⟩
  ⟨geometry, parts, completed⟩

/-- The given-source row retains the complete original Entry factory on these SAME geometry and observations. -/
theorem fromSources_eq_fromGeometry
    (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets) geometry) :
    fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry shared =
    fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry := by
  let parts : {value : geometry.view.Observations old // value = geometry.view.observations old} :=
    ⟨geometry.view.observations old, rfl⟩
  let actual := Completed.fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
    geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
    geometry.acquisition shared
  let expected := Completed.fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
    geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest geometry.acquisition
  have actualEq : actual = expected :=
    Completed.fromSources_eq_fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest
      geometry.acquisition shared
  have same : (⟨actual, actualEq⟩ : {value : Completed (count := count) (floor := floor) (targets := targets)
      geometry.view center geometry.endpoints row old parts.val diameter positive comparisonRequest //
      value = expected}) = ⟨expected, rfl⟩ := by
    apply Subtype.ext
    exact actualEq
  exact congrArg (fun result => (⟨geometry, parts, result⟩ :
    Entry (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest)) same

/-- Compare three independent old row Spines on ONE given geometry and complete six-channel source bank.

Every row's old observation heads are read once. The same supplied source
product is forwarded to all three source workers; no six-channel source
preparation is executed by this multirow consumer.
-/
def rowsFromSources (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : (row : Row) → Primitive.Spine (row.expression parameter) accuracy trace.path) :
    Entry (count := count) (floor := floor) (targets := targets)
        center (Row.connection 0) (observed (Row.connection 0)) diameter positive comparisonRequest ×
      Entry (count := count) (floor := floor) (targets := targets)
        center (Row.connection 1) (observed (Row.connection 1)) diameter positive comparisonRequest ×
      Entry (count := count) (floor := floor) (targets := targets)
        center Row.scalar (observed Row.scalar) diameter positive comparisonRequest :=
  let zero := fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
    center (Row.connection 0) (observed (Row.connection 0)) diameter positive comparisonRequest geometry shared
  let one := fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
    center (Row.connection 1) (observed (Row.connection 1)) diameter positive comparisonRequest geometry shared
  let scalar := fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
    center Row.scalar (observed Row.scalar) diameter positive comparisonRequest geometry shared
  ⟨zero, one, scalar⟩

/-- Retain the original producer order while sharing the given-geometry numerical operation.

The convenience entry reads the View, splits the old Heads, retains the
endpoint queries, and acquires geometry in that original order. The shared
worker then consumes those same caches. A pre-observation client instead
calls Geometry.build before observing, followed by fromGeometry afterward.
-/
def build : Entry (count := count) (floor := floor) (targets := targets)
    center row old diameter positive comparisonRequest :=
  let view : {value : TraceView
      budget current inherited request cached ordered small remaining fits trace //
    value = TraceView.build trace} :=
    ⟨TraceView.build trace, rfl⟩
  let parts : {value : view.val.Observations old // value = view.val.observations old} :=
    ⟨view.val.observations old, rfl⟩
  let endpoints : {value : view.val.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet //
    value = TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) view.val sheet} :=
    ⟨TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) view.val sheet, rfl⟩
  let acquisition : {value : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.val.queries diameter positive //
    value = PrimitiveCover.Acquisition.build (count := count)
      (parent center) endpoints.val.queries diameter positive} :=
    ⟨PrimitiveCover.Acquisition.build (count := count)
      (parent center) endpoints.val.queries diameter positive, rfl⟩
  let geometry : Geometry (trace := trace) (count := count) center diameter positive := ⟨view, endpoints, acquisition⟩
  fromParts (count := count) (floor := floor) (targets := targets)
    center row old diameter positive comparisonRequest geometry parts

/-- The given-geometry route recovers the original whole Entry factory when its actual geometry factory is retained.

This is a proof about the same selected caches and pure operation values.
The geometry factory occurs only in this erased equality; the given-geometry
producer never executes it to obtain a second cache.
-/
theorem fromGeometry_eq_build (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (factory : geometry = Geometry.build (trace := trace) (count := count) center diameter positive) :
    fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry =
    build (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest := by
  cases factory
  rfl

variable {center row old diameter positive comparisonRequest}
variable (kept : Entry (count := count) (floor := floor) (targets := targets)
  center row old diameter positive comparisonRequest)

/-- Read the same complete geometry cache, acquired independently of the old primitive request. -/
@[expose] def geometry : Geometry (trace := trace) (count := count) center diameter positive := kept.1

/-- The given-geometry constructor retains the complete supplied geometry cache unchanged. -/
theorem fromGeometry_geometry (geometry : Geometry (trace := trace) (count := count) center diameter positive) :
    (fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry).geometry = geometry := by
  unfold fromGeometry fromParts Entry.geometry
  rfl

/-- Read the actual retained three-suffix View of the GIVEN original materialized trace. -/
@[expose] def view : TraceView
    budget current inherited request cached ordered small remaining fits trace := kept.1.view

/-- Read the SAME three old Head observations, including both actual stationary comparisons. -/
@[expose] def parts : kept.view.Observations old := kept.2.1.val

/-- Read both actual old endpoint-query Owners without evaluating any coarse continuation. -/
@[expose] def endpoints : kept.view.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet :=
  kept.1.endpoints

/-- Read the SAME retained checked geometry, source caches, Point observations and requested joins. -/
@[expose] def completed : Completed (count := count) (floor := floor) (targets := targets)
    kept.view center kept.endpoints row old kept.parts diameter positive comparisonRequest := kept.2.2.val

/-- The actual View was read from the SAME original trace. -/
theorem view_eq : kept.view = TraceView.build trace := kept.1.view_eq

/-- The three old Head observations share the SAME actual View and unchanged old Spine. -/
theorem parts_eq : kept.parts = kept.view.observations old := kept.2.1.property

/-- The endpoint-query pair was retained from those SAME actual source/moving Owners. -/
theorem endpoints_eq : kept.endpoints =
    TraceView.EndpointQueries.build
      (curve := Fibre.frameCurve frame) (differential := basis) kept.view sheet := kept.1.endpoints_eq

/-- The complete source refinement has its exact given-geometry factory on these same original caches. -/
theorem completed_eq : kept.completed = Completed.fromGeometry (trace := trace) (count := count)
  (floor := floor) (targets := targets)
    kept.view center kept.endpoints row old kept.parts diameter positive comparisonRequest kept.1.acquisition :=
  kept.2.2.property

/-- Read the original following materialized Trace through its whole retained suffix equality. -/
@[expose] def nextTrace : PreparedTraceBudget.Trace budget remaining fits.2.2 := kept.view.tailTrace

/-- The given-geometry constructor keeps the literal original following Trace stored before observations. -/
theorem fromGeometry_nextTrace (geometry : Geometry (trace := trace) (count := count) center diameter positive) :
    (fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry).nextTrace = geometry.nextTrace := by
  unfold fromGeometry fromParts nextTrace view Geometry.nextTrace Geometry.view
  rfl

/-- The supplied-source row keeps the SAME following Trace retained before any row observation. -/
theorem fromSources_nextTrace
    (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets) geometry) :
    (fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry shared).nextTrace = geometry.nextTrace :=
  (congrArg (fun value : Entry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest => value.nextTrace)
    (fromSources_eq_fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry shared)).trans (fromGeometry_nextTrace geometry)

/-- Read the identical old observation suffix at that original following trace, changing only exact whole indices. -/
@[expose] def nextObserved : Primitive.Spine (row.expression parameter) accuracy kept.nextTrace.path :=
  kept.parts.following

/-- The original whole old terminal Vertex survives the actual three-head extraction. -/
theorem nextObserved_last : kept.nextObserved.last = old.last := kept.parts.following_last

/-- Read actual source samples in the SAME checked child order. -/
@[expose] def integrals : List Canonical := kept.completed.integrals

/-- The actual row Entry reads precisely its SAME given source-bank integral list, retaining all endpoint caches. -/
theorem fromSources_integrals
    (geometry : Geometry (trace := trace) (count := count) center diameter positive)
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets) geometry) :
    (fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry shared).integrals =
      Geometry.Sources.integrals (count := count) (floor := floor) (targets := targets) geometry row shared := by
  unfold fromSources integrals completed
  exact Completed.fromSources_integrals (count := count) (floor := floor) (targets := targets)
    (view := geometry.view) (center := center) (endpoints := geometry.endpoints) (row := row) (old := old)
    (parts := geometry.view.observations old) (diameter := diameter) (positive := positive)
    (comparisonRequest := comparisonRequest) geometry.acquisition shared

/-- Read the SAME retained child count, keeping zero for an empty inner refinement. -/
@[expose] def childCount : Nat := kept.completed.childCount

/-- The given-geometry entry has exactly the child count computed before the old observation request was selected. -/
theorem fromGeometry_childCount (geometry : Geometry (trace := trace) (count := count) center diameter positive) :
    (fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      center row old diameter positive comparisonRequest geometry).childCount = geometry.childCount := by
  change (Completed.fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
    geometry.view center geometry.endpoints row old (geometry.view.observations old)
    diameter positive comparisonRequest geometry.acquisition).childCount = geometry.acquisition.childCount
  exact Completed.fromGeometry_childCount (count := count) (floor := floor) (targets := targets)
    (view := geometry.view) (center := center) (endpoints := geometry.endpoints) (row := row) (old := old)
    (parts := geometry.view.observations old) (diameter := diameter) (positive := positive)
    (comparisonRequest := comparisonRequest) geometry.acquisition

/-- Both old stationary roles remain around actual moving residuals, including stationary or repeated requests. -/
@[expose] def errors : List Canonical :=
  kept.parts.source.before.2.2.1.jump ::
    (kept.completed.errors ++ [kept.parts.reset.before.2.2.1.jump])

/-- The actual local source charge is augmented by BOTH unchanged original stationary-request allowances. -/
@[expose] def charge : Fraction.Rational :=
  accuracy.tolerance + (kept.completed.charge + accuracy.tolerance)

/-- The real zero-child comparison and both old stationary roles give two residuals per child plus three. -/
theorem errors_length : kept.errors.length = 2 * kept.childCount + 3 := by
  have localCount := kept.completed.errors_length
  have appendCount := Data.List.Append.length_append kept.completed.errors
    [kept.parts.reset.before.2.2.1.jump]
  change (kept.completed.errors ++ [kept.parts.reset.before.2.2.1.jump]).length + 1 =
    2 * kept.completed.childCount + 3
  calc
    _ = kept.completed.errors.length + 1 + 1 := congrArg (fun length : Nat => length + 1) appendCount
    _ = (2 * kept.completed.childCount + 1) + 1 + 1 :=
      congrArg (fun length : Nat => length + 1 + 1) localCount
    _ = _ := by omega0

/-- Both old stationary comparisons and actual refined source errors give the exact next-source increment telescope.

Only exact old Head shared/first laws identify scalar readings. Coordinates
supply stationarity of the two original links; their existing comparisons,
not coordinate equality, pay the two jumps.
-/
theorem sum_errors : Norm.Sum.Basic.gaussianSum kept.errors =
    kept.nextObserved.first.value - old.first.value - Norm.Sum.Basic.gaussianSum kept.integrals := by
  have source := kept.parts.source.before.2.2.1.jump_eq_of_same kept.view.source_point.symm
  have reset := kept.parts.reset.before.2.2.1.jump_eq_of_same
    (kept.view.moving_point.trans kept.view.tail_point.symm)
  have firstValue := congrArg Primitive.Vertex.value kept.parts.source.first_eq
  have movingFirst := (congrArg Primitive.Vertex.value kept.parts.moving.first_eq).trans
    (congrArg Primitive.Vertex.value kept.parts.source.shared)
  have resetFirst := (congrArg Primitive.Vertex.value kept.parts.reset.first_eq).trans
    (congrArg Primitive.Vertex.value kept.parts.moving.shared)
  have followingFirst := kept.parts.following_first_value.trans
    (congrArg Primitive.Vertex.value kept.parts.reset.shared)
  have sourceJump := source.trans (congrArg (fun first : Canonical =>
    kept.parts.source.before.last.value - first) firstValue)
  have movingSum := kept.completed.sum_errors.trans (congrArg (fun first : Canonical =>
    kept.parts.moving.before.last.value - first - Norm.Sum.Basic.gaussianSum kept.completed.integrals) movingFirst)
  have resetJump := reset.trans (congrArg₂ (fun first last : Canonical => last - first)
    resetFirst followingFirst.symm)
  have scalar (first second third last integral : Canonical) :
      (second - first) + ((third - second - integral) + (last - third)) = last - first - integral := by ring1
  have tail := congrArg₂ (fun moving closing : Canonical => moving + closing) movingSum
    ((Basic.add_zero kept.parts.reset.before.2.2.1.jump).trans resetJump)
  have added := congrArg₂ (fun first last : Canonical => first + last) sourceJump tail
  change kept.parts.source.before.2.2.1.jump + Norm.Sum.Basic.gaussianSum
    (kept.completed.errors ++ [kept.parts.reset.before.2.2.1.jump]) = _
  exact (congrArg (fun total : Canonical => kept.parts.source.before.2.2.1.jump + total)
    (Norm.Sum.Basic.gaussianSum_append _ _)).trans (added.trans (scalar _ _ _ _ _))

/-- Actual old stationary caches and unchanged mixed-request source comparisons pay their full finite norm sum. -/
theorem normSum_le : Norm.Sum.Basic.gaussianNormSqSum kept.errors ≤ kept.charge := by
  have source := (Norm.Basic.normSq_eq_canonical kept.parts.source.before.2.2.1.jump).symm.trans_le
    kept.parts.source.before.2.2.1.jump_lt.le
  have reset := (Norm.Basic.normSq_eq_canonical kept.parts.reset.before.2.2.1.jump).symm.trans_le
    kept.parts.reset.before.2.2.1.jump_lt.le
  have paid := Fraction.Order.Arithmetic.add_le_add_direct source
    (Fraction.Order.Arithmetic.add_le_add_direct kept.completed.normSum_le reset)
  change Canonical.normSq kept.parts.source.before.2.2.1.jump + Norm.Sum.Basic.gaussianNormSqSum
    (kept.completed.errors ++ [kept.parts.reset.before.2.2.1.jump]) ≤ _
  have zero : Canonical.normSq kept.parts.reset.before.2.2.1.jump + 0 =
      Canonical.normSq kept.parts.reset.before.2.2.1.jump :=
    (Fraction.Field.add_comm _ 0).trans (Fraction.Field.zero_add _)
  have tail := (Norm.Sum.Basic.gaussianNormSqSum_append kept.completed.errors
    [kept.parts.reset.before.2.2.1.jump]).trans
      (congrArg (fun last : Fraction.Rational => Norm.Sum.Basic.gaussianNormSqSum kept.completed.errors + last) zero)
  exact (congrArg (fun total : Fraction.Rational =>
    Canonical.normSq kept.parts.source.before.2.2.1.jump + total) tail).trans_le paid

end Entry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

end
