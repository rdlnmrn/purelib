module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Cached
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Integrals
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Inspection.Rows
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Queries
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic

/-! # Complete cached-endpoint source outcomes at one actual old moving occurrence

The actual View, old Head splits and retained endpoint queries index both
execution branches. The same primitive-safe geometry producer retains its
whole Bounds/depth/mesh/block evidence before the source constructor is
called. Actual endpoint Owner records, queries, old Vertices and requests
are forwarded throughout; no canonical endpoint Owner is a data source.
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
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
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
variable (view : PreparedTraceBudget.Trace.View
  budget current inherited request cached ordered small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
variable (endpoints : view.EndpointQueries (curve := Fibre.frameCurve frame) (differential := basis) sheet)
variable (row : Row) {accuracy : AccuracyRequest}
variable (old : Primitive.Spine (row.expression parameter) accuracy trace.path) (parts : view.Observations old)
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}

variable (diameter : Data.Rat.Fraction.Rational) (positive : 0 < diameter)
variable (comparisonRequest : AccuracyRequest)

/-- The actual stationary budget, cached-query root certificate and real comparison on both old endpoint roles. -/
@[expose] def StationaryCompleted :=
  Σ keptBudget : {value : ParentBudget (parent center).edge //
      value = ParentBudget.acquire (parent center).edge ∧ current.parameter = request.endpoint.parameter},
  Σ queryRoots : {value : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      ((parent center).edge.rootName 0 (parent center).edge.baseInside)
      ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
    value = PrimitiveCover.stationaryRootsFromQueries
      (parent center) endpoints.queries keptBudget.property.2 keptBudget.val},
  {value : Points.Cached.EmptyCompared (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets) row (parent center) endpoints.source endpoints.moving
      (endpoints.sourceVertex (curve := Fibre.frameCurve frame) old parts)
      (endpoints.movingVertex (curve := Fibre.frameCurve frame) old parts) comparisonRequest
      keptBudget.property.2 queryRoots.val //
    value = compareGivenEmpty (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts keptBudget.property.2 keptBudget.val queryRoots comparisonRequest}

/-- The SAME checked geometry, actual cached-query root chain and source/Point/join outcome on the old moving head.

The geometry payload is the existing exact PrimitiveCover.Refinement dependent
product. Its block factory preserves common original segment frames;
root and endpoint relations are never substituted for that evidence.
-/
@[expose] def RefinedCompleted :=
  Σ safe : {value : EndpointSafeBlock (parent center) //
    value.budget = ParentBudget.acquire (parent center).edge},
  Σ _geometry : PrimitiveCover.Refinement (parent center) diameter positive safe.val,
  Σ inspected : {value : CoveredParents.Inspection (count := count) safe.val.block.children //
    value = CoveredParents.Inspection.build safe.val.block.children ∧
      CoveredParents.Inspection.Ready safe.val.block.children value},
  Σ covered : {value : CoveredParents.Inspection.Success inspected.val //
    value.val = CoveredParents.Inspection.coveredOfReady safe.val.block.children inspected.val inspected.property.2},
  Σ queryRoots : {value : RootChain safe.val.block.children
      ((parent center).edge.rootName 0 (parent center).edge.baseInside)
      ((parent center).edge.rootName 1 (of_decide_eq_true rfl)) //
    value = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe.val endpoints.queries},
  {value : OnCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe.val inspected.val covered.val queryRoots comparisonRequest //
    value = compareGivenCover (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts safe.val inspected.val covered.val queryRoots comparisonRequest}

namespace RefinedCompleted

variable {view center endpoints row old parts diameter positive comparisonRequest}
variable (retained : RefinedCompleted (count := count) (floor := floor) (targets := targets)
  view center endpoints row old parts diameter positive comparisonRequest)

/-- Read the SAME actual original block and ParentBudget without reconstructing child geometry. -/
@[expose] def safe : EndpointSafeBlock (parent center) := retained.1.val

/-- Read the original Bounds, depth, mesh and checked-block factories accompanying this SAME source execution. -/
@[expose] def geometry : PrimitiveCover.Refinement
    (parent center) diameter positive retained.safe := retained.2.1

end RefinedCompleted

/-- Both actual refinement branches retain their complete original geometry and actual cached endpoint comparison. -/
@[expose] def Completed :=
  StationaryCompleted (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts comparisonRequest ⊕
    RefinedCompleted (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest

namespace Completed

/-- Compare the unchanged old endpoints using the actual given zero-width budget and query-root cache. -/
private def fromStationary
    (geometry : PrimitiveCover.Acquisition.Stationary (parent center) endpoints.queries) :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest :=
  let compared := compareGivenEmpty (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts geometry.1.property.2 geometry.1.val geometry.2 comparisonRequest
  .inl ⟨geometry.1, geometry.2, ⟨compared, rfl⟩⟩

/-- Construct source and Point comparisons on the same given refined geometry and actual query-root cache. -/
private def fromRefined
    (geometry : PrimitiveCover.Acquisition.Refined (count := count)
      (parent center) endpoints.queries diameter positive) :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest :=
  let compared := compareGivenCover (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts geometry.1.val geometry.2.2.1.val geometry.2.2.2.1.val
    geometry.2.2.2.2 comparisonRequest
  .inr ⟨geometry.1, geometry.2.1, geometry.2.2.1, geometry.2.2.2.1, geometry.2.2.2.2, ⟨compared, rfl⟩⟩

/-- Complete the source comparison on a given original geometry acquisition after requests are selected.

The actual old View, endpoint queries and observations index the existing
source workers. Both branches consume the same given budget, checked
geometry, neighborhoods, cover and signed roots. No geometry producer,
endpoint query or old observation is executed here.
-/
def fromGeometry
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest :=
  match geometry with
  | .inl retained => fromStationary (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest retained
  | .inr retained => fromRefined (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest retained

/-- Refine this same old View once and consume its actual cached endpoint Owners in both execution branches.

The original convenience entry retains its complete geometry before the
shared source worker consumes it. A caller that already acquired geometry
can use fromGeometry and choose requests from its actual child count.
Existing old observation requests and all result fields remain unchanged.
-/
def build : Completed (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts diameter positive comparisonRequest :=
  let geometry := PrimitiveCover.Acquisition.build (count := count)
    (parent center) endpoints.queries diameter positive
  fromGeometry (count := count) (floor := floor) (targets := targets)
    view center endpoints row old parts diameter positive comparisonRequest geometry

/-- Row-independent certified six-channel source data on the SAME actual acquisition outcome.

Stationary outer roles have no source child and retain the unit. A strict
outcome stores one actual complete source product on its own inspected
neighborhoods and successful cover, with the original whole factory.
-/
@[expose] def Sources
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :=
  match geometry with
  | .inl _ => PUnit
  | .inr retained =>
      {value : PreparedParents retained.2.2.2.1.val.val floor targets //
        value = PreparedParents.fromInspection retained.2.2.1.val retained.2.2.2.1.val floor targets}

namespace Sources

/-- Prepare one actual six-channel source bank on the GIVEN complete geometry before any row observation. -/
def build
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry :=
  match geometry with
  | .inl _ => PUnit.unit
  | .inr retained =>
      ⟨PreparedParents.fromInspection retained.2.2.1.val retained.2.2.2.1.val floor targets, rfl⟩

/-- Read the literal original differential-cell occurrences without another source or observation execution. -/
@[expose] def cells (channel : Fin 6)
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry →
      List CellModel :=
  match geometry with
  | .inl _ => fun _ => []
  | .inr retained => fun shared => PreparedParents.cells (covered := retained.2.2.2.1.val.val) shared.val channel

/-- Read the actual row-model integrals directly from the SAME six-channel source product, without observations. -/
@[expose] def integrals (row : Row)
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry → List Canonical :=
  match geometry with
  | .inl _ => fun _ => []
  | .inr retained => fun shared => Points.Cache.sourceIntegrals row retained.2.2.2.1.val.val shared.val

/-- The actual row-model sample is the exact combination of the SAME six stored physical source lists.

The strict branch uses the actual direct child chain and the original
source algebra. Empty source lists have zero numerical combination;
no endpoint comparison is removed from the separate completion cache.
-/
theorem combine_eq (row : Row)
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry) :
    gaussianSum (integrals (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive row geometry shared) =
      Row.combine parameter row (fun channel =>
        (PathModel.mk (cells (count := count) (floor := floor) (targets := targets)
          view center endpoints diameter positive channel geometry shared)).integralSample) := by
  cases geometry with
  | inl retained =>
      change 0 = Row.combine parameter row (fun _ => 0)
      exact (Row.combine_zero parameter row).symm
  | inr retained =>
      exact Points.Cache.sum_sourceIntegrals_combine row retained.2.2.2.1.val.val shared.val
        (CenteredPathChain.ofDirect retained.1.val.block.chain)

end Sources

/-- Consume the GIVEN complete six-channel bank on the SAME geometry and original moving observations.

The empty branch uses its original real endpoint comparison. The strict
branch reuses the actual covered source product through the original
cached endpoint Owners and signed root chain. It prepares no source,
geometry, query or old observation.
-/
def fromSources
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry →
      Completed (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts diameter positive comparisonRequest :=
  match geometry with
  | .inl retained => fun _ =>
      fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts diameter positive comparisonRequest (.inl retained)
  | .inr retained => fun shared =>
      let compared := compareGivenPreparedCover (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest shared
      have factory := compareGivenPreparedCover_eq_compareGivenCover
        (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest shared
      .inr ⟨retained.1, retained.2.1, retained.2.2.1, retained.2.2.2.1, retained.2.2.2.2,
        ⟨compared, factory⟩⟩

/-- The actual given-source execution retains the original whole completion factory on these SAME cached inputs. -/
theorem fromSources_eq_fromGeometry
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry) :
    fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest geometry shared =
    fromGeometry (trace := trace) (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest geometry := by
  cases geometry with
  | inl retained => rfl
  | inr retained =>
      let actual := compareGivenPreparedCover (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest shared
      let expected := compareGivenCover (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest
      have actualEq : actual = expected := compareGivenPreparedCover_eq_compareGivenCover
        (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest shared
      have same : (⟨actual, actualEq⟩ : {value : OnCover (count := count) (floor := floor) (targets := targets)
          view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
          retained.2.2.2.2 comparisonRequest // value = expected}) = ⟨expected, rfl⟩ := by
        apply Subtype.ext
        exact actualEq
      exact congrArg (fun result => (.inr
        ⟨retained.1, retained.2.1, retained.2.2.1, retained.2.2.2.1, retained.2.2.2.2, result⟩ :
        Completed (count := count) (floor := floor) (targets := targets)
          view center endpoints row old parts diameter positive comparisonRequest)) same

variable {view center endpoints row old parts diameter positive comparisonRequest}

/-- Read the SAME original refined source-integral list, with an empty inner word for a zero-width outer occurrence. -/
@[expose] def integrals :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest → List Canonical
  | .inl _ => []
  | .inr retained => retained.2.2.2.2.2.val.integrals

/-- The actual completed row reads exactly the SAME supplied source-bank integral list.

All actual Point readings and endpoint joins remain in the completion.
Only their integral projection is transported through original stored
source/reading factories; no source or observation producer is executed.
-/
theorem fromSources_integrals
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      view center endpoints diameter positive geometry) :
    (fromSources (trace := trace) (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest geometry shared).integrals =
      Sources.integrals (count := count) (floor := floor) (targets := targets)
        view center endpoints diameter positive row geometry shared := by
  cases geometry with
  | inl retained => rfl
  | inr retained =>
      unfold fromSources integrals
      exact compareGivenPreparedCover_integrals (count := count) (floor := floor) (targets := targets)
        view center endpoints row old parts retained.1.val retained.2.2.1.val retained.2.2.2.1.val
        retained.2.2.2.2 comparisonRequest shared

/-- Read actual signed source/join residuals, retaining the genuine comparison in the zero-child branch. -/
@[expose] def errors :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest → List Canonical
  | .inl retained => retained.2.2.val.errors
  | .inr retained => retained.2.2.2.2.2.val.errors

/-- Read the literal retained block child count; a zero-width occurrence has no fabricated inner child. -/
@[expose] def childCount :
    Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest → Nat
  | .inl _ => 0
  | .inr retained => retained.1.val.block.children.length

/-- The completed comparison retains exactly the child count available before numerical requests were selected. -/
theorem fromGeometry_childCount
    (geometry : PrimitiveCover.Acquisition (count := count)
      (parent center) endpoints.queries diameter positive) :
    (fromGeometry (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest geometry).childCount =
      geometry.childCount := by
  cases geometry with
  | inl retained => rfl
  | inr retained => rfl

/-- The exact local charge keeps both original old request owners and the SAME actual refined child count. -/
@[expose] def charge
    (retained : Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest) : Data.Rat.Fraction.Rational :=
  Points.charge targets comparisonRequest retained.childCount accuracy accuracy

/-- Actual child residuals and the real endpoint comparison give exactly two residuals per child plus one. -/
theorem errors_length
    (retained : Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest) :
    retained.errors.length = 2 * retained.childCount + 1 := by
  cases retained with
  | inl retained => exact retained.2.2.val.errors_length
  | inr retained => exact retained.2.2.2.2.2.val.errors_length

/-- SAME cached-Owner comparisons telescope to the literal old moving increment minus actual child source samples. -/
theorem sum_errors
    (retained : Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest) :
    Norm.Sum.Basic.gaussianSum retained.errors = parts.moving.before.last.value - parts.moving.before.first.value -
      Norm.Sum.Basic.gaussianSum retained.integrals := by
  cases retained with
  | inl retained =>
      have same := retained.2.2.val.sum_errors
      have values := congrArg₂ (fun first last : Canonical => last - first)
        (endpoints.sourceVertex_value (curve := Fibre.frameCurve frame) old parts)
        (endpoints.movingVertex_value (curve := Fibre.frameCurve frame) old parts)
      exact same.trans (values.trans (Basic.sub_zero _).symm)
  | inr retained => exact retained.2.2.2.2.2.val.sum_errors

/-- The SAME actual old requests and new source/Point/join caches pay the full local norm sum. -/
theorem normSum_le
    (retained : Completed (count := count) (floor := floor) (targets := targets)
      view center endpoints row old parts diameter positive comparisonRequest) :
    Norm.Sum.Basic.gaussianNormSqSum retained.errors ≤ retained.charge := by
  cases retained with
  | inl retained => exact retained.2.2.val.normSum_le
  | inr retained => exact retained.2.2.2.2.2.val.normSum_le

end Completed

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cached

end
