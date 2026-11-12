module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Preparation
public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Vertex
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Integration.Path.Primitive.Cells.Targets
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Nat.Order

/-! # Count-paid original six-channel sources on retained prepared parents

The actual spatial parent and its original covering patch supply physical
endpoints, sheet and containment. One neighborhood/cache/clearance chain,
two actual continued points and vertex plans, and the original count-paid
allocations construct the existing six-channel source preparation. Every
request consumes its retained original owner; the old curved chart-time
model and its numerical samples are distinct and remain untouched.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}

namespace PreparedParent

/-- The literal starting lifted endpoint of the original parent's retained local segment. -/
abbrev startPoint (parent : CenteredEdge (Fibre.frameCurve frame) basis) : LiftedPoint 2 :=
  ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩

/-- The literal finishing lifted endpoint of that identical original local segment and sheet. -/
abbrev finishPoint (parent : CenteredEdge (Fibre.frameCurve frame) basis) : LiftedPoint 2 :=
  ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩

/-- The existing lift of the exact original local segment with its retained sheet permutation. -/
abbrev liftedCell (parent : CenteredEdge (Fibre.frameCurve frame) basis) :
    LiftedCell (startPoint parent) (finishPoint parent) :=
  ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment

/-- The original covering patch contains its exact physical source endpoint. -/
theorem start_inside (patch : PreparedPatch parent) (count : Nat) :
    (patch.neighborhood count).box.Contains (startPoint parent).coordinate := by
  have inside := patch.start_inside count
  rewrite [parent.edge.point_zero] at inside
  exact inside

/-- The stored covered-parent finish witness admits that same original physical lifted endpoint. -/
theorem finish_inside (patch : PreparedPatch parent) (count : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    (patch.neighborhood count).box.Contains (finishPoint parent).coordinate := by
  rewrite [parent.edge.point_one] at covered
  exact covered

/-- The actual original ordered spatial displacement determines its source-request cost. -/
@[expose] def cost (parent : CenteredEdge (Fibre.frameCurve frame) basis) : Rational :=
  Norm.Basic.normSq ((finishPoint parent).coordinate - (startPoint parent).coordinate)

/-- The original squared-displacement source cost is nonnegative. -/
theorem cost_nonnegative (parent : CenteredEdge (Fibre.frameCurve frame) basis) : 0 ≤ cost parent :=
  Norm.Basic.normSq_nonneg _

/-- The complete original parent-source cache on one GIVEN continued neighborhood.

The original physical parent and both exact endpoint containments index
all retained caches, points, vertices, plans and six-channel preparation.
This is the original dependent tuple, with the neighborhood argument
made explicit; it introduces no replacement owner or record.
-/
@[expose] def OnNeighborhood (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    {count : Nat} (neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) count) (floor : Nat)
    (startInside : neighborhood.box.Contains (startPoint parent).coordinate)
    (finishInside : neighborhood.box.Contains (finishPoint parent).coordinate)
    (targets : CellEndpoints.Targets original stage) :=
  (cache : Cache neighborhood) ×
  (bounds : UniformBounds neighborhood) ×
  (firstSample : ContinuedNeighborhood.Point neighborhood
    (PreparedParent.startPoint parent).coordinate) ×
  (lastSample : ContinuedNeighborhood.Point neighborhood
    (PreparedParent.finishPoint parent).coordinate) ×
  (firstVertex : { vertex : Vertex parameter (PreparedParent.startPoint parent) //
    vertex = Vertex.ofPoint firstSample }) ×
  (lastVertex : { vertex : Vertex parameter (PreparedParent.finishPoint parent) //
    vertex = Vertex.ofPoint lastSample }) ×
  (firstPlan : { plan : EndpointPlan firstSample floor targets.endpoint //
    plan = EndpointPlan.ofVertexCache firstSample firstVertex floor targets.endpoint targets.endpoint_positive }) ×
  (lastPlan : { plan : EndpointPlan lastSample floor targets.endpoint //
    plan = EndpointPlan.ofVertexCache lastSample lastVertex floor targets.endpoint targets.endpoint_positive }) ×
  (requests : IntegrandRequests bounds floor (targets.localBound / 4)) ×
  Preparation (lifted := PreparedParent.liftedCell parent) (cache := cache) requests firstPlan.val lastPlan.val
    startInside finishInside
    (targets.sourceTarget (PreparedParent.cost parent))
    (targets.sourceTarget_positive (PreparedParent.cost parent) (PreparedParent.cost_nonnegative parent))

end PreparedParent

/-- The complete original endpoint and source caches of one count-paid prepared spatial parent.

The covering patch and enclosing path allocations remain indices. Actual
continued points, vertices and plans precede model selection. The final
existing Preparation retains its one request, physical six-cell cache,
independent endpoint attachments and six-channel Query.
-/
abbrev PreparedParent (patch : PreparedPatch parent) (count floor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) :=
  PreparedParent.OnNeighborhood parent (patch.neighborhood count) floor
    (PreparedParent.start_inside patch count) (PreparedParent.finish_inside patch count covered) targets

namespace PreparedParent

variable {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {targets : CellEndpoints.Targets original stage}

/-- Read the one retained source relation/primitive budget cache on the exact original neighborhood. -/
@[expose] def cache (prepared : PreparedParent patch count floor covered targets) :
    Cache (patch.neighborhood count) := prepared.1

/-- Read the retained uniform six-integrand bounds sharing that same original neighborhood. -/
@[expose] def bounds (prepared : PreparedParent patch count floor covered targets) :
    UniformBounds (patch.neighborhood count) := prepared.2.1

/-- Read the actual original source-point continuation owner without querying it again. -/
@[expose] def firstSample (prepared : PreparedParent patch count floor covered targets) :
    ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate := prepared.2.2.1

/-- Read the independent exact finishing-point owner of this original spatial parent. -/
@[expose] def lastSample (prepared : PreparedParent patch count floor covered targets) :
    ContinuedNeighborhood.Point (patch.neighborhood count) (finishPoint parent).coordinate := prepared.2.2.2.1

/-- Read the complete original source vertex and its point-factory equality. -/
@[expose] def firstVertex (prepared : PreparedParent patch count floor covered targets) :
    { vertex : Vertex parameter (startPoint parent) // vertex = Vertex.ofPoint prepared.firstSample } :=
  prepared.2.2.2.2.1

/-- Read the complete retained finishing vertex with its independent original point and factors. -/
@[expose] def lastVertex (prepared : PreparedParent patch count floor covered targets) :
    { vertex : Vertex parameter (finishPoint parent) // vertex = Vertex.ofPoint prepared.lastSample } :=
  prepared.2.2.2.2.2.1

/-- Read the original source endpoint plan consuming its exact retained vertex cache. -/
@[expose] def firstPlan (prepared : PreparedParent patch count floor covered targets) :
    { plan : EndpointPlan prepared.firstSample floor targets.endpoint //
      plan = EndpointPlan.ofVertexCache prepared.firstSample prepared.firstVertex floor targets.endpoint
        targets.endpoint_positive } := prepared.2.2.2.2.2.2.1

/-- Read the original finishing plan with its own vertex factors, precision and requests. -/
@[expose] def lastPlan (prepared : PreparedParent patch count floor covered targets) :
    { plan : EndpointPlan prepared.lastSample floor targets.endpoint //
      plan = EndpointPlan.ofVertexCache prepared.lastSample prepared.lastVertex floor targets.endpoint
        targets.endpoint_positive } := prepared.2.2.2.2.2.2.2.1

/-- Read the six actual uniform requests selected before the common original source model. -/
@[expose] def requests (prepared : PreparedParent patch count floor covered targets) :
    IntegrandRequests prepared.bounds floor (targets.localBound / 4) := prepared.2.2.2.2.2.2.2.2.1

/-- Read the original physical source preparation, both actual attachments and same-cell six-channel query. -/
@[expose] def preparation (prepared : PreparedParent patch count floor covered targets) :
    Preparation (lifted := liftedCell parent) (cache := prepared.cache) prepared.requests
      prepared.firstPlan.val prepared.lastPlan.val (start_inside patch count) (finish_inside patch count covered)
      (targets.sourceTarget (cost parent)) (targets.sourceTarget_positive (cost parent) (cost_nonnegative parent)) :=
  prepared.2.2.2.2.2.2.2.2.2

/-- Transport the identical retained six-channel query to its actual stored model-cell index.

The existing complete cell equality changes only the query's nominal cell
index. Its original owner, source request, selected models, bounds and
uniform request cache remain unchanged, with no source or query execution.
-/
@[expose] def modelQuery (prepared : PreparedParent patch count floor covered targets) :
    Query (Cell.ofModels (parameter := parameter) prepared.preparation.attached.source
      (liftedCell parent) prepared.preparation.models
      (start_inside patch count) (finish_inside patch count covered)) :=
  prepared.preparation.query.castCell prepared.preparation.cell_eq

/-- The actual retained Cell floor is exactly the original six-integrand and two-endpoint construction maximum. -/
theorem sourceFloor_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.floor =
      max prepared.requests.stage (max prepared.firstPlan.val.requests.stage prepared.lastPlan.val.requests.stage) :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) => cell.floor) prepared.preparation.cell_eq

/-- The actual original source selection pays the same retained prepared-parent construction floor.

Only the scalar Cell.floor projection is transported through its complete
factory equation. The final lower bound is read from the SAME retained
Request.selection; no request, model, Point or preparation is executed.
-/
theorem floor_le_sourceStage (prepared : PreparedParent patch count floor covered targets) :
    floor ≤ prepared.preparation.cell.request.selection.stage := by
  have current : floor ≤ prepared.preparation.cell.floor :=
    (prepared.requests.floor_le.trans (Data.Nat.Order.le_max_left _ _)).trans_eq prepared.sourceFloor_eq.symm
  exact current.trans prepared.preparation.cell.request.selection.lower

/-- The retained original cell uses the actual count-paid source target of this physical displacement. -/
theorem target_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.target = targets.sourceTarget (cost parent) := by
  rewrite [prepared.preparation.cell_eq]
  rfl

/-- The retained primitive displacement cost is exactly that of the original physical parent endpoints. -/
theorem displacement_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.primitives.displacementNorm = cost parent :=
  prepared.preparation.cell.primitives.displacementNorm_eq

/-- The identical original six cell models retain the enclosing path's computed differential allowance. -/
theorem allowance_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.allowance = targets.localBound := by
  rewrite [prepared.preparation.cell_eq]
  rfl

end PreparedParent

namespace PreparedParent.OnNeighborhood

/-- Construct the original parent-source tuple using this exact GIVEN neighborhood and endpoint certificates.

The original branch builds each cache, point, vertex, endpoint plan,
request and preparation once. Both the ordinary patch producer and a
checked-neighborhood producer consume this same operation.
-/
def build (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    {count : Nat} (neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) count) (floor : Nat)
    (startInside : neighborhood.box.Contains (PreparedParent.startPoint parent).coordinate)
    (finishInside : neighborhood.box.Contains (PreparedParent.finishPoint parent).coordinate)
    (targets : CellEndpoints.Targets original stage) :
    OnNeighborhood parent neighborhood floor startInside finishInside targets :=
  let cache := Cache.ofPatch neighborhood
  let bounds := UniformBounds.ofClearance neighborhood cache.clearance cache.clearance_eq
  let firstSample := ContinuedNeighborhood.Point.acquire neighborhood (PreparedParent.startPoint parent).coordinate
    startInside
  let lastSample := ContinuedNeighborhood.Point.acquire neighborhood (PreparedParent.finishPoint parent).coordinate
    finishInside
  let firstVertex : { vertex : Vertex parameter (PreparedParent.startPoint parent) //
      vertex = Vertex.ofPoint firstSample } :=
    ⟨Vertex.ofPoint firstSample, rfl⟩
  let lastVertex : { vertex : Vertex parameter (PreparedParent.finishPoint parent) //
      vertex = Vertex.ofPoint lastSample } :=
    ⟨Vertex.ofPoint lastSample, rfl⟩
  let firstPlan := EndpointPlan.ofVertexCache firstSample firstVertex floor targets.endpoint targets.endpoint_positive
  let lastPlan := EndpointPlan.ofVertexCache lastSample lastVertex floor targets.endpoint targets.endpoint_positive
  let requests := IntegrandRequests.build bounds floor (targets.localBound / 4)
    (Data.Rat.Bounds.Quarter.quarter_pos targets.localBound_positive)
  let preparation := Cell.prepare (PreparedParent.liftedCell parent) requests cache firstPlan lastPlan
    startInside finishInside targets.localBound_positive (targets.sourceTarget (PreparedParent.cost parent))
    (targets.sourceTarget_positive (PreparedParent.cost parent) (PreparedParent.cost_nonnegative parent))
  ⟨cache, bounds, firstSample, lastSample, firstVertex, lastVertex, ⟨firstPlan, rfl⟩, ⟨lastPlan, rfl⟩, requests,
    preparation⟩

/-- Reindex the SAME completed parent-source tuple through a whole neighborhood identity.

The data argument has already been constructed. Equality changes only
its original neighborhood and proof indices; it cannot substitute a
fresh neighborhood into the executable construction.
-/
@[expose] def cast {count floor : Nat}
    {first last : ContinuedNeighborhood (Paths.polynomial parameter) count} (same : first = last)
    {firstStart : first.box.Contains (PreparedParent.startPoint parent).coordinate}
    {firstFinish : first.box.Contains (PreparedParent.finishPoint parent).coordinate}
    {lastStart : last.box.Contains (PreparedParent.startPoint parent).coordinate}
    {lastFinish : last.box.Contains (PreparedParent.finishPoint parent).coordinate}
    {targets : CellEndpoints.Targets original stage}
    (prepared : OnNeighborhood parent first floor firstStart firstFinish targets) :
    OnNeighborhood parent last floor lastStart lastFinish targets := by
  cases same
  exact prepared

/-- Whole neighborhood transport preserves the complete actual constructed source cache heterogeneously. -/
theorem cast_heq {count floor : Nat}
    {first last : ContinuedNeighborhood (Paths.polynomial parameter) count} (same : first = last)
    {firstStart : first.box.Contains (PreparedParent.startPoint parent).coordinate}
    {firstFinish : first.box.Contains (PreparedParent.finishPoint parent).coordinate}
    {lastStart : last.box.Contains (PreparedParent.startPoint parent).coordinate}
    {lastFinish : last.box.Contains (PreparedParent.finishPoint parent).coordinate}
    {targets : CellEndpoints.Targets original stage}
    (prepared : OnNeighborhood parent first floor firstStart firstFinish targets) :
    HEq (cast same (lastStart := lastStart) (lastFinish := lastFinish) prepared) prepared := by
  cases same
  rfl

end PreparedParent.OnNeighborhood

namespace PreparedParent

/-- Prepare the original parent source on the SAME already inspected neighborhood, then reindex the completed cache.

The supplied whole factory certifies the original patch owner and every
neighborhood field. Both endpoint proofs are transported before the
shared branch runs on the GIVEN neighborhood. Only its completed result
is cast to the original PreparedParent index, preserving every actual
cache, point, observation, request and selected source factory.
-/
def fromNeighborhood (patch : PreparedPatch parent) (count floor : Nat)
    (neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (factory : neighborhood = patch.neighborhood count)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) : PreparedParent patch count floor covered targets :=
  let startInside := Eq.mpr (congrArg (fun kept : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    kept.box.Contains (startPoint parent).coordinate) factory) (start_inside patch count)
  let finishInside := Eq.mpr (congrArg (fun kept : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    kept.box.Contains (finishPoint parent).coordinate) factory) (finish_inside patch count covered)
  let prepared := OnNeighborhood.build parent neighborhood floor startInside finishInside targets
  OnNeighborhood.cast factory prepared

/-- The whole checked-neighborhood source is the same shared construction through an exact final index transport. -/
theorem fromNeighborhood_eq (patch : PreparedPatch parent) (count floor : Nat)
    (neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (factory : neighborhood = patch.neighborhood count)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) :
    fromNeighborhood patch count floor neighborhood factory covered targets =
      let startInside := Eq.mpr (congrArg (fun kept : ContinuedNeighborhood (Paths.polynomial parameter) count =>
        kept.box.Contains (startPoint parent).coordinate) factory) (start_inside patch count)
      let finishInside := Eq.mpr (congrArg (fun kept : ContinuedNeighborhood (Paths.polynomial parameter) count =>
        kept.box.Contains (finishPoint parent).coordinate) factory) (finish_inside patch count covered)
      OnNeighborhood.cast factory
        (OnNeighborhood.build parent neighborhood floor startInside finishInside targets) := by
  unfold fromNeighborhood
  rfl

end PreparedParent

/-- Construct the original count-paid six-channel source on a retained covered spatial parent.

The two continued points and original vertices are acquired once. The
same cached clearance feeds relation and uniform budgets. The original
path targets determine differential allowance, endpoint allocation and
source residual request; no final primitive or integral bound is supplied.
-/
def prepareParent (patch : PreparedPatch parent) (count floor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) : PreparedParent patch count floor covered targets :=
  let neighborhood := patch.neighborhood count
  let startInside := PreparedParent.start_inside patch count
  let finishInside := PreparedParent.finish_inside patch count covered
  PreparedParent.OnNeighborhood.build parent neighborhood floor startInside finishInside targets

/-- The actual parent producer retains the complete original starting Point acquisition at every source stage. -/
theorem prepareParent_firstSample (patch : PreparedPatch parent) (count floor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) :
    (prepareParent patch count floor covered targets).firstSample =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (PreparedParent.startPoint parent).coordinate
        (PreparedParent.start_inside patch count) := by
  unfold prepareParent PreparedParent.OnNeighborhood.build PreparedParent.firstSample
  rfl

/-- The same parent producer retains its independent complete finishing Point acquisition across target stages. -/
theorem prepareParent_lastSample (patch : PreparedPatch parent) (count floor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (targets : CellEndpoints.Targets original stage) :
    (prepareParent patch count floor covered targets).lastSample =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (PreparedParent.finishPoint parent).coordinate
        (PreparedParent.finish_inside patch count covered) := by
  unfold prepareParent PreparedParent.OnNeighborhood.build PreparedParent.lastSample
  rfl

/-- The whole original source Vertex is independent of path allocations and arithmetic request floors.

Both preparations use the same physical patch, coefficient count and source
point. Their original Point readbacks and complete Vertex.ofPoint factory
equations identify the retained geometric owner and primitive coefficients;
no bank reading or endpoint request is transported to a different accuracy.
-/
theorem prepareParent_firstVertex_eq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (patch : PreparedPatch parent) (count firstFloor lastFloor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex : Nat} (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex) :
    (prepareParent patch count firstFloor covered firstTargets).firstVertex.val =
      (prepareParent patch count lastFloor covered lastTargets).firstVertex.val := by
  have samples : (prepareParent patch count firstFloor covered firstTargets).firstSample =
      (prepareParent patch count lastFloor covered lastTargets).firstSample :=
    (prepareParent_firstSample patch count firstFloor covered firstTargets).trans
      (prepareParent_firstSample patch count lastFloor covered lastTargets).symm
  exact (prepareParent patch count firstFloor covered firstTargets).firstVertex.property.trans
    ((congrArg (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count)
        (PreparedParent.startPoint parent).coordinate => Vertex.ofPoint sample) samples).trans
      (prepareParent patch count lastFloor covered lastTargets).firstVertex.property.symm)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
