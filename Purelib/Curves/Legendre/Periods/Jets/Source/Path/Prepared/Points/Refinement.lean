module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Inspection
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Inspection
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Topology.PreparedBankRootChains

/-! # Actual primitive-safe source refinement compared to the unchanged old endpoints

The original primitive-safe block executes once. Source preparation
consumes its SAME inspected neighborhoods, and Point observations consume
those SAME completed sources. The original old cached/transported endpoint
names are read internally. Their mixed-request comparisons and every
actual refined child residual give the finite scalar telescope.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

open Purelib.Riemann
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
  (DirectPathChain uniformParentMesh checkedParentBlock)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original zero query reads the SAME cached old moving-source Owner's name. -/
private theorem first_name (parent : CenteredEdge (Fibre.frameCurve frame) basis) :
    parent.edge.rootName 0 parent.edge.baseInside = ownerName parent.edge.cached.preparedOwner :=
  parent.edge.rootName_zero_eq_cached.trans (by
    unfold ownerName Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
    rfl)

/-- The original one query reads the SAME accepted old moving-target Owner's name. -/
private theorem last_name (parent : CenteredEdge (Fibre.frameCurve frame) basis) :
    parent.edge.rootName 1 (of_decide_eq_true rfl) = ownerName
      (Branches.PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
        parent.edge.left parent.edge.owner parent.edge.request parent.edge.small) :=
  parent.edge.rootName_one_eq_transported.trans (by
    unfold ownerName Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
    rfl)

/-- Attach the original query-root chain to both literal old cached/transported endpoint Owners.

Only the two exact original endpoint name readbacks change the type
indices. The actual supplied chain, every child and each signed comparison
are retained; no coarse or child root query is executed.
-/
def endpointRoots (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    {children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (roots : RootChain children (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl))) :
    RootChain children (ownerName parent.edge.cached.preparedOwner)
      (ownerName (Branches.PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
        parent.edge.left parent.edge.owner parent.edge.request parent.edge.small)) :=
  Riemann.Topology.PreparedBankRootChains.RootChain.castNames (first_name parent) (last_name parent) roots

/-- The zero-width outer occurrence supplies an empty geometric word while retaining both original endpoint roles. -/
theorem stationary_geometry (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) :
    Nonempty (DirectPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.finishPoint parent)) := by
  have endpoints : PreparedParent.startPoint parent = PreparedParent.finishPoint parent :=
    congrArg (fun position : Rational =>
      (⟨parent.edge.segment.pointAt position, parent.edge.sheet⟩ : LiftedPoint 2)) same
  exact ⟨Eq.mp (congrArg (fun finish : LiftedPoint 2 =>
    DirectPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (start := PreparedParent.startPoint parent) (finish := finish)) endpoints)
        (DirectPathChain.nil (PreparedParent.startPoint parent))⟩

/-- The actual strict child block, inspected neighborhoods, source product and mixed-request sewing caches.

The SAME original Bounds, computed depth, checked mesh and whole block
factory remain separate from root agreement. The actual EndpointSafeBlock
retains its original child chain, movement data and ParentBudget. Every
later runtime cache has its whole constructor equation. The given old endpoint Vertices retain their
original independent accuracy; no old Spine or root row is replaced.
-/
@[expose] def RefinedConsumer (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (diameter : Rational) (positive : 0 < diameter)
    (floor : Nat) (targets : CellEndpoints.Targets original stage) (oldAccuracy : AccuracyRequest)
    (first : PreparedParent.SourceVertex row parent oldAccuracy)
    (last : PreparedParent.TargetVertex row parent oldAccuracy) (request : AccuracyRequest) (Result : Type u) :=
  (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) →
  (bounds : Bounds parent.edge.segment) → bounds = Bounds.build parent.edge.segment →
  (chosenDepth : Nat) → chosenDepth = PrimitiveCover.depth parent bounds diameter →
  (enough : Branches.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter ≤ chosenDepth) →
  (mesh : Riemann.Integration.CheckedDirectGeometry.Mesh parent.edge diameter chosenDepth
    parent.edge.left parent.edge.request.endpoint) →
  mesh = uniformParentMesh parent proper diameter positive chosenDepth enough →
  (safe : EndpointSafeBlock parent) → safe.budget = ParentBudget.acquire parent.edge →
  safe.block = checkedParentBlock parent mesh →
  (inspected : CoveredParents.Inspection (count := count) safe.block.children) →
  inspected = CoveredParents.Inspection.build safe.block.children →
  (ready : CoveredParents.Inspection.Ready safe.block.children inspected) →
  (covered : CoveredParents.Inspection.Success inspected) →
  covered.val = CoveredParents.Inspection.coveredOfReady safe.block.children inspected ready →
  (queryRoots : RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
    (parent.edge.rootName 1 (of_decide_eq_true rfl))) →
  queryRoots = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChain safe →
  (roots : RootChain safe.block.children (ownerName parent.edge.cached.preparedOwner)
    (ownerName (Branches.PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner parent.edge.request parent.edge.small))) →
  roots = endpointRoots parent queryRoots →
  (prepared : PreparedParents covered.val floor targets) →
  prepared = PreparedParents.fromInspection inspected covered floor targets →
  (readings : Readings row covered.val prepared) → readings = Readings.build row covered.val prepared →
  (compared : Cache row request covered.val prepared readings ⟨safe.block.chain⟩ first last roots) →
  compared = Cache.build row request covered.val prepared readings ⟨safe.block.chain⟩ first last roots → Result

/-- A zero-width original occurrence retains its actual old-to-old requested comparison and original root budget.

Its empty inner word has no fabricated source cell. The SAME two old
Vertices keep their independent request states and values; the actual
OwnerJoin and requested observation comparison remain runtime data.
-/
@[expose] def StationaryConsumer (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (floor : Nat) (targets : CellEndpoints.Targets original stage) (oldAccuracy : AccuracyRequest)
    (first : PreparedParent.SourceVertex row parent oldAccuracy)
    (last : PreparedParent.TargetVertex row parent oldAccuracy) (request : AccuracyRequest) (Result : Type u) :=
  (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) →
  (budget : ParentBudget parent.edge) → budget = ParentBudget.acquire parent.edge →
  (queryRoots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
    (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl))) →
  queryRoots = PrimitiveCover.stationaryRoots parent same budget →
  (roots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
    (ownerName parent.edge.cached.preparedOwner)
    (ownerName (Branches.PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner parent.edge.request parent.edge.small))) →
  roots = endpointRoots parent queryRoots →
  (compared : Cache (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same) first last roots) →
  compared = Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same) first last roots → Result

/-- Retain the real old-endpoint comparison on the original zero-width branch.

The supplied budget and empty query-root chain are the actual refinement
outcome. Their exact name transport feeds one comparison of the unchanged
outer observations, without constructing a source cell.
-/
private def withStationary (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (floor : Nat) (targets : CellEndpoints.Targets original stage) (oldAccuracy : AccuracyRequest)
    (first : PreparedParent.SourceVertex row parent oldAccuracy)
    (last : PreparedParent.TargetVertex row parent oldAccuracy) (request : AccuracyRequest) {Result : Type u}
    (consume : StationaryConsumer (count := count) row parent floor targets oldAccuracy first last request Result)
    (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter)
    (budget : ParentBudget parent.edge) (budgetFactory : budget = ParentBudget.acquire parent.edge)
    (queryRoots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl)))
    (queryRootsFactory : queryRoots = PrimitiveCover.stationaryRoots parent same budget) : Result :=
  let roots := endpointRoots parent queryRoots
  let compared := Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row request CoveredParents.nil PUnit.unit PUnit.unit
    (stationary_geometry parent same) first last roots
  consume same budget budgetFactory queryRoots queryRootsFactory roots rfl compared rfl

/-- Refine sufficiently, prepare SAME inspected sources once, and compare them to both unchanged old endpoint readings.

The parameter decision and primitive-safe refinement precede all new
coefficient observations. The actual new accuracy is localAccuracy targets;
each junction additionally uses the supplied independent comparison
request. The resulting Cache.integral_error_le retains all old/new
tolerances and proves the exact finite source-integral telescope.
A stationary outer interval executes one real mixed-request comparison.
This does not supply numerical row-model attachment, primitive-constant
normalization, canonical-cycle incidence or global signed root return.
-/
def withSources (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (diameter : Rational) (positive : 0 < diameter) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) (oldAccuracy : AccuracyRequest)
    (first : PreparedParent.SourceVertex row parent oldAccuracy)
    (last : PreparedParent.TargetVertex row parent oldAccuracy) (request : AccuracyRequest) {Result : Type u}
    (stationary : StationaryConsumer (count := count) row parent floor targets oldAccuracy first last request Result)
    (refined : RefinedConsumer (count := count)
      row parent diameter positive floor targets oldAccuracy first last request Result) :
    Result :=
  PrimitiveCover.withCoverOrStationary (count := count) parent diameter positive
    (withStationary row parent floor targets oldAccuracy first last request stationary)
    (fun proper bounds boundsFactory chosenDepth depthFactory enough mesh meshFactory safe
        budgetFactory blockFactory inspected inspectedFactory ready covered coveredFactory queryRoots
        queryRootsFactory =>
      let roots := endpointRoots parent queryRoots
      let completed := OnInspection.build (frame := frame) (basis := basis) (count := count) (floor := floor)
        (targets := targets) row parent safe inspected covered parent.edge.cached.preparedOwner
        (Branches.PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
          parent.edge.left parent.edge.owner parent.edge.request parent.edge.small) first last request roots
      refined proper bounds boundsFactory chosenDepth depthFactory enough mesh meshFactory safe budgetFactory
        blockFactory inspected inspectedFactory ready covered coveredFactory queryRoots queryRootsFactory
        roots rfl completed.prepared completed.prepared_eq completed.readings completed.readings_eq
        completed.compared completed.compared_eq)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

end
