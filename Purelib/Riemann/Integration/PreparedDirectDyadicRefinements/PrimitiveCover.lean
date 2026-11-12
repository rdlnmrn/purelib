module

public import Purelib.Riemann.Topology.PreparedRefinementRootChains.Queries
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Coverage
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order

/-! # Primitive-safe coverage of the same actual direct parent block

One original segment bound and a computed maximum depth pay root
preparation and primitive-neighborhood coverage together. The actual
checked block supplies the stored children. Complete segment-frame
readbacks transport the same original bound to those children; neither
child centers nor root preparations are replayed to obtain coverage.
The original ParentBudget and same block give the genuine signed RootChain.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

open Purelib.Riemann
open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Branches

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original segment's complete dependent geometric frame, used only for exact index transport. -/
private def SegmentFrame (polynomial : GaussianPolynomial) :=
  Σ ambient : Geometry.Rational.Box, Σ start : Canonical, Σ finish : Canonical,
    ClearSegment polynomial ambient start finish

/-- Read the complete actual segment and all its original indices without constructing a different segment. -/
private def segmentFrame (edge : PreparedEdge curve differential) : SegmentFrame curve.polynomial :=
  ⟨edge.ambient, edge.start, edge.finish, edge.segment⟩

/-- The original bound family on the exact retained segment frame. -/
private def FrameBounds {polynomial : GaussianPolynomial} (frame : SegmentFrame polynomial) := Bounds frame.2.2.2

/-- Every actual checked leaf retains the original whole segment frame, in original child order. -/
private theorem child_frame {parent : PreparedEdge curve differential} {diameter : Rational} :
    {depth : Nat} → {left right : PreparedSheetContinuation.Endpoint} →
    (mesh : CheckedDirectGeometry.Mesh parent diameter depth left right) →
    ∀ child ∈ mesh.children, segmentFrame child.edge = segmentFrame parent
  | _, _, _, .leaf data _, _, member => by
      cases member with
      | head => rfl
      | tail _ impossible => cases impossible
  | _, _, _, .split first second, child, member => by
      rcases Membership.mem_append.mp member with inFirst | inSecond
      · exact child_frame first child inFirst
      · exact child_frame second child inSecond

/-- Actual block-factory evidence transfers the checked mesh's whole segment-frame law to its SAME stored children. -/
private theorem block_frame (parent : CenteredEdge curve differential) {diameter : Rational} {depth : Nat}
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint)
    (block : DirectParentBlock parent) (factory : block = checkedParentBlock parent mesh)
    {child : CenteredEdge curve differential} (member : child ∈ block.children) :
    segmentFrame child.edge = segmentFrame parent.edge := by
  have children := (congrArg DirectParentBlock.children factory).trans (checkedParentBlock_children parent mesh)
  exact child_frame mesh child (Eq.mp (congrArg (fun values => child ∈ values) children) member)

/-- Transport the SAME original segment-bound cache through its complete geometric-frame identity. -/
private def childBounds {parent child : CenteredEdge curve differential}
    (same : segmentFrame child.edge = segmentFrame parent.edge) (bounds : Bounds parent.edge.segment) :
    Bounds child.edge.segment := Eq.mpr (congrArg FrameBounds same) bounds

/-- Exact frame transport preserves the actual original radius field. -/
private theorem cast_radius {polynomial : GaussianPolynomial} {first last : SegmentFrame polynomial}
    (same : first = last) (bounds : FrameBounds last) :
    (Eq.mpr (congrArg FrameBounds same) bounds).radius = bounds.radius := by
  cases same
  rfl

/-- The once built original segment bound has the exact corresponding child-bound factory after frame transport. -/
private theorem childBounds_factory {parent child : CenteredEdge curve differential}
    (same : segmentFrame child.edge = segmentFrame parent.edge) (bounds : Bounds parent.edge.segment)
    (factory : bounds = Bounds.build parent.edge.segment) :
    childBounds same bounds = Bounds.build child.edge.segment := by
  have natural {first last : SegmentFrame curve.polynomial} (equal : first = last) :
      Eq.mpr (congrArg FrameBounds equal) (Bounds.build last.2.2.2) = Bounds.build first.2.2.2 := by
    cases equal
    rfl
  exact (congrArg (fun kept : Bounds parent.edge.segment => childBounds same kept) factory).trans (natural same)

/-- Read the original movement bound at the same retained bounded child occurrence. -/
private theorem movement_at {bound : Rational} :
    (children : List (CenteredEdge curve differential)) → ChildMovementBound bound children →
    (index : Fin children.length) → (children[index.val]'index.isLt).edge.pointMovement ≤ bound
  | [], _, index => Fin.elim0 index
  | _ :: children, .cons head tail, index =>
      Fin.cases head (fun following => movement_at children tail following) index

/-- The same root-preparation and primitive-radius costs determine one sufficient finite refinement depth. -/
@[expose] def depth (parent : CenteredEdge curve differential) (bounds : Bounds parent.edge.segment)
    (diameter : Rational) : Nat :=
  max (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter)
    (Search.firstQuarterBelow (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) 0 (bounds.radius ^ 2))

/-- The computed maximum retains the original sufficient root-preparation depth. -/
theorem depth_enough (parent : CenteredEdge curve differential) (bounds : Bounds parent.edge.segment)
    (diameter : Rational) :
    PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter ≤ depth parent bounds diameter :=
  Data.Nat.Order.le_max_left _ _

/-- Every child movement at the same computed depth lies strictly inside the retained primitive radius. -/
theorem depth_small (parent : CenteredEdge curve differential) (bounds : Bounds parent.edge.segment)
    (diameter : Rational) :
    Basic.quarterRadius (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) (depth parent bounds diameter) < bounds.radius ^ 2 := by
  have nonnegative : 0 ≤ geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter := Data.Gaussian.Norm.Basic.normSq_nonneg _
  exact (Basic.quarterRadius_antitone nonnegative (Data.Nat.Order.le_max_right _ _)).trans_lt
    (Search.firstQuarterBelow_accurate _ nonnegative 0 _
      (Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct bounds.radius_positive 2))

/-- Construct and inspect one actual child patch using the SAME transported original segment bound.

The positive coverage result follows from the actual child movement
certificate and original radius. The original neighborhood and point
inspection still execute once; their cached result is retained unchanged.
-/
private def inspectChild {parent child : CenteredEdge curve differential}
    (bounds : Bounds parent.edge.segment) (boundsFactory : bounds = Bounds.build parent.edge.segment)
    (same : segmentFrame child.edge = segmentFrame parent.edge)
    (small : child.edge.pointMovement < bounds.radius ^ 2) :
    {inspected : CoveredParents.Inspection.AtParent count child //
      inspected.Ready ∧ inspected = CoveredParents.Inspection.AtParent.build count child} := by
  let retainedBounds := childBounds same bounds
  let patch := PreparedPatch.ofBounds child retainedBounds
  have boundFactory := childBounds_factory same bounds boundsFactory
  have patchFactory : patch = PreparedPatch.acquire child := congrArg (PreparedPatch.ofBounds child) boundFactory
  let inspected := CoveredParents.Inspection.AtParent.fromPatch count patch patchFactory
  have radius : patch.bounds.radius = bounds.radius := cast_radius same bounds
  have near : Data.Gaussian.Norm.Basic.normSq (child.edge.point 1 - child.edge.point 0) ≤ patch.bounds.radius ^ 2 :=
    small.le.trans_eq (congrArg (fun radius : Rational => radius ^ 2) radius).symm
  have covered := patch.point_inside_of_distance count near
  have actual : inspected.neighborhood.box.Contains (child.edge.point 1) :=
    Eq.mpr (congrArg (fun neighborhood : Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood
      curve.polynomial count => neighborhood.box.Contains (child.edge.point 1))
        (CoveredParents.Inspection.AtParent.fromPatch_neighborhood count patch patchFactory)) covered
  exact ⟨inspected, inspected.ready_of_inside actual,
    CoveredParents.Inspection.AtParent.fromPatch_eq_build count patch patchFactory⟩

/-- The same actual meshes, child block, checked neighborhoods, derived cover and original signed root chain.

The whole segment-frame and movement certificates are derived from the
retained checked-block factory. Both original Bounds and every original
child remain actual data. No old root row or old observation is replaced.
-/
@[expose] def ConsumerWith (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter)
    (rootsFor : (safe : EndpointSafeBlock parent) →
      RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
        (parent.edge.rootName 1 (of_decide_eq_true rfl))) (Result : Type u) :=
  (bounds : Bounds parent.edge.segment) → bounds = Bounds.build parent.edge.segment →
  (chosenDepth : Nat) → chosenDepth = depth parent bounds diameter →
  (enough : PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter ≤ chosenDepth) →
  (mesh : CheckedDirectGeometry.Mesh parent.edge diameter chosenDepth parent.edge.left parent.edge.request.endpoint) →
  mesh = uniformParentMesh parent proper diameter positive chosenDepth enough →
  (safe : EndpointSafeBlock parent) → safe.budget = ParentBudget.acquire parent.edge →
  safe.block = checkedParentBlock parent mesh →
  (inspected : CoveredParents.Inspection (count := count) safe.block.children) →
  inspected = CoveredParents.Inspection.build safe.block.children →
  (ready : CoveredParents.Inspection.Ready safe.block.children inspected) →
  (covered : CoveredParents.Inspection.Success inspected) →
  covered.val = CoveredParents.Inspection.coveredOfReady safe.block.children inspected ready →
  (roots : RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
    (parent.edge.rootName 1 (of_decide_eq_true rfl))) →
  roots = rootsFor safe → Result

/-- The original primitive-safe geometry callback with its unchanged original root-chain factory. -/
@[expose] def Consumer (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter) (Result : Type u) :=
  ConsumerWith (count := count) parent proper diameter positive
    (fun safe => Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChain safe) Result

/-- The SAME actual geometry callback with its root chain derived from the GIVEN original parent query provider.

No source target or observation accuracy has yet been selected. The actual
bounds, depth, mesh, child count, block and endpoint queries are available
before a consumer requests new source or primitive observations.
-/
@[expose] def ConsumerFromQueries (parent : CenteredEdge curve differential)
    (queries : RootContinuation.PreparedRefinementRootEndpoints.Queries parent.edge)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter) (Result : Type u) :=
  ConsumerWith (count := count) parent proper diameter positive
    (fun safe => Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe queries) Result

/-- Build one primitive-safe child block and certify coverage on those SAME actual stored children.

One original Bounds, one checked mesh, one checked block and one retained
ParentBudget execute. The source bounds are transported as data, not
rebuilt per child. Complete original block-factory evidence supplies each
segment frame; actual movement bounds prove each inspected containment.
The same EndpointSafeBlock supplies every signed root-chain junction.
This constructs no old/source observation and no replacement TransportRow.
-/
private def withCoverBy (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter)
    (rootsFor : (safe : EndpointSafeBlock parent) →
      RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
        (parent.edge.rootName 1 (of_decide_eq_true rfl))) {Result : Type u}
    (consume : ConsumerWith (count := count) parent proper diameter positive rootsFor Result) : Result := by
  let bounds := Bounds.build parent.edge.segment
  let chosenDepth := depth parent bounds diameter
  have enough := depth_enough parent bounds diameter
  let mesh := uniformParentMesh parent proper diameter positive chosenDepth enough
  let block := checkedParentBlock parent mesh
  let budget := ParentBudget.acquire parent.edge
  let safe : EndpointSafeBlock parent := ⟨budget, block⟩
  have blockFactory : safe.block = checkedParentBlock parent mesh := rfl
  have small := depth_small parent bounds diameter
  let entries := fun index : Fin safe.block.children.length =>
    let child := safe.block.children[index.val]'index.isLt
    have same := block_frame parent mesh safe.block blockFactory (List.getElem_mem index.isLt)
    have movement := movement_at safe.block.children safe.block.movements index
    have blockDepth : safe.block.depth = chosenDepth := checkedParentBlock_depth parent mesh
    have movementSmall : child.edge.pointMovement < bounds.radius ^ 2 :=
      movement.trans_lt (Eq.mpr (congrArg (fun selectedDepth =>
        Basic.quarterRadius (geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter) selectedDepth < bounds.radius ^ 2) blockDepth) small)
    inspectChild (count := count) bounds rfl same movementSmall
  let inspected : CoveredParents.Inspection (count := count) safe.block.children :=
    DependentProduct.ofFn safe.block.children (fun index => (entries index).val)
  have inspectedFactory : inspected = CoveredParents.Inspection.build safe.block.children :=
    (DependentProduct.ofFn_congr safe.block.children (fun index => (entries index).val)
      (fun index => CoveredParents.Inspection.AtParent.build count
        (safe.block.children[index.val]'index.isLt)) (fun index => (entries index).property.2)).trans
      (CoveredParents.Inspection.build_eq safe.block.children).symm
  have readyAt (index : Fin safe.block.children.length) : (inspected.entry index).Ready := by
    have same := DependentProduct.get_ofFn safe.block.children (fun index => (entries index).val) index
    exact Eq.mpr (congrArg (fun checked : CoveredParents.Inspection.AtParent count
      (safe.block.children[index.val]'index.isLt) => checked.Ready) same) (entries index).property.1
  have ready := CoveredParents.Inspection.ready_of_entries safe.block.children inspected readyAt
  let covered : CoveredParents.Inspection.Success inspected :=
    ⟨CoveredParents.Inspection.coveredOfReady safe.block.children inspected ready, ⟨ready, rfl⟩⟩
  let roots := rootsFor safe
  exact consume bounds rfl chosenDepth rfl enough mesh rfl safe rfl blockFactory inspected inspectedFactory
    ready covered rfl roots rfl

/-- Build the original primitive-safe block and original root chain through the SAME shared geometry worker. -/
def withCover (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter) {Result : Type u}
    (consume : Consumer (count := count) parent proper diameter positive Result) : Result :=
  withCoverBy parent proper diameter positive
    (fun safe => Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChain safe) consume

/-- Build the SAME actual geometry once and derive its root chain using GIVEN cached parent queries throughout.

The shared worker constructs the original Bounds/mesh/block/neighborhoods
once. The selected root-chain factory consumes the actual query provider,
including its retained zero/unit Owners. Its complete geometry remains
available before source targets and new observation requests are chosen.
-/
def withCoverFromQueries (parent : CenteredEdge curve differential)
    (queries : RootContinuation.PreparedRefinementRootEndpoints.Queries parent.edge)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Rational) (positive : 0 < diameter) {Result : Type u}
    (consume : ConsumerFromQueries (count := count) parent queries proper diameter positive Result) : Result :=
  withCoverBy parent proper diameter positive
    (fun safe => Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe queries) consume

/-- A zero parameter-width original parent retains both outer endpoint roles at the same exact coordinate. -/
theorem stationary_point (parent : CenteredEdge curve differential)
    (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) :
    parent.edge.point 0 = parent.edge.point 1 :=
  parent.edge.point_zero.trans ((congrArg parent.edge.segment.pointAt same).trans parent.edge.point_one.symm)

/-- The actual retained parent budget supplies both original root roles of a zero-width inner word. -/
def stationaryRoots (parent : CenteredEdge curve differential)
    (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) (budget : ParentBudget parent.edge) :
    RootChain (curve := curve) (differential := differential) [] (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl)) :=
  .nil (RootContinuation.PreparedRefinementRootEndpoints.samePointEquivalent budget
    0 1 parent.edge.baseInside (of_decide_eq_true rfl) (stationary_point parent same))

/-- The actual zero-width root comparison consumes the SAME GIVEN parent query provider at both endpoints. -/
def stationaryRootsFromQueries (parent : CenteredEdge curve differential)
    (queries : RootContinuation.PreparedRefinementRootEndpoints.Queries parent.edge)
    (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) (budget : ParentBudget parent.edge) :
    RootChain (curve := curve) (differential := differential) [] (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl)) :=
  .nil (RootContinuation.PreparedRefinementRootEndpoints.samePointEquivalentUsing budget queries
    0 1 parent.edge.baseInside (of_decide_eq_true rfl) (stationary_point parent same))

/-- The original stationary outer occurrence, its two endpoint roles and genuine root-return comparison.

Only its inner refinement word is empty. Both root names remain the
original parent queries and the actual ParentBudget supplies their
comparison. This implies no equality of primitive observation values.
-/
@[expose] def StationaryConsumer (parent : CenteredEdge curve differential) (Result : Type u) :=
  (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) →
  (budget : ParentBudget parent.edge) → budget = ParentBudget.acquire parent.edge →
  (roots : RootChain (curve := curve) (differential := differential) [] (parent.edge.rootName 0 parent.edge.baseInside)
    (parent.edge.rootName 1 (of_decide_eq_true rfl))) → roots = stationaryRoots parent same budget → Result

/-- Decide the original parameter interval once, retaining the original exact order and zero-width proof route. -/
private def withInterval (parent : CenteredEdge curve differential) {Result : Type u}
    (stationary : parent.edge.left.parameter = parent.edge.request.endpoint.parameter → Result)
    (refined : parent.edge.left.parameter < parent.edge.request.endpoint.parameter → Result) : Result :=
  if proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter then
    refined proper
  else
    have reverse : parent.edge.request.endpoint.parameter ≤ parent.edge.left.parameter := by
      by_cases reverse : parent.edge.request.endpoint.parameter ≤ parent.edge.left.parameter
      · exact reverse
      · exact False.elim (proper ⟨parent.edge.ordered, reverse⟩)
    have same := Data.Rat.Fraction.Order.Basic.le_antisymm _ _ parent.edge.ordered reverse
    stationary same

/-- The zero-width original callback keeps actual cached parent queries and its exact derived root-chain factory. -/
@[expose] def StationaryConsumerFromQueries (parent : CenteredEdge curve differential)
    (queries : RootContinuation.PreparedRefinementRootEndpoints.Queries parent.edge) (Result : Type u) :=
  (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter) →
  (budget : ParentBudget parent.edge) → budget = ParentBudget.acquire parent.edge →
  (roots : RootChain (curve := curve) (differential := differential) [] (parent.edge.rootName 0 parent.edge.baseInside)
    (parent.edge.rootName 1 (of_decide_eq_true rfl))) →
  roots = stationaryRootsFromQueries parent queries same budget → Result

/-- Refine one original parent sufficiently, or retain its actual zero-width outer occurrence with an empty inner word.

The original parameter decision is constructive and runs before any new
source or primitive observation. Physically stationary parents with a
strict parameter interval still keep their actual refined child visits.
A zero-width parent retains its old root names, ParentBudget and both
outer roles; no strict direct block is fabricated for that branch.
-/
def withCoverOrStationary (parent : CenteredEdge curve differential)
    (diameter : Rational) (positive : 0 < diameter) {Result : Type u}
    (stationary : StationaryConsumer parent Result)
    (refined : (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) →
      Consumer (count := count) parent proper diameter positive Result) : Result :=
  withInterval parent
    (fun same =>
      let budget := ParentBudget.acquire parent.edge
      let roots := stationaryRoots parent same budget
      stationary same budget rfl roots rfl)
    (fun proper => withCover parent proper diameter positive (refined proper))

/-- Refine the original parent or retain its zero-width occurrence using actual GIVEN endpoint-query caches.

Both branches share the original parameter decision and geometry worker.
No source Targets or primitive observation accuracy is required: a consumer
may allocate them from the SAME actual child count afterward. Existing old
observations remain governed by their unchanged original requests.
-/
def withCoverOrStationaryFromQueries (parent : CenteredEdge curve differential)
    (queries : RootContinuation.PreparedRefinementRootEndpoints.Queries parent.edge)
    (diameter : Rational) (positive : 0 < diameter) {Result : Type u}
    (stationary : StationaryConsumerFromQueries parent queries Result)
    (refined : (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) →
      ConsumerFromQueries (count := count) parent queries proper diameter positive Result) : Result :=
  withInterval parent
    (fun same =>
      let budget := ParentBudget.acquire parent.edge
      let roots := stationaryRootsFromQueries parent queries same budget
      stationary same budget rfl roots rfl)
    (fun proper => withCoverFromQueries parent queries proper diameter positive (refined proper))

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

end
