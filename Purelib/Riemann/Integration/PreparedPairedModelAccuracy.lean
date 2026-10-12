module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
import Purelib.Riemann.Topology.PreparedBankRootChains

public import Purelib.Riemann.Integration.PreparedModelAccuracy
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Two differential error requests consume one checked geometric refinement.
The second coefficient model is recast from cached owners, not independently
prepared and then identified by its endpoints. -/
namespace Purelib.Riemann.Integration.PreparedPairedModelAccuracy

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (checkedParentBlock uniformParentMesh)
open Purelib.Riemann.Integration.PreparedModelAccuracy (Profile Budget Request)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the paired model-accuracy request. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Two differential accuracy requests sharing one original checked geometric mesh.

The retained accuracy is positive and below the target. Both original profiles, the root budget, selected minimum depth
and exact first/recast block identities remain explicit. -/
structure PairedRequest (parent : CenteredEdge curve source) (other : Differentials.Basic.Differential genus)
    (target : Fraction.Rational) where
  /-- The retained positive accuracy paid by both differential profiles. -/ accuracy : Fraction.Rational
  /-- Strict positivity of the shared original accuracy. -/ accuracyPositive : 0 < accuracy
  /-- The shared accuracy is at most the original requested target. -/ accuracy_le : accuracy ≤ target
  /-- The original requested floor for both child-block depths. -/ minimumDepth : Nat
  /-- The original source differential's parent accuracy profile. -/ firstProfile : Profile parent
  /-- The recast differential's profile on the same original geometric parent. -/ secondProfile : Profile
    (recastCenteredEdge other parent)
  /-- The original parent endpoint root budget. -/ rootBudget : PreparedRefinementRootEndpoints.ParentBudget parent.edge
  /-- The shared spatial/root budget for the summed profile scales and retained depth floor. -/ budget : Budget
    firstProfile.movement (firstProfile.scale + secondProfile.scale)
    (fun diameter => max minimumDepth (PreparedPrimitiveRequests.preparationDepth parent diameter)) accuracy
  /-- The actual checked original parent mesh selected by that shared budget. -/ mesh : CheckedDirectGeometry.Mesh
    parent.edge budget.diameter budget.depth
    parent.edge.left parent.edge.request.endpoint
  /-- The retained model-accuracy request on the original source differential. -/ first : Request firstProfile accuracy
  /-- The retained model-accuracy request on the recast differential. -/ second : Request secondProfile accuracy
  /-- The first request retains exactly the original checked mesh block. -/ first_block : first.block =
    checkedParentBlock parent mesh
  /-- The second request retains exactly that same mesh recast to the other differential. -/ second_block : second.block
    = checkedParentBlock (recastCenteredEdge other parent) (mesh.recast other)

constructive_injectivity PairedRequest

namespace PairedRequest
variable {parent : CenteredEdge curve source} {other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential
  genus} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Acquire one checked mesh paying both original differential model-accuracy profiles.

The common budget uses their summed scales and the requested depth floor. The second child block is the recast of that
exact first mesh, preserving the shared geometry and root owners. -/
@[expose] def build (parent : CenteredEdge curve source) (other : Differentials.Basic.Differential genus)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (target accuracy : Fraction.Rational) (positive : 0 < accuracy) (accuracyLe : accuracy ≤ target)
    (minimumDepth : Nat) : PairedRequest parent other target := by
  let firstProfile := Profile.build parent
  let secondProfile := Profile.build (recastCenteredEdge other parent)
  let rootBudget := PreparedRefinementRootEndpoints.ParentBudget.acquire parent.edge
  let budget := Budget.build firstProfile.movement (firstProfile.scale + secondProfile.scale)
    (fun diameter => max minimumDepth (PreparedPrimitiveRequests.preparationDepth parent diameter))
      firstProfile.movement_nonnegative
    (add_nonneg firstProfile.scale_nonnegative secondProfile.scale_nonnegative) positive
  let mesh := uniformParentMesh parent proper budget.diameter budget.diameterPositive budget.depth
    ((Data.Nat.Order.le_max_right _ _).trans budget.prepared)
  have radiusNonnegative : 0 ≤ Geometric.Basic.quarterRadius firstProfile.movement budget.depth + budget.diameter :=
    add_nonneg (Geometric.Basic.quarterRadius_nonneg firstProfile.movement_nonnegative _) budget.diameterPositive.le
  have firstPaid : firstProfile.scale * (Geometric.Basic.quarterRadius firstProfile.movement budget.depth +
    budget.diameter) ≤ accuracy :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right secondProfile.scale_nonnegative) radiusNonnegative).trans budget.paid
  have secondPaid : secondProfile.scale * (Geometric.Basic.quarterRadius secondProfile.movement budget.depth +
    budget.diameter) ≤ accuracy :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_left firstProfile.scale_nonnegative) radiusNonnegative).trans budget.paid
  let first : Request firstProfile accuracy :=
    ⟨budget.diameter, budget.diameterPositive, budget.depth, checkedParentBlock parent mesh, rfl, rfl, firstPaid⟩
  let second : Request secondProfile accuracy :=
    ⟨budget.diameter, budget.diameterPositive, budget.depth,
      checkedParentBlock (recastCenteredEdge other parent) (mesh.recast other), rfl, rfl, secondPaid⟩
  exact ⟨accuracy, positive, accuracyLe, minimumDepth, firstProfile, secondProfile, rootBudget, budget, mesh, first,
    second, rfl, rfl⟩

/-- The original first child block meets the retained minimum depth. -/
theorem first_depth_ge (request : PairedRequest parent other target) :
    request.minimumDepth ≤ request.first.block.depth := by
  rw [request.first_block, PreparedDirectDyadicRefinements.checkedParentBlock_depth]
  exact (Data.Nat.Order.le_max_left _ _).trans request.budget.prepared

/-- The original recast child block meets the retained minimum depth. -/
theorem second_depth_ge (request : PairedRequest parent other target) :
    request.minimumDepth ≤ request.second.block.depth := by
  rw [request.second_block, PreparedDirectDyadicRefinements.checkedParentBlock_depth]
  exact (Data.Nat.Order.le_max_left _ _).trans request.budget.prepared

/-- The retained second child list is exactly the differential recast of the first list. -/
theorem children_eq (request : PairedRequest parent other target) :
    request.second.block.children = request.first.block.children.map (recastCenteredEdge other) := by
  rw [request.first_block, request.second_block, PreparedDirectDyadicRefinements.checkedParentBlock_children,
    PreparedDirectDyadicRefinements.checkedParentBlock_children]
  exact request.mesh.recast_children other

/-- Every original first-block child meets the requested model-error target. -/
theorem first_error (request : PairedRequest parent other target)
    {child : CenteredEdge curve source} (member : child ∈ request.first.block.children) :
    child.edge.modelErrorAllowance ≤ target := (request.first.child_error member).trans request.accuracy_le

open Purelib.Data.List in
/-- The corresponding recast child meets the same requested model-error target. -/
theorem second_error (request : PairedRequest parent other target)
    {child : CenteredEdge curve source} (member : child ∈ request.first.block.children) :
    (recastCenteredEdge other child).edge.modelErrorAllowance ≤ target := by
  apply le_trans (b := request.accuracy) _ request.accuracy_le
  apply request.second.child_error
  rw [request.children_eq]
  exact Map.mem_map_of_mem member

open Purelib.Riemann.Integration in
/-- Read the original first block together with its retained endpoint root budget. -/
@[expose] def safeBlock (request : PairedRequest parent other target) :
    PreparedEndpointSafeRefinement.EndpointSafeBlock parent where
  budget := request.rootBudget
  block := request.first.block

open Purelib.Riemann.Topology
/-- Read the original first child block's root chain between the retained parent endpoint names. -/
@[expose] def firstRootChain (request : PairedRequest parent other target) :
    PreparedRefinementRootChains.RootChain request.first.block.children
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (by decide)) :=
  PreparedRefinementRootChains.EndpointSafeBlock.rootChain (safeBlock request)

/-- Transport the original root chain to the exact recast second child list. -/
@[expose] def secondRootChain (request : PairedRequest parent other target) :
    PreparedRefinementRootChains.RootChain request.second.block.children
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (by decide)) :=
  PreparedBankRootChains.RootChain.castChildren request.children_eq.symm
    (PreparedRecastRootChains.RootChain.recast other (firstRootChain request))

end PairedRequest
end Purelib.Riemann.Integration.PreparedPairedModelAccuracy
