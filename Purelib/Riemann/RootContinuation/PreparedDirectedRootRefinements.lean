module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Scale
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels

import Purelib.Riemann.Integration.PreparedUniformDisplacements
import Purelib.Riemann.Topology.PreparedRecastRootChains
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Tactic.Ring

public section

/-!
# Directed ancestry of the actual root-safe refinement stages

The original connected grouping and all-query root maps are retained along
with a positive rational displacement factor for every descendant. The
certificates are propositions; extracting them does not rerun preparation.
-/

namespace Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
  (DirectPathChain DirectParentBlock SynchronizedDirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
  (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (BudgetBank)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints
  (RootClosedState)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState
  (Step)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data in
/-- The descendant displacement is a positive rational multiple of the original parent displacement.

The witness preserves orientation, while a stationary parent still has zero descendant displacement. -/
@[expose] def SameDirection (parent child : CenteredEdge curve source) : Prop :=
  ∃ factor : Rat.Fraction.Rational, 0 < factor ∧ child.edge.point 1 - child.edge.point 0 =
    (⟨factor, 0⟩ : Gaussian.Basic.Canonical) * (parent.edge.point 1 - parent.edge.point 0)

namespace SameDirection

section
open Purelib.Data
/-- Every parent has its own direction with scale one. -/
theorem refl (parent : CenteredEdge curve source) : SameDirection parent parent :=
  ⟨1, by decide, by change _ = (1 : Gaussian.Basic.Canonical) * _; ring1⟩

/-- Compose positive displacement scales through the retained intermediate parent. -/
theorem trans {parent middle child : CenteredEdge curve source}
    (first : SameDirection parent middle) (last : SameDirection middle child) : SameDirection parent child := by
  obtain ⟨a, aPositive, first⟩ := first
  obtain ⟨b, bPositive, last⟩ := last
  have scalar : (⟨b * a, 0⟩ : Gaussian.Basic.Canonical) = (⟨b, 0⟩ : Gaussian.Basic.Canonical) * (⟨a, 0⟩ :
    Gaussian.Basic.Canonical) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  refine ⟨b * a, Rat.Fraction.Order.Arithmetic.mul_pos_direct bPositive aPositive, ?_⟩
  rw [last, first, scalar]
  ring1

end

open Purelib.Curves in
/-- Changing the differential preserves the exact displacement-direction witness. -/
theorem recast {parent child : CenteredEdge curve source} (same : SameDirection parent child) (target :
  Hyperelliptic.Differentials.Basic.Differential genus) :
    SameDirection (recastCenteredEdge target parent) (recastCenteredEdge target child) := same

open Purelib.Riemann in
/-- Every actual child of a retained direct block has the original parent's direction. -/
theorem ofBlock {parent : CenteredEdge curve source} (block : DirectParentBlock parent)
    {child : CenteredEdge curve source} (member : child ∈ block.children) : SameDirection parent child := by
  obtain ⟨factor, positive, equal⟩ :=
    Integration.PreparedUniformDisplacements.DirectParentBlock.step_eq_positive_scale block
  exact ⟨factor, positive,
    (Integration.PreparedUniformDisplacements.DirectParentBlock.child_displacement block member).trans equal⟩

end SameDirection

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Any two original parent parameter points differ by their rational parameter difference times the parent
displacement. -/
private theorem point_difference (parent : CenteredEdge curve source) (first last : Rat.Fraction.Rational) :
    parent.edge.point last - parent.edge.point first =
      (⟨last - first, 0⟩ : Gaussian.Basic.Canonical) * (parent.edge.point 1 - parent.edge.point 0) := by
  apply Gaussian.Basic.ext <;>
    simp only [Integration.PreparedConstantModels.PreparedEdge.point,
      Geometry.ClearPath.ClearSegment.pointAt,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

open Purelib.Data in
/-- A moving parent's actual retained endpoint query fractions are strictly ordered.

The positive displacement factor and original point-location equations identify their difference, using coordinate
cancellation only for the nonstationary parent. -/
theorem RootSubedge.endpoint_order {parent child : CenteredEdge curve source} (relation : RootSubedge parent child)
    (direction : SameDirection parent child) (moving : parent.edge.point 1 ≠ parent.edge.point 0) :
    (relation.location 0 (by decide)).fraction < (relation.location 1 (by decide)).fraction := by
  obtain ⟨factor, positive, equal⟩ := direction
  have affine := point_difference parent (relation.location 0 (by decide)).fraction (relation.location 1 (by
    decide)).fraction
  rw [(relation.location 0 (by decide)).point_eq, (relation.location 1 (by decide)).point_eq] at affine
  have scalars := Gaussian.Field.mul_right_cancel_of_ne (by
    intro vanished
    exact moving (Gaussian.Basic.gaussian_eq_of_sub_eq_zero vanished)) (affine.symm.trans equal)
  have scalarEq := congrArg Gaussian.Basic.re scalars
  change (relation.location 1 (by decide)).fraction - (relation.location 0 (by decide)).fraction = factor at scalarEq
  have ordered := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct positive (relation.location 0 (by
    decide)).fraction
  have finishEq : (relation.location 0 (by decide)).fraction + factor = (relation.location 1 (by decide)).fraction := by
    rw [← scalarEq]
    ring1
  simpa only [add_zero, finishEq] using ordered

/-- Certify connected parent grouping, original root ancestry and positive traversal direction together.

The proposition follows the actual ordered child blocks, retaining each parent's connected path and all-query root maps.
-/
inductive DirectedRefinement : List (CenteredEdge curve source) → List (CenteredEdge curve source) → Prop
  /-- The empty lists form a directed refinement. -/ | nil : DirectedRefinement [] []
  /-- Extend a directed refinement by one actual connected parent block with its root maps and positive directions. -/ |
    cons {parent : CenteredEdge curve source} {parents block children : List (CenteredEdge curve source)}
      (chain : DirectPathChain block
        (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
        (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩))
      (roots : RootSubedgeBlock parent block)
      (direction : ∀ child ∈ block, SameDirection parent child)
      (tail : DirectedRefinement parents children) : DirectedRefinement (parent :: parents) (block ++ children)

namespace DirectedRefinement

/-- The original parent list is a directed refinement of itself. -/
theorem refl : ∀ parents : List (CenteredEdge curve source), DirectedRefinement parents parents
  | [] => .nil
  | parent :: parents => .cons (.cons parent (.nil _)) (.cons (.refl parent) .nil)
      (fun _ member => Purelib.Data.List.Membership.mem_singleton.mp member ▸ SameDirection.refl parent) (refl parents)

/-- Recover a proof-local witness of the same grouped root-subedge refinement. -/
theorem roots {parents children : List (CenteredEdge curve source)} (refinement : DirectedRefinement parents children) :
    Nonempty (RootSubedgeRefinement parents children) := by
  induction refinement with
  | nil => exact ⟨.nil⟩
  | cons chain roots direction tail ih =>
      obtain ⟨remaining⟩ := ih
      exact ⟨.cons chain roots remaining⟩

/-- Split a directed refinement at an exact concatenation of its original parent lists. -/
theorem split : ∀ (first : List (CenteredEdge curve source))
    {second children : List (CenteredEdge curve source)}, DirectedRefinement (first ++ second) children →
    ∃ left right, children = left ++ right ∧ DirectedRefinement first left ∧ DirectedRefinement second right
  | [], _, children, refinement => ⟨[], children, rfl, .nil, refinement⟩
  | parent :: first, _, _, .cons (block := block) chain roots direction tail => by
      obtain ⟨left, right, equal, firstPart, secondPart⟩ := split first tail
      exact ⟨block ++ left, right, (congrArg (List.append block) equal).trans (Purelib.Data.List.Append.append_assoc _ _
        _).symm,
        .cons chain roots direction firstPart, secondPart⟩

/-- Transport one original parent's positive direction through every actual descendant block. -/
private theorem through {parent : CenteredEdge curve source} {middle children : List (CenteredEdge curve source)}
    (refinement : DirectedRefinement middle children) (direction : ∀ child ∈ middle, SameDirection parent child) :
    ∀ child ∈ children, SameDirection parent child := by
  induction refinement with
  | nil => intro child member; exact (List.not_mem_nil member).elim
  | @cons head heads block children chain roots localDirection tail ih =>
      intro child member
      rcases Purelib.Data.List.Membership.mem_append.mp member with member | member
      · exact (direction head List.mem_cons_self).trans (localDirection child member)
      · exact ih (fun child member => direction child (List.mem_cons_of_mem _ member)) child member

open Purelib.Riemann in
/-- Compose directed refinements while preserving their original grouping and root maps.

Each intermediate block is split along its actual descendants, and the two positive displacement factors compose. -/
theorem trans {parents middle children : List (CenteredEdge curve source)}
    (first : DirectedRefinement parents middle) (last : DirectedRefinement middle children) :
    DirectedRefinement parents children := by
  induction first generalizing children with
  | nil => exact last
  | @cons parent parents block middle chain roots direction tail ih =>
      obtain ⟨left, right, equal, firstPart, secondPart⟩ := split block last
      obtain ⟨rootParts⟩ := firstPart.roots
      rw [equal]
      exact .cons
        (RootContinuation.PreparedNestedRootRefinements.refinedChain rootParts chain)
        (RootContinuation.PreparedNestedRootRefinements.refineBlock rootParts roots)
        (firstPart.through direction) (ih secondPart)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Change the differential throughout a directed refinement while retaining its physical grouping and root ancestry. -/
theorem recast (target : Hyperelliptic.Differentials.Basic.Differential genus) {parents children : List (CenteredEdge
  curve source)}
    (refinement : DirectedRefinement parents children) :
    DirectedRefinement (parents.map (recastCenteredEdge target)) (children.map (recastCenteredEdge target)) := by
  induction refinement with
  | nil => exact .nil
  | cons chain roots direction tail ih =>
      rw [List.map_cons, Purelib.Data.List.Map.map_append]
      refine .cons (chain.recast target)
        (Topology.PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeBlock.recast
          target roots) ?_ ih
      intro child member
      obtain ⟨original, present, rfl⟩ := List.Map.mem_map.mp member
      exact (direction original present).recast target

end DirectedRefinement

namespace BudgetBank

open Purelib.Riemann in
open Purelib.Data in
/-- The supplied synchronized blocks and original budget bank certify the actual directed refinement. -/
theorem directed : ∀ {parents : List (CenteredEdge curve source)} {commonDepth : Nat} {diameter : Rat.Fraction.Rational}
    (_ : BudgetBank parents) (blocks : SynchronizedDirectBlockRefinement commonDepth diameter parents),
    DirectedRefinement parents blocks.children
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons block _ _ blocks => by
      let safe : EndpointSafeBlock _ :=
        ⟨head, block⟩
      exact .cons block.chain
        (RootContinuation.PreparedSubedgeRootQueries.EndpointSafeBlock.subedges safe)
        (fun _ member => SameDirection.ofBlock block member)
        (Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements.BudgetBank.directed tail blocks)

end BudgetBank

namespace RootClosedState

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Every retained root-safe schedule step is a directed refinement of its original parents. -/
theorem Step.directed {root : Named} {current : RootClosedState curve source root}
    {targets : List (Hyperelliptic.Differentials.Basic.Differential genus)} {target : Rat.Fraction.Rational} (step :
      Step current targets target) :
    DirectedRefinement current.state.parents step.next.state.parents := by
  rw [step.parents_eq]
  exact RootContinuation.PreparedDirectedRootRefinements.BudgetBank.directed
    step.accuracy.budgets step.accuracy.blocks

open Purelib.Curves in
/-- Every actual schedule stage retains directed root ancestry from the initial parent list.

The proof composes the already retained refinement blocks without rerunning preparation. -/
theorem statesDirected {root : Named} (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus)) :
    ∀ stage, DirectedRefinement initial.state.parents (initial.states targets stage).state.parents
  | 0 => .refl _
  | stage + 1 =>
      (statesDirected initial targets stage).trans
        (Step.directed (initial.scheduledStep targets stage))

end RootClosedState
end Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
