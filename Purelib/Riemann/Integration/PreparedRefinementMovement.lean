module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Count-aware movement bounds for actual period refinements

Synchronized dyadic refinement multiplies the cell count by `2^depth`, but
divides the sum of squared displacements by at least the same factor.  Their
product therefore never increases.  The existing accuracy floor also bounds
every actual child displacement by the requested tolerance; no new depth or
replacement mesh is introduced here.
-/

namespace Purelib.Riemann.Integration.PreparedRefinementMovement

public section

open Purelib.Algebra

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Paths.PreparedPrimitivePaths (block_movement_le)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained movement bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (RootSafeAccuracy)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

open Purelib.Data.Rat in
/-- Sum the original centered parents' squared endpoint movements in list order.

Each retained parent contributes its actual geometric movement once. Structural
recursion preserves the ordered parent list and its original endpoint data. -/
@[expose] def movementSum : List (CenteredEdge curve source) → Fraction.Rational
  | [] => 0
  | parent :: parents => parent.edge.pointMovement + movementSum parents

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
/-- Multiply the retained movement sum by the original parent count.

The same cached parent list supplies both the rational count and its movement
sum, so the weight measures these original observations together. -/
@[expose] def movementMass (parents : List (CenteredEdge curve source)) : Fraction.Rational :=
  Budget.Aggregate.countCoordinate parents.length * movementSum parents

/-- Movement mass is the rational parent count times the original movement sum. -/
theorem movementMass_eq (parents : List (CenteredEdge curve source)) :
    movementMass parents = (parents.length : Fraction.Rational) * movementSum parents := by
  rw [movementMass, Budget.Aggregate.countCoordinate_eq]

end

open Purelib.Data.Gaussian in
/-- The original parent movement sum is nonnegative. -/
theorem movementSum_nonnegative : ∀ (parents : List (CenteredEdge curve source)), 0 ≤ movementSum parents
  | [] => le_rfl
  | _ :: parents => add_nonneg (Norm.Basic.normSq_nonneg _) (movementSum_nonnegative parents)

open Purelib.Data.Rat in
/-- The original count-weighted movement mass is nonnegative. -/
theorem movementMass_nonnegative (parents : List (CenteredEdge curve source)) : 0 ≤ movementMass parents := by
  rw [movementMass_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) (movementSum_nonnegative parents)

/-- Movement sums add across concatenated original parent lists. -/
private theorem movementSum_append (first second : List (CenteredEdge curve source)) :
    movementSum (first ++ second) = movementSum first + movementSum second := by
  induction first with
  | nil => change movementSum second = 0 + movementSum second; ring1
  | cons parent parents ih => simp only [List.cons_append, movementSum, ih]; ring1

open Purelib.Data.Gaussian in
open Purelib.Riemann.Integration in
/-- The retained parent movement equals its original segment's geometric movement. -/
theorem pointMovement_eq_geometric (parent : CenteredEdge curve source) :
    parent.edge.pointMovement = geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter := by
  unfold PreparedConstantModels.PreparedEdge.pointMovement geometricMovement
  simp only [Norm.Basic.normSq_eq_canonical]
  change normSq (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) = _
  rw [parent.edge.localSegment.pointAt_one, parent.edge.localSegment.pointAt_zero]

open Purelib.Data.Rat in
/-- A uniform original parent-movement bound controls the sum by parent count times that bound. -/
private theorem movementSum_le (parents : List (CenteredEdge curve source)) (bound : Fraction.Rational)
    (bounded : ∀ parent ∈ parents, parent.edge.pointMovement ≤ bound) :
    movementSum parents ≤ (parents.length : Fraction.Rational) * bound := by
  induction parents with
  | nil => change (0 : Fraction.Rational) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | cons parent parents ih =>
      have total := add_le_add (bounded parent (List.mem_cons_self ..))
        (ih fun child member => bounded child (List.mem_cons_of_mem parent member))
      exact total.trans_eq (by rw [List.length_cons, Nat.cast_succ]; ring1)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
/-- The retained child movement sum, scaled by its dyadic count, is bounded by the original parent movement. -/
theorem block_scaledMovementSum_le {parent : CenteredEdge curve source} (block : DirectParentBlock parent) :
    ((2 ^ block.depth : Nat) : Fraction.Rational) * movementSum block.children ≤ parent.edge.pointMovement := by
  have sumBound := movementSum_le block.children (Geometric.Basic.quarterRadius parent.edge.pointMovement block.depth)
    (by
    intro child member
    rw [pointMovement_eq_geometric parent]
    exact PreparedPrimitivePaths.block_movement_le block member)
  rw [block.childCount] at sumBound
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans_eq
      (Geometric.DyadicCount.dyadic_count_cancel parent.edge.pointMovement block.depth)

section
open Purelib.Data.Rat
/-- A synchronized refinement's dyadic-scaled child movement sum is bounded by its original parent sum. -/
theorem synchronized_scaledMovementSum_le : ∀ {depth : Nat} {diameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (blocks : SynchronizedDirectBlockRefinement depth diameter parents),
    ((2 ^ depth : Nat) : Fraction.Rational) * movementSum blocks.children ≤ movementSum parents
  | _, _, _, .nil => by change _ * 0 ≤ 0; rw [Fraction.Field.mul_zero_direct]
  | _, _, _, .cons block depthEq _ tail => by
      rw [SynchronizedDirectBlockRefinement.children, movementSum_append, _root_.mul_add]
      have head := block_scaledMovementSum_le block
      rw [depthEq] at head
      exact add_le_add head (synchronized_scaledMovementSum_le tail)

/-- Synchronized dyadic refinement does not increase the original count-weighted movement mass.

The exact child-count identity and retained shared depth cancel the geometric movement decay, keeping the original
parent list as the bound owner. -/
theorem synchronized_movementMass_le {depth : Nat} {diameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (blocks : SynchronizedDirectBlockRefinement depth diameter parents) :
    movementMass blocks.children ≤ movementMass parents := by
  rw [movementMass_eq, movementMass_eq, blocks.children_length, NatCast.mul]
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (synchronized_scaledMovementSum_le blocks) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le parents.length))
  exact (show (parents.length : Fraction.Rational) * ((2 ^ depth : Nat) : Fraction.Rational) * movementSum
    blocks.children =
    (parents.length : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) * movementSum blocks.children) by
      ring1).trans_le bound

end

section
open Purelib.Curves.Hyperelliptic
/-- Recasting the differential preserves the same original geometric movement sum. -/
theorem movementSum_recast (target : Differentials.Basic.Differential genus) : ∀ (parents : List (CenteredEdge curve
  source)),
    movementSum (parents.map (recastCenteredEdge target)) = movementSum parents
  | [] => rfl
  | parent :: parents => by
      change parent.edge.pointMovement + movementSum (parents.map (recastCenteredEdge target)) = _
      rw [movementSum_recast target parents]
      rfl

/-- Recasting the differential preserves the same original count-weighted movement mass.

The recast list keeps its length and each original geometric movement. Its
retained rational count and movement sum therefore give the same mass. -/
theorem movementMass_recast (target : Differentials.Basic.Differential genus) (parents : List (CenteredEdge curve
  source)) :
    movementMass (parents.map (recastCenteredEdge target)) = movementMass parents := by
  rw [movementMass_eq, movementMass_eq, Purelib.Data.List.Map.length_map, movementSum_recast]

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Each child of the retained root-safe accuracy result meets its requested movement bound. -/
theorem acquired_childMovement_le (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) (targets : List (Differentials.Basic.Differential
      genus))
    (target : Fraction.Rational) (positive : 0 < target) {child : CenteredEdge curve source}
    (member : child ∈ (RootSafeAccuracy.acquire parents proper targets target positive).blocks.children) :
    child.edge.pointMovement ≤ target :=
  (RootSafeAccuracy.acquire parents proper targets target positive).movement child member

namespace RootClosedState

open Purelib.Riemann.Integration.PreparedRefinementMovement
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState (Step)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained movement bounds. -/
private abbrev Coordinate := Fraction.Rational

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {source : Differential genus} {root : Named}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- A retained root-closed refinement step does not increase its original movement mass. -/
theorem Step.movementMass_le {current : RootClosedState curve source root} {targets : List
  (Differentials.Basic.Differential genus)}
    {target : Fraction.Rational} (step : Step current targets target) :
    movementMass step.next.state.parents ≤ movementMass current.state.parents := by
  rw [step.parents_eq]
  exact synchronized_movementMass_le step.accuracy.blocks

open Purelib.Curves.Hyperelliptic in
/-- Every scheduled root-closed state has movement mass bounded by the retained initial state. -/
theorem states_movementMass_le (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus)) :
    ∀ stage, movementMass (initial.states targets stage).state.parents ≤ movementMass initial.state.parents
  | 0 => le_rfl
  | stage + 1 => (Step.movementMass_le (initial.scheduledStep targets stage)).trans (states_movementMass_le initial
    targets stage)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Each next-stage parent meets the original current stage's scheduled movement target. -/
theorem states_childMovement_le (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (stage : Nat) {child : PreparedSubdivisionModelCore.CenteredEdge curve source}
    (member : child ∈ (initial.states targets (stage + 1)).state.parents) :
    child.edge.pointMovement ≤ initial.state.scheduleTarget targets stage := by
  let step := initial.scheduledStep targets stage
  have belongs : child ∈ step.next.state.parents := member
  rw [step.parents_eq] at belongs
  exact acquired_childMovement_le (initial.states targets stage).state.parents (initial.states targets
    stage).state.proper targets
    (initial.state.scheduleTarget targets stage) (initial.state.scheduleTarget_positive targets stage) belongs

end RootClosedState
end
end Purelib.Riemann.Integration.PreparedRefinementMovement
