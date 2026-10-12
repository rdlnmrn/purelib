module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! A computed stage forces the actual scheduler's spatial depth above a
requested floor, using a retained parent with positive squared movement. -/
namespace Purelib.Riemann.Integration.PreparedScheduledDepthFloor

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicIncrements_length
  dyadicIncrements_sum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_pos quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

open Purelib.Integration.Path.Dyadic in
/-- Depth-zero child coordinate paths read back the original endpoint displacements. -/
private theorem zero_paths (children : List (CenteredEdge curve source)) :
    (children.map (fun child => DyadicPrimitivePaths.dyadicIncrements (fun parameter => child.edge.point parameter) 0 0
      1)).flatten =
      children.map (fun child => child.edge.point 1 - child.edge.point 0) := by
  induction children with
  | nil => rfl
  | cons child children ih => exact congrArg (List.cons _) ih

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path.Dyadic in
/-- The original parent movement is bounded by squared dyadic count times a uniform child movement bound. -/
private theorem block_movement {parent : CenteredEdge curve source} {children : List (CenteredEdge curve source)}
    {depth : Nat} {radius : Coordinate}
    (path : children.map (fun child => child.edge.point 1 - child.edge.point 0) =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => parent.edge.point parameter) depth 0 1)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ radius) :
    parent.edge.pointMovement ≤ ((2 ^ depth : Nat) : Coordinate) * (((2 ^ depth : Nat) : Coordinate) * radius) := by
  have count := congrArg List.length path
  rw [Purelib.Data.List.Map.length_map, DyadicPrimitivePaths.dyadicIncrements_length] at count
  have total := congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum path
  rw [DyadicPrimitivePaths.dyadicIncrements_sum] at total
  have bound := Norm.Sum.Bounds.normSq_sum_le
    (children.map (fun child => child.edge.point 1 - child.edge.point 0)) radius (by
      intro value member
      obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
      exact movements child inChildren)
  rw [total, Purelib.Data.List.Map.length_map, count] at bound
  exact bound

/-- Every original parent's movement is controlled by its retained dyadic readback and child bound. -/
theorem DyadicPaths.parent_movement
    {parents children : List (CenteredEdge curve source)} {refinement : RootSubedgeRefinement parents children}
    {depth : Nat} (paths : DyadicPaths depth refinement) {radius : Coordinate}
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ radius)
    {parent : CenteredEdge curve source} (member : parent ∈ parents) :
    parent.edge.pointMovement ≤ ((2 ^ depth : Nat) : Coordinate) * (((2 ^ depth : Nat) : Coordinate) * radius) := by
  induction refinement with
  | nil => cases member
  | @cons head parents block children chain roots remaining ih =>
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | inTail
      · subst parent
        have path := paths.1 (fun value => value) 0
        rw [Nat.add_zero, zero_paths] at path
        exact block_movement path (fun child inBlock => movements child (List.mem_append_left _ inBlock))
      · exact ih paths.2 (fun child inChildren => movements child (List.mem_append_right _ inChildren)) inTail

namespace RootClosedState

variable {root : Named}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
/-- Select a schedule stage whose radius is below the original moving parent's requested depth threshold.

The executable quarter-radius search uses the retained schedule base and parent movement, then advances the selected
stage once. -/
@[expose] def depthFloorStage (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (parent : CenteredEdge curve source) (minimum : Nat) : Nat :=
  Geometric.Search.firstQuarterBelow (initial.state.scheduleBase targets) 0 (Geometric.Basic.quarterRadius
    parent.edge.pointMovement minimum) + 1

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The scheduled spatial depth reaches the requested floor after its selected threshold stage.

A retained initial parent with strictly positive movement supplies the witness; its original dyadic readback rules out a
shallower depth at the scheduled child movement bound. -/
theorem depthFloorStage_enough (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    {parent : CenteredEdge curve source} (member : parent ∈ initial.state.parents)
    (moving : 0 < parent.edge.pointMovement) (minimum stage : Nat)
    (later : depthFloorStage initial targets parent minimum ≤ stage + 1) :
    minimum ≤ PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial targets (stage + 1) := by
  have threshold := Geometric.Search.firstQuarterBelow_accurate (initial.state.scheduleBase targets)
    (initial.state.scheduleBase_positive targets).le 0 (Geometric.Basic.quarterRadius parent.edge.pointMovement minimum)
    (Geometric.Basic.quarterRadius_pos moving minimum)
  have indexLe : Geometric.Search.firstQuarterBelow (initial.state.scheduleBase targets) 0
      (Geometric.Basic.quarterRadius parent.edge.pointMovement minimum) ≤ stage + 1 :=
    (Nat.le_succ _).trans later
  have small := (quarterRadius_antitone (initial.state.scheduleBase_positive targets).le
    indexLe).trans_lt threshold
  have movement := DyadicPaths.parent_movement (PreparedScheduledPrimitivePaths.RootClosedState.states_dyadicPaths
    initial targets (stage + 1))
    (fun child inChildren => PreparedRefinementMovement.RootClosedState.states_childMovement_le initial targets stage
      inChildren) member
  apply Nat.le_of_not_lt
  intro shallow
  have radiusSmall := small.trans_le (quarterRadius_antitone moving.le (Nat.le_of_lt shallow))
  have countPositive : (0 : Coordinate) < ((2 ^ PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial
    targets (stage + 1) : Nat) : Coordinate) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide))
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct countPositive
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct countPositive radiusSmall)
  have impossible := movement.trans_lt scaled
  rw [Geometric.DyadicCount.dyadic_count_cancel] at impossible
  exact (lt_irrefl parent.edge.pointMovement) impossible

end RootClosedState
end Purelib.Riemann.Integration.PreparedScheduledDepthFloor
