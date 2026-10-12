module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Square.Centered

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Integration.PreparedCoveredParentLists
public import Purelib.Riemann.Integration.PreparedRefinementMovement

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Primitive coverage on the actual standard period refinement

Checked direct meshes keep each child's original clear segment. Carry its
cached uniform bounds through the existing scheduler, then select a stage
whose movement fits every retained bound. No replacement path, root owner,
or refinement schedule is constructed.
-/

namespace Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover

open Purelib.Data.Rat
open Purelib.Data.Nat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.CheckedDirectGeometry (Mesh)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents (recast)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods (grow_box_refines)
open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (RootSafeAccuracy)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

open Purelib.Data in
set_option genInjectivity false in
/-- Retain uniform bounds for the original segments with one common radius floor.

The dependent list follows the actual parent edges, allowing their bounds to pass through checked refinement while
endpoints change. -/
inductive SegmentBounds (radius : Rat.Fraction.Rational) : List (CenteredEdge curve source) → Type
  /-- The empty parent list has the common radius bound. -/ | nil : SegmentBounds radius []
  /-- Retain one original segment bound, its radius-floor proof and the bounds for the remaining parents. -/ | cons
    {parent : CenteredEdge curve source} {parents : List (CenteredEdge curve source)}
      (bounds : Bounds parent.edge.segment) (lower : radius ≤ bounds.radius)
      (tail : SegmentBounds radius parents) : SegmentBounds radius (parent :: parents)

constructive_injectivity SegmentBounds

namespace SegmentBounds

variable {radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data in
/-- Lower the common radius floor without changing any retained segment bounds. -/
@[expose] def weaken {smaller : Rat.Fraction.Rational} (order : smaller ≤ radius) :
    ∀ {parents : List (CenteredEdge curve source)}, SegmentBounds radius parents → SegmentBounds smaller parents
  | _, .nil => .nil
  | _, .cons bounds lower tail => .cons bounds (order.trans lower) (tail.weaken order)

/-- Concatenate the retained bounds in the same order as their original parent lists. -/
@[expose] def append : ∀ {first last : List (CenteredEdge curve source)},
    SegmentBounds radius first → SegmentBounds radius last → SegmentBounds radius (first ++ last)
  | _, _, .nil, last => last
  | _, _, .cons bounds lower tail, last => .cons bounds lower (tail.append last)

section
open Purelib.Data
/-- Carry the original segment bounds through a checked dyadic mesh.

Every accepted leaf retains its parent's exact segment, so the original clearance and radius evidence are reused. -/
@[expose] def mesh {parent : PreparedEdge curve source}
    (bounds : Bounds parent.segment) (lower : radius ≤ bounds.radius) {diameter : Rat.Fraction.Rational} :
    ∀ {depth : Nat} {left right : Endpoint}
      (mesh : Mesh parent diameter depth left right), SegmentBounds radius mesh.children
  | _, _, _, .leaf _ _ => .cons bounds lower .nil
  | _, _, _, .split first last => (mesh bounds lower first).append (mesh bounds lower last)

/-- Carry each original parent's bounds through its exact checked mesh and ordered child blocks. -/
@[expose] def meshes {depth : Nat} {diameter : Rat.Fraction.Rational} :
    ∀ {parents : List (CenteredEdge curve source)} (_bounds : SegmentBounds radius parents)
      (meshes : CheckedDirectMeshes depth diameter parents), SegmentBounds radius meshes.toBlocks.children
  | _, .nil, .nil => .nil
  | _, .cons bounds lower tail, .cons head rest => by
      rw [CheckedDirectMeshes.toBlocks_cons_children]
      exact (mesh bounds lower head).append (tail.meshes rest)

end

open Purelib.Curves in
open Purelib.Data in
/-- Transport retained segment bounds through the supplied root-safe refinement's actual blocks. -/
@[expose] def refine {parents : List (CenteredEdge curve source)} (bounds : SegmentBounds radius parents)
    {targets : List (Hyperelliptic.Differentials.Basic.Differential genus)} {target : Rat.Fraction.Rational} (accuracy :
      RootSafeAccuracy parents targets target) :
    SegmentBounds radius accuracy.blocks.children := by
  rw [accuracy.blocks_eq, accuracy.result.blocks_eq]
  exact bounds.meshes accuracy.result.meshes

open Purelib.Geometry in
/-- A sufficiently small parent movement puts its final point in every retained primitive neighborhood. -/
theorem finish_inside {parent : CenteredEdge curve source} (patch : PreparedPatch parent)
    (count : Nat) (small : parent.edge.pointMovement ≤ patch.bounds.radius ^ 2) :
    (patch.neighborhood count).box.Contains (parent.edge.point 1) := by
  apply (grow_box_refines _).contains
  apply (patch.seed.uniformBox_refines count).contains
  apply Rational.Box.Square.Centered.centeredBox_contains_of_normSq_sub_le patch.bounds.radius_positive.le
  rw [← parent.edge.point_zero]
  exact small

open Purelib.Curves in
open Purelib.Data in
/-- Build primitive coverage on the actual parents from their retained segment bounds.

The positive common radius and movement bounds certify each endpoint using the original segment's prepared patch. -/
@[expose] def covered (positive : 0 < radius) (count : Nat) :
    ∀ {parents : List (CenteredEdge curve source)} (_bounds : SegmentBounds radius parents),
      (∀ parent ∈ parents, parent.edge.pointMovement ≤ radius ^ 2) →
        Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count parents
  | _, .nil, _ => .nil
  | _, .cons bounds lower tail, small =>
      let patch := PreparedPatch.ofBounds _ bounds
      .cons patch (finish_inside patch count ((small _ List.mem_cons_self).trans
        (Rat.Fraction.Order.Arithmetic.pow_le_pow_direct positive.le lower 2)))
        (tail.covered positive count (fun parent member => small parent (List.mem_cons_of_mem _ member)))

end SegmentBounds

open Purelib.Data in
set_option genInjectivity false in
/-- Retain original segment bounds with one positive common radius.

The dependent bounds follow the supplied parent list and supply the fixed geometric threshold used by later scheduled
refinements. -/
structure PeriodCoverSeed (parents : List (CenteredEdge curve source)) where
  /-- The retained common radius floor for the original segments. -/ radius : Rat.Fraction.Rational
  /-- The common radius is strictly positive. -/ positive : 0 < radius
  /-- The actual original segment bounds sharing this radius floor. -/ bounds : SegmentBounds radius parents

constructive_injectivity PeriodCoverSeed

namespace PeriodCoverSeed

/-- Compute a common positive radius and cache each original segment's bounds.

Successive minima retain the radius floor for the full finite parent list; the empty list uses radius one. -/
@[expose] def build : (parents : List (CenteredEdge curve source)) → PeriodCoverSeed parents
  | [] => ⟨1, by decide, .nil⟩
  | parent :: parents =>
      let bounds := Bounds.build parent.edge.segment
      let tail := build parents
      let radius := min bounds.radius tail.radius
      ⟨radius, Fraction.Order.Basic.lt_min bounds.radius_positive tail.positive,
        .cons bounds (Fraction.Order.Basic.min_le_left _ _) (tail.bounds.weaken (Fraction.Order.Basic.min_le_right _
          _))⟩

end PeriodCoverSeed

open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain an actual scheduled state together with its inherited segment bounds.

The state is stored for executable use, while a proof identifies it with the original schedule at the specified stage.
-/
structure BoundedPeriodStage {root : Gaussian.Name.Basic.Named}
    (initial : RootClosedState curve source root) (targets : List (Hyperelliptic.Differentials.Basic.Differential
      genus))
    (radius : Rat.Fraction.Rational) (stage : Nat) where
  /-- The cached root-closed state at the retained schedule stage. -/ current : RootClosedState curve source root
  /-- The cached state equals the exact original scheduled state. -/ current_eq : current = initial.states targets stage
  /-- The inherited original segment bounds on the cached state's actual parents. -/ bounds : SegmentBounds radius
    current.state.parents

constructive_injectivity BoundedPeriodStage

namespace BoundedPeriodStage

variable {root : Purelib.Approximation.Gaussian.Name.Basic.Named}

open Purelib.Curves in
open Purelib.Data in
/-- Run the original refinement schedule while retaining its segment bounds.

Each step consumes the cached preceding state and transports the same original bounds through that step's actual
root-safe accuracy result. -/
@[expose] def build (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    {radius : Rat.Fraction.Rational} (bounds : SegmentBounds radius initial.state.parents) :
    (stage : Nat) → BoundedPeriodStage initial targets radius stage
  | 0 => ⟨initial, rfl, bounds⟩
  | stage + 1 =>
      let previous := build initial targets bounds stage
      let step := RootClosedState.Step.acquire previous.current targets (initial.state.scheduleTarget targets stage)
        (initial.state.scheduleTarget_positive targets stage)
      { current := step.next
        current_eq := by
          change (RootClosedState.Step.acquire previous.current targets _ _).next = _
          rw [previous.current_eq]
          rfl
        bounds := by
          rw [step.parents_eq]
          exact previous.bounds.refine step.accuracy }

end BoundedPeriodStage

open Purelib.Curves in
open Purelib.Approximation in
set_option genInjectivity false in
/-- Retain an arbitrarily late original schedule stage with primitive coverage.

The computed stage meets the requested minimum and a positive movement threshold. Its actual state, original bounds and
coverage remain cached together. -/
structure CoveredPeriodStage {root : Gaussian.Name.Basic.Named}
    (initial : RootClosedState curve source root) (targets : List (Hyperelliptic.Differentials.Basic.Differential
      genus)) (count minimum : Nat) where
  /-- The cached common-radius seed on the initial parents. -/ seed : PeriodCoverSeed initial.state.parents
  /-- The computed primitive-covered schedule stage. -/ stage : Nat
  /-- The computed stage meets the requested minimum. -/ stage_ge : minimum ≤ stage
  /-- The computed stage is strictly positive. -/ stage_positive : 0 < stage
  /-- The original schedule's geometric movement bound is strictly below the retained radius squared. -/ movement_small
    : Rational.Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) stage < seed.radius ^ 2
  /-- The actual scheduled state and inherited segment bounds. -/ retained : BoundedPeriodStage initial targets
    seed.radius stage
  /-- Primitive coverage on the retained state's exact current parents. -/ covered :
    Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count retained.current.state.parents

constructive_injectivity CoveredPeriodStage

namespace CoveredPeriodStage

variable {root : Purelib.Approximation.Gaussian.Name.Basic.Named}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Select and construct a sufficiently late covered stage of the original schedule.

A finite quarter-radius search and the supplied minimum determine the stage; inherited bounds and actual child movement
then certify the cached parent coverage. -/
@[expose] def acquire (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    (count minimum : Nat) : CoveredPeriodStage initial targets count minimum := by
  let seed := PeriodCoverSeed.build initial.state.parents
  let first := Rational.Geometric.Search.firstQuarterBelow (initial.state.scheduleBase targets) 0 (seed.radius ^ 2)
  let stage := max minimum first + 1
  have small : Rational.Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) stage < seed.radius ^ 2 :=
    (quarterRadius_antitone (initial.state.scheduleBase_positive targets).le
      ((Order.le_max_right _ _).trans (Nat.le_succ _))).trans_lt
      (Rational.Geometric.Search.firstQuarterBelow_accurate _ (initial.state.scheduleBase_positive targets).le 0 _
        (Rat.Fraction.Order.Arithmetic.pow_pos_direct seed.positive 2))
  let retained := BoundedPeriodStage.build initial targets seed.bounds stage
  have movements : ∀ parent ∈ retained.current.state.parents, parent.edge.pointMovement ≤ seed.radius ^ 2 := by
    rw [retained.current_eq]
    intro parent member
    exact (Integration.PreparedRefinementMovement.RootClosedState.states_childMovement_le initial targets (max minimum
      first) member).trans small.le
  exact ⟨seed, stage, (Order.le_max_left _ _).trans (Nat.le_succ _), Nat.zero_lt_succ _, small,
    retained, retained.bounds.covered seed.positive count movements⟩

open Purelib.Riemann in
open Purelib.Curves in
/-- Change the differential while reusing the cached geometric coverage and original owners. -/
@[expose] def recast {initial : RootClosedState curve source root} {targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus)} {count minimum : Nat}
    (stage : CoveredPeriodStage initial targets count minimum) (target : Hyperelliptic.Differentials.Basic.Differential
      genus) :
    Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count
      (stage.retained.current.state.parents.map (recastCenteredEdge target)) :=
  Integration.PreparedCoveredParentLists.CoveredParents.recast target stage.covered

end CoveredPeriodStage
end Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
