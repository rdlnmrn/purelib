module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Root-safe common refinements with finite-family accuracy

The checked selector verifies geometry and the actual finite-family allowance
before materializing centres. Cached fixed-box budgets establish root gluing
through finite comparison subdivisions, independently of integration depth.
The actual synchronized blocks are evaluated once and retained as data.
-/

namespace Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (CompatibleConstantPathRefinement)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

section
open Purelib.Integration
/-- Transport a checked integration refinement along its child-list equality. -/
@[expose] def reindexCompatible {parents first second : List Polynomial.Gaussian.Cell.Basic.CellModel}
    (equal : first = second) (refinement : CompatibleConstantPathRefinement parents first) :
    CompatibleConstantPathRefinement parents second := equal ▸ refinement

/-- Reindexing the child-list presentation preserves the exact comparison allowance. -/
theorem reindexCompatible_allowance {parents first second : List Polynomial.Gaussian.Cell.Basic.CellModel}
    (equal : first = second) (refinement : CompatibleConstantPathRefinement parents first) :
    (Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      (reindexCompatible equal refinement)) =
      (Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      refinement) := by
  cases equal
  rfl

end

set_option genInjectivity false in
/-- Cached root and polynomial budgets indexed by the original prepared parent list.

Each budget depends on its parent geometry independently of the requested differential family and accuracy. -/
inductive BudgetBank : List (CenteredEdge curve differential) → Type 2
  /-- The empty parent list has an empty retained budget bank. -/ | nil : BudgetBank []
  /-- Retain one parent budget together with the exact tail bank. -/ | cons {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)}
      (head : ParentBudget parent.edge) (tail : BudgetBank parents) : BudgetBank (parent :: parents)

constructive_injectivity BudgetBank

namespace BudgetBank

/-- Acquire and retain one root-comparison budget for each prepared parent. -/
@[expose] def acquire : (parents : List (CenteredEdge curve differential)) → BudgetBank parents
  | [] => .nil
  | parent :: parents => .cons (ParentBudget.acquire parent.edge) (acquire parents)

open Purelib.Riemann
open Purelib.Data
/-- Transport the incoming root chain through the actual synchronized child blocks.

Each parent uses its cached fixed-box budget, preserving both endpoint names at every accepted common depth. -/
@[expose] def rootChain : ∀ {parents : List (CenteredEdge curve differential)} {commonDepth : Nat} {diameter :
  Rat.Fraction.Rational}
    (_ : BudgetBank parents) (blocks : SynchronizedDirectBlockRefinement commonDepth diameter parents),
    ∀ {first last : Named}, RootChain parents first last →
      RootChain blocks.children first last
  | [], _, _, .nil, .nil, _, _, .nil equivalent => .nil equivalent
  | _ :: _, _, _, .cons head tail, .cons block _ _ blocks, _, _, .cons _ entry remaining =>
      let safe : EndpointSafeBlock _ :=
        ⟨head, block⟩
      ((Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChain safe).changeStart entry).append
        (tail.rootChain blocks remaining)

/-- Retain all-query root maps on the same synchronized children.

The block grouping and child data agree with those consumed by the root chain and integration comparison. -/
@[expose] def subedgeRefinement : ∀ {parents : List (CenteredEdge curve differential)} {commonDepth : Nat} {diameter :
  Rat.Fraction.Rational}
    (_ : BudgetBank parents) (blocks : SynchronizedDirectBlockRefinement commonDepth diameter parents),
    RootSubedgeRefinement parents blocks.children
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons block _ _ blocks =>
      let safe : EndpointSafeBlock _ :=
        ⟨head, block⟩
      .cons block.chain (RootContinuation.PreparedSubedgeRootQueries.EndpointSafeBlock.subedges safe)
        (tail.subedgeRefinement blocks)

end BudgetBank

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- A finite-family refinement with cached root budgets and the exact synchronized children.

The result retains the original accuracy selection, its child-block identity and a movement bound for every actual
child. -/
structure RootSafeAccuracy (parents : List (CenteredEdge curve differential))
    (targets : List (Hyperelliptic.Differentials.Basic.Differential genus)) (target : Rat.Fraction.Rational) where
  /-- The retained root-comparison budget bank for the original parents. -/ budgets : BudgetBank parents
  /-- The checked finite-differential-family accuracy result. -/ result : DifferentialAccurateDirectRefinement parents
    targets target
  /-- The cached synchronized child blocks at the retained depth and diameter. -/ blocks :
    SynchronizedDirectBlockRefinement result.depth result.rootDiameter parents
  /-- The cached blocks are exactly those stored in the accuracy result. -/ blocks_eq : blocks = result.blocks
  /-- Every actual child's geometric movement is at most the target. -/ movement : ∀ child ∈ blocks.children,
    child.edge.pointMovement ≤ target

constructive_injectivity RootSafeAccuracy

namespace RootSafeAccuracy

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Synchronized children beyond the common accuracy depth meet the movement bound.

The retained maximum bounds both the current parent depth and the original
tail depth. Every selected child keeps its original geometric movement estimate. -/
theorem synchronized_movement_le {accuracy : Rat.Fraction.Rational} (positive : 0 < accuracy) :
    ∀ {depth : Nat} {diameter : Rat.Fraction.Rational} {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth diameter parents),
      commonAccuracyDepth accuracy parents ≤ depth → ∀ child ∈ blocks.children, child.edge.pointMovement ≤ accuracy
  | _, _, _, .nil, _, child, member => by cases member
  | depth, _, parent :: _, .cons block depthEq _ tail, enough, child, member => by
      rcases List.Membership.mem_append.mp member with member | member
      · have small := Rational.Geometric.Search.firstQuarterBelow_accurate
          (geometricMovement parent.edge.segment parent.edge.left.parameter parent.edge.request.endpoint.parameter)
          (Gaussian.Norm.Basic.normSq_nonneg _) 0 accuracy positive
        have later := quarterRadius_antitone
          (scale := geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) (Gaussian.Norm.Basic.normSq_nonneg _)
          ((Nat.Order.le_max_left _ _).trans enough)
        have bounded := Paths.PreparedPrimitivePaths.block_movement_le block member
        rw [depthEq] at bounded
        exact bounded.trans ((later.trans_lt small).le)
      · exact synchronized_movement_le positive tail ((Nat.Order.le_max_right _ _).trans enough) child member

section
open Purelib.Curves
open Purelib.Data
/-- The finite-family refinement accuracy is at most its positive target.

The original nonnegative coefficient makes its denominator at least one, so
dividing the retained target cannot increase the requested accuracy. -/
theorem accuracy_le_target (parents : List (CenteredEdge curve differential)) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    {target : Rat.Fraction.Rational} (positive : 0 < target) : differentialRefinementAccuracy parents targets target ≤
      target := by
  unfold differentialRefinementAccuracy
  have coefficient := differentialRefinementCoefficient_nonnegative parents targets
  have denominatorPositive : 0 < differentialRefinementCoefficient parents targets + 1 := by
    have atLeastOne := Rat.Fraction.Order.Arithmetic.add_le_add_direct coefficient (le_refl (1 : Rat.Fraction.Rational))
    have positiveOne : (0 : Rat.Fraction.Rational) < 0 + 1 := by decide
    exact positiveOne.trans_le atLeastOne
  apply (Rat.Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
  have oneLe : (1 : Rat.Fraction.Rational) ≤ differentialRefinementCoefficient parents targets + 1 := by
    simpa only [Rat.Fraction.Field.zero_add] using
      Rat.Fraction.Order.Arithmetic.add_le_add_direct coefficient (le_refl (1 : Rat.Fraction.Rational))
  calc
    target = target * 1 := by ring1
    _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe positive.le
/-- A successful finite proposal search returns at least its starting depth.

Each retained recursive attempt advances that depth by one. A successful
original selection carries the exact depth of the attempt that produced it. -/
theorem search_depth (parents : List (CenteredEdge curve differential))
    (proper : AllParentsProper parents) (targets : List (Hyperelliptic.Differentials.Basic.Differential genus)) (target
      : Rat.Fraction.Rational) :
    ∀ fuel depth rootBits (selected : CheckedSelection parents targets target),
      searchSelection parents proper targets target fuel depth rootBits = some selected →
      depth ≤ selected.depth
  | 0, _, _, _, observed => by cases observed
  | fuel + 1, depth, rootBits, selected, observed => by
      unfold searchSelection at observed
      dsimp only at observed
      split at observed
      · exact (Nat.le_succ depth).trans (search_depth parents proper targets target fuel _ _ selected observed)
      · split at observed
        · exact (Nat.le_succ depth).trans (search_depth parents proper targets target fuel _ _ selected observed)
        · have equal := Option.some.inj observed
          cases equal
          exact le_rfl
end

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- A checked finite-family selection with geometric shrinking for its actual children.

The movement certificate uses the same selected meshes and requested target. -/
structure Selection (parents : List (CenteredEdge curve differential))
    (targets : List (Hyperelliptic.Differentials.Basic.Differential genus)) (target : Rat.Fraction.Rational) where
  /-- The retained checked selection of common depth, root diameter and allowances. -/ selected : CheckedSelection
    parents targets target
  /-- Every child of the selected meshes meets the target movement bound. -/ movement : ∀ child ∈
    selected.meshes.toBlocks.children, child.edge.pointMovement ≤ target

constructive_injectivity Selection

section
open Purelib.Curves
open Purelib.Data
/-- Select a finite-family refinement starting at the geometric accuracy floor.

Reuse the finite proposal search and its uniform fallback; cached root-comparison clearance imposes no additional
integration-depth floor. -/
@[expose] def select (parents : List (CenteredEdge curve differential)) (proper : AllParentsProper parents)
    (targets : List (Hyperelliptic.Differentials.Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive :
      0 < target) :
    Selection parents targets target :=
  let depth := commonAccuracyDepth target parents
  let rootBits := proposedRootBits parents.length (familyForecast parents targets) target
  match observed : searchSelection parents proper targets target 8 depth rootBits with
  | some selected => ⟨selected, synchronized_movement_le positive selected.meshes.toBlocks
      (search_depth parents proper targets target 8 depth rootBits selected observed)⟩
  | none =>
      let selected := uniformSelection parents proper targets target positive
      let accuracy := differentialRefinementAccuracy parents targets target
      have enough : commonAccuracyDepth accuracy parents ≤ selected.depth := Nat.Order.le_max_right _ _
      ⟨selected, fun child member =>
        (synchronized_movement_le (differentialRefinementAccuracy_positive parents targets positive)
          selected.meshes.toBlocks enough child member).trans (accuracy_le_target parents targets positive)⟩

/-- Materialize one certified refinement selection and retain its exact cached child blocks.

Store the parent root budgets alongside geometric movement and finite-family accuracy certificates. -/
@[expose] def acquire (parents : List (CenteredEdge curve differential)) (proper : AllParentsProper parents)
    (targets : List (Hyperelliptic.Differentials.Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive :
      0 < target) :
    RootSafeAccuracy parents targets target :=
  let budgets := BudgetBank.acquire parents
  let selection := select parents proper targets target positive
  let selected := selection.selected
  let blocks := selected.meshes.toBlocks
  let result : DifferentialAccurateDirectRefinement parents targets target :=
    { rootDiameter := selected.rootDiameter
      rootDiameterPositive := selected.positive
      depth := selected.depth
      meshes := selected.meshes
      allowances := selected.allowances
      blocks := blocks
      blocks_eq := rfl }
  ⟨budgets, result, blocks, rfl, selection.movement⟩

end

variable {parents : List (CenteredEdge curve differential)} {targets : List
  (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)} {target : Purelib.Data.Rat.Fraction.Rational}

/-- Extend an original root chain through the retained cached child blocks. -/
@[expose] def rootChain (safe : RootSafeAccuracy parents targets target) {first last : Named}
    (roots : RootChain parents first last) : RootChain safe.blocks.children first last :=
  safe.budgets.rootChain safe.blocks roots

/-- Read the retained all-query parent-to-child root refinement. -/
@[expose] def subedgeRefinement (safe : RootSafeAccuracy parents targets target) :
    RootSubedgeRefinement parents safe.blocks.children :=
  safe.budgets.subedgeRefinement safe.blocks

open Purelib.Curves in
/-- Read the exact integration comparison for any differential on the cached geometry.

The comparison preserves the same parent and child models after recasting their differential, even outside the selected
finite family. -/
@[expose] def compatible (safe : RootSafeAccuracy parents targets target) (memberDifferential :
  Hyperelliptic.Differentials.Basic.Differential genus) :
    CompatibleConstantPathRefinement ((parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)
      ((safe.blocks.children.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model) :=
  reindexCompatible (congrArg (fun blocks =>
    (blocks.children.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model) safe.blocks_eq.symm)
    (safe.result.compatible memberDifferential)

open Purelib.Curves
open Purelib.Integration
/-- A selected differential's comparison allowance is bounded by twice its original aggregate allowance plus the target.
-/
theorem comparisonAllowance_le (safe : RootSafeAccuracy parents targets target)
    (memberDifferential : Hyperelliptic.Differentials.Basic.Differential genus) (member : memberDifferential ∈ targets)
      :
    (Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      (safe.compatible memberDifferential)) ≤
      2 * (Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)).aggregateAllowance + target :=
          by
  rw [compatible, reindexCompatible_allowance]
  exact safe.result.comparisonAllowance_le memberDifferential member

/-- A selected differential's actual cached child model meets the target aggregate allowance. -/
theorem modelAllowance_le (safe : RootSafeAccuracy parents targets target)
    (memberDifferential : Hyperelliptic.Differentials.Basic.Differential genus) (member : memberDifferential ∈ targets)
      :
    (Polynomial.Gaussian.Path.Basic.PathModel.mk
      ((safe.blocks.children.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)).aggregateAllowance ≤
        target := by
  rw [safe.blocks_eq]
  exact safe.result.modelAllowance_le memberDifferential member

end RootSafeAccuracy

end Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
