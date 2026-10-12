module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

public import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDyadicRefinements

@[expose] public section

namespace Purelib.Riemann.RootContinuation.PreparedRootSafeReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedSelection SynchronizedDirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (RootSafeAccuracy BudgetBank)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)
open Purelib.Riemann.Transport.PreparedDirectRefinementReplay

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

section
open Purelib.Curves.Hyperelliptic
/-- Restore root-safe accuracy from an observed selection and retained blocks.

Requires exact selection and block readbacks, keeps the selected meshes and allowances, and transports the original
movement certificate to those actual blocks. -/
def accuracy (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents targets target)
    (observed : selected = (RootSafeAccuracy.select parents proper targets target positive).selected)
    (blocks : SynchronizedDirectBlockRefinement selected.depth selected.rootDiameter parents)
    (equal : blocks = selected.meshes.toBlocks) : RootSafeAccuracy parents targets target where
  budgets := BudgetBank.acquire parents
  result :=
    { rootDiameter := selected.rootDiameter
      rootDiameterPositive := selected.positive
      depth := selected.depth
      meshes := selected.meshes
      allowances := selected.allowances
      blocks := blocks
      blocks_eq := equal }
  blocks := blocks
  blocks_eq := rfl
  movement := by
    change ∀ child ∈ blocks.children, child.edge.pointMovement ≤ target
    cases equal
    cases observed
    exact (RootSafeAccuracy.select parents proper targets target positive).movement

/-- Restored accuracy equals the original acquisition.

Uses the supplied selection and block equalities without replacing the retained refinement data. -/
theorem accuracy_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents targets target)
    (observed : selected = (RootSafeAccuracy.select parents proper targets target positive).selected)
    (blocks : SynchronizedDirectBlockRefinement selected.depth selected.rootDiameter parents)
    (equal : blocks = selected.meshes.toBlocks) :
    accuracy parents proper targets target positive selected observed blocks equal =
      RootSafeAccuracy.acquire parents proper targets target positive := by
  cases equal
  cases observed
  rfl

/-- Restore root-safe accuracy from the retained mesh centers.

Builds the block view of the original selected meshes using their exact center witnesses and block readback. -/
def fromCenters (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents targets target)
    (observed : selected = (RootSafeAccuracy.select parents proper targets target positive).selected)
    (centers : BankCenters selected.meshes) : RootSafeAccuracy parents targets target :=
  accuracy parents proper targets target positive selected observed
    (blocks selected.meshes centers)
    (blocks_eq selected.meshes centers)

/-- Center-based replay equals the original root-safe acquisition. -/
theorem fromCenters_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents targets target)
    (observed : selected = (RootSafeAccuracy.select parents proper targets target positive).selected)
    (centers : BankCenters selected.meshes) :
    fromCenters parents proper targets target positive selected observed centers =
      RootSafeAccuracy.acquire parents proper targets target positive :=
  accuracy_eq parents proper targets target positive selected observed _ _

end

open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
/-- Restore a root-closed refinement step from an observed selection and centers.

Retains the current closed state and uses the exact replayed accuracy certificate to construct its next state. -/
def step {root : Name.Basic.Named} (current : RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection current.state.parents targets target)
    (observed : selected = (RootSafeAccuracy.select current.state.parents current.state.proper targets target
      positive).selected)
    (centers : BankCenters selected.meshes) :
    RootClosedState.Step current targets target :=
  RootClosedState.Step.ofAccuracy current
    (fromCenters current.state.parents current.state.proper targets target positive selected observed centers)

/-- The replayed root-closed step equals the original acquired step. -/
theorem step_eq {root : Name.Basic.Named} (current : RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection current.state.parents targets target)
    (observed : selected = (RootSafeAccuracy.select current.state.parents current.state.proper targets target
      positive).selected)
    (centers : BankCenters selected.meshes) :
    step current targets target positive selected observed centers =
      RootClosedState.Step.acquire current targets target positive :=
  congrArg (RootClosedState.Step.ofAccuracy current)
    (fromCenters_eq current.state.parents current.state.proper targets target positive selected observed centers)

/-- The replayed step preserves readiness of every retained parent.

Uses the exact next-parent block readback and the original center-based readiness transport. -/
theorem step_ready {root : Name.Basic.Named} (current : RootClosedState curve source root)
    (ready : AllReady current.state.parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection current.state.parents targets target)
    (observed : selected = (RootSafeAccuracy.select current.state.parents current.state.proper targets target
      positive).selected)
    (centers : BankCenters selected.meshes) :
    AllReady
      (step current targets target positive selected observed centers).next.state.parents := by
  rw [RootClosedState.Step.parents_eq]
  exact blocks_ready selected.meshes centers ready

end Purelib.Riemann.RootContinuation.PreparedRootSafeReplay
