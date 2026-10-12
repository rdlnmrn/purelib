module
import Purelib.Data.List.Append
import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

public section

/-! Exact nested dyadic paths of the actual root-closed period schedule. -/
namespace Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths.PreparedRefinementRootEndpoints

open Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (BudgetBank RootSafeAccuracy)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained scheduled primitive paths. -/
private abbrev Coordinate := Fraction.Rational

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
/-- The retained checked meshes realize the budget bank's exact dyadic subedge paths. -/
theorem BudgetBank.checked_dyadicPaths {parents : List (CenteredEdge curve source)}
    {depth : Nat} {diameter : Fraction.Rational} (budgets : BudgetBank parents)
    (meshes : CheckedDirectMeshes depth diameter parents) :
    PreparedNestedDyadicPaths.DyadicPaths depth (budgets.subedgeRefinement meshes.toBlocks) := by
  induction budgets with
  | nil => cases meshes; trivial
  | cons head tail ih =>
      cases meshes with
      | cons mesh meshes =>
          constructor
          · intro value fine
            exact
              PreparedDirectDyadicRefinements.checkedParentBlock_primitive_refined_increments
              _ mesh value fine
          · exact ih meshes

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
/-- The retained root-safe accuracy result realizes its original dyadic subedge paths. -/
theorem RootSafeAccuracy.dyadicPaths {parents : List (CenteredEdge curve source)}
    {targets : List (Differentials.Basic.Differential genus)} {target : Fraction.Rational}
    (safe : RootSafeAccuracy parents targets target) :
    PreparedNestedDyadicPaths.DyadicPaths safe.result.depth safe.subedgeRefinement := by
  unfold RootSafeAccuracy.subedgeRefinement
  rw [safe.blocks_eq, safe.result.blocks_eq]
  exact BudgetBank.checked_dyadicPaths safe.budgets safe.result.meshes

end Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths.PreparedRefinementRootEndpoints

namespace Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths.RootClosedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Integration.Path.BoundaryRibbon (Coordinate Gaussian)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (RootSafeAccuracy)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState (Step)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {root :
  Purelib.Approximation.Gaussian.Name.Basic.Named}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Paths in
/-- A root-closed step's child primitive increments equal its original parent increments at the retained extra depth. -/
theorem Step.primitive_refined_increments {current : RootClosedState curve source root}
    {targets : List (Differentials.Basic.Differential genus)} {target : Fraction.Rational} (step : Step current targets
      target)
    (value : BoundaryRibbon.Gaussian → BoundaryRibbon.Gaussian) (fine : Nat) :
    (step.next.state.parents.map (fun child =>
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0 1)).flatten =
      (current.state.parents.map (fun parent =>
        DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter))
          (step.accuracy.result.depth + fine) 0 1)).flatten := by
  rw [step.parents_eq, step.accuracy.blocks_eq, step.accuracy.result.blocks_eq]
  exact PreparedCheckedPrimitivePaths.PreparedDirectDyadicRefinements.CheckedDirectMeshes.primitive_refined_increments
    step.accuracy.result.meshes value fine

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
/-- A root-closed refinement step retains its exact dyadic path identities through the original child-list equality. -/
theorem Step.dyadicPaths {current : RootClosedState curve source root}
    {targets : List (Differentials.Basic.Differential genus)} {target : Fraction.Rational} (step : Step current targets
      target) :
    PreparedNestedDyadicPaths.DyadicPaths step.accuracy.result.depth step.subedgeRefinement :=
  PreparedNestedDyadicPaths.DyadicPaths.castChildren
    (PreparedScheduledPrimitivePaths.PreparedRefinementRootEndpoints.RootSafeAccuracy.dyadicPaths step.accuracy)
    step.parents_eq.symm

open Purelib.Curves.Hyperelliptic in
/-- Sum the actual dyadic depths selected by the original scheduled root-closed steps. -/
@[expose] def spatialDepth (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus)) : Nat → Nat
  | 0 => 0
  | stage + 1 => spatialDepth initial targets stage + (initial.scheduledStep targets stage).accuracy.result.depth

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Every scheduled state retains the exact initial-parent dyadic paths at its accumulated spatial depth.

The proof composes the original root-subedge witnesses and their actual selected depths, preserving the same initial
parents and ordered refinements. -/
theorem states_dyadicPaths (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus)) (stage : Nat) :
    PreparedNestedDyadicPaths.DyadicPaths (spatialDepth initial targets stage) (initial.statesSubedges targets stage) :=
      by
  induction stage with
  | zero =>
      change PreparedNestedDyadicPaths.DyadicPaths 0 (PreparedNestedRootRefinements.refl initial.state.parents)
      generalize initial.state.parents = parents
      induction parents with
      | nil => trivial
      | cons parent parents ih =>
          constructor
          · intro value fine
            change DyadicPrimitivePaths.dyadicIncrements _ fine 0 1 ++ [] = DyadicPrimitivePaths.dyadicIncrements _ (0 +
              fine) 0 1
            rw [Purelib.Data.List.Append.append_nil, Nat.zero_add]
          · exact ih
  | succ stage ih =>
      change PreparedNestedDyadicPaths.DyadicPaths
        (spatialDepth initial targets stage + (initial.scheduledStep targets stage).accuracy.result.depth)
        (PreparedNestedRootRefinements.trans
          (initial.statesSubedges targets stage) (initial.scheduledStep targets stage).subedgeRefinement)
      exact PreparedNestedDyadicPaths.DyadicPaths.trans ih
        (Step.dyadicPaths (initial.scheduledStep targets stage))

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Paths in
/-- A scheduled state's primitive increments flatten to the initial parents at the accumulated plus extra depth. -/
theorem states_primitive_refined_increments (initial : RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (value : BoundaryRibbon.Gaussian →
      BoundaryRibbon.Gaussian) (stage fine : Nat) :
    ((initial.states targets stage).state.parents.map (fun child =>
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0 1)).flatten =
      (initial.state.parents.map (fun parent =>
        DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter))
          (spatialDepth initial targets stage + fine) 0 1)).flatten := by
  exact PreparedNestedDyadicPaths.DyadicPaths.flatten
    (states_dyadicPaths initial targets stage) value fine

end Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths.RootClosedState
