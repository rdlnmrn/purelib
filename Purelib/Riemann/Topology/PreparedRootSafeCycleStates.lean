module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Periods.PeriodMatrix

public import Purelib.Riemann.RootContinuation.PreparedClosedBankRoots
public import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
public import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Accurate root-closed refinement states of the actual A-cycle banks

Every stage retains the original switched integration interface, together
with operational closure of its actual nonstationary parents.  The common
depth is selected for both root safety and the finite differential family.
These states start at the existing owner-closed schedule's exact initial
model; equality with that schedule's older later-depth choices is not assumed.
-/

namespace Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy (RootSafeAccuracy reindexCompatible
  reindexCompatible_allowance)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of root-preserving refinement targets. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState SwitchedPathChain)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- A closed switched state whose exact parent chain returns to one retained root name.

The lifted endpoint equality and root-chain certificate refer to the same original parents; neither geometric closure
nor root-name closure replaces the other. -/
structure RootClosedState (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus) (root : Named) where
  /-- The exact retained switched state and its original centered parents. -/ state : DirectSwitchedState curve
    differential
  /-- The retained lifted final point equals the retained starting point. -/ closed : state.finish = state.start
  /-- The exact parent root chain starts and finishes at the retained root name. -/ roots : RootChain state.parents root
    root

constructive_injectivity RootClosedState

namespace RootClosedState

variable {root : Named}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A checked accurate refinement retaining its exact next closed state and child-parent identity.

The root-safe accuracy result supplies the original subedge witnesses, while equalities link the next state's
computation and parents to those exact checked blocks. -/
structure Step (current : RootClosedState curve differential root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Fraction.Rational) where
  /-- The root-safe accurate refinement of the current state's exact parents. -/ accuracy : RootSafeAccuracy
    current.state.parents targets target
  /-- The retained next closed state with its exact root-chain certificate. -/ next : RootClosedState curve differential
    root
  /-- The next switched state is exactly refinement by the retained accuracy result. -/ next_eq : next.state =
    current.state.refine accuracy.result
  /-- The next state's parent list is exactly the retained checked block children. -/ parents_eq : next.state.parents =
    accuracy.blocks.children

constructive_injectivity Step

namespace Step

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct the next closed state from the supplied root-safe accuracy result.

The original closing equality is retained and the root chain is transported through the exact checked children using the
blocks identity. -/
def ofAccuracy (current : RootClosedState curve differential root)
    {targets : List (Differentials.Basic.Differential genus)} {target : Fraction.Rational}
    (accuracy : RootSafeAccuracy current.state.parents targets target) : Step current targets target := by
  let nextState := current.state.refine accuracy.result
  let next : RootClosedState curve differential root :=
    ⟨nextState, current.closed, by
      change RootChain accuracy.result.blocks.children root root
      rw [← accuracy.blocks_eq]
      exact accuracy.rootChain current.roots⟩
  exact ⟨accuracy, next, rfl, congrArg (fun blocks => blocks.children) accuracy.blocks_eq.symm⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Acquire a root-safe accurate step for the retained proper parents and positive target budget. -/
def acquire (current : RootClosedState curve differential root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Fraction.Rational) (positive : 0 < target) :
      Step current targets target :=
  ofAccuracy current (PreparedRootSafeAccuracy.RootSafeAccuracy.acquire current.state.parents current.state.proper
    targets target positive)

variable {current : RootClosedState curve differential root} {targets : List
  (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)} {target : Purelib.Data.Rat.Fraction.Rational}

/-- The checked refinement step preserves the original lifted starting point. -/
theorem start_eq (step : Step current targets target) : step.next.state.start = current.state.start := by
  rw [step.next_eq]
  rfl

/-- The checked refinement step preserves the original lifted final point. -/
theorem finish_eq (step : Step current targets target) : step.next.state.finish = current.state.finish := by
  rw [step.next_eq]
  rfl

/-- The checked root-safe step preserves the stationary switch count. -/
theorem switchCount_eq (step : Step current targets target) :
    step.next.state.chain.switchCount = current.state.chain.switchCount := by
  rw [step.next_eq]
  exact current.state.refine_switchCount step.accuracy.result

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transport the checked compatible refinement to the next state's exact recast parent list. -/
def compatible (step : Step current targets target) (memberDifferential : Differentials.Basic.Differential genus) :
    Basic.PathModel.CompatibleConstantPathRefinement
      ((current.state.parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)
      ((step.next.state.parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model) :=
  reindexCompatible (congrArg (fun parents =>
    (parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model) step.parents_eq.symm)
    (step.accuracy.compatible memberDifferential)

/-- Read the original parent-to-child root-subedge witnesses on the exact next-state parents. -/
def subedgeRefinement (step : Step current targets target) :
    RootSubedgeRefinement current.state.parents step.next.state.parents :=
  step.accuracy.subedgeRefinement.castChildren step.parents_eq.symm

section
open Purelib.Curves.Hyperelliptic
open Purelib.Integration.Polynomial.Gaussian.Path
/-- A requested differential's step comparison costs at most twice the old flat allowance plus the target. -/
theorem comparisonAllowance_le (step : Step current targets target)
    (memberDifferential : Differentials.Basic.Differential genus) (member : memberDifferential ∈ targets) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (step.compatible
      memberDifferential)) ≤
      2 * (Basic.PathModel.mk
        ((current.state.parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)).aggregateAllowance
          + target := by
  rw [compatible, reindexCompatible_allowance]
  exact step.accuracy.comparisonAllowance_le memberDifferential member

/-- Every requested differential's next flat model meets the retained target allowance. -/
theorem flatAllowance_le (step : Step current targets target)
    (memberDifferential : Differentials.Basic.Differential genus) (member : memberDifferential ∈ targets) :
    (Basic.PathModel.mk
      ((step.next.state.parents.map (recastCenteredEdge memberDifferential)).map CenteredEdge.model)).aggregateAllowance
        ≤ target := by
  rw [step.parents_eq]
  exact step.accuracy.modelAllowance_le memberDifferential member

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The next switched model allowance is bounded by the original switch factor times the target. -/
theorem modelAllowance_le (step : Step current targets target)
    (memberDifferential : Differentials.Basic.Differential genus) (member : memberDifferential ∈ targets) :
    (step.next.state.model memberDifferential).aggregateAllowance ≤ current.state.chain.switchFactor * target := by
  have bound := SwitchedPathChain.recastCells_aggregateAllowance_le_switchFactor memberDifferential
    step.next.state.chain
  have factorEq : step.next.state.chain.switchFactor = current.state.chain.switchFactor := by
    unfold SwitchedPathChain.switchFactor
    rw [step.switchCount_eq]
  rw [factorEq] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (step.flatAllowance_le memberDifferential member) current.state.chain.switchFactor_positive.le)

end Step

section
open Purelib.Curves.Hyperelliptic
/-- Iterate checked root-safe steps from the exact initial closed state.

Every stage retains the same root-name endpoint and uses targets prescribed by the initial state's geometric schedule.
-/
def states (initial : RootClosedState curve differential root) (targets : List (Differentials.Basic.Differential genus))
  :
    Nat → RootClosedState curve differential root
  | 0 => initial
  | index + 1 =>
      let current := states initial targets index
      (Step.acquire current targets (initial.state.scheduleTarget targets index)
        (initial.state.scheduleTarget_positive targets index)).next

/-- The exact root-safe step at the retained stage and original schedule target. -/
def scheduledStep (initial : RootClosedState curve differential root) (targets : List (Differentials.Basic.Differential
  genus)) (index : Nat) :
    Step (initial.states targets index) targets (initial.state.scheduleTarget targets index) :=
  Step.acquire (initial.states targets index) targets (initial.state.scheduleTarget targets index)
    (initial.state.scheduleTarget_positive targets index)

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- Compose the retained subedge witnesses from the initial parents to the requested stage.

The construction starts with the exact identity refinement and preserves each stage's original parent-child relation
when composing successors. -/
def statesSubedges (initial : RootClosedState curve differential root) (targets : List (Differentials.Basic.Differential
  genus)) :
    (index : Nat) → RootSubedgeRefinement initial.state.parents (initial.states targets index).state.parents
  | 0 => PreparedNestedRootRefinements.refl initial.state.parents
  | index + 1 => PreparedNestedRootRefinements.trans (initial.statesSubedges targets index) (initial.scheduledStep
    targets index).subedgeRefinement

open Purelib.Curves.Hyperelliptic
/-- Every root-safe stage retains the original stationary switch count. -/
theorem states_switchCount (initial : RootClosedState curve differential root) (targets : List
  (Differentials.Basic.Differential genus)) :
    ∀ index, (initial.states targets index).state.chain.switchCount = initial.state.chain.switchCount
  | 0 => rfl
  | index + 1 => (initial.scheduledStep targets index).switchCount_eq.trans (states_switchCount initial targets index)

/-- Each successor model meets the original switch-factor-adjusted scheduled target. -/
theorem states_modelAllowance_le (initial : RootClosedState curve differential root)
    (targets : List (Differentials.Basic.Differential genus)) (memberDifferential : Differentials.Basic.Differential
      genus)
    (member : memberDifferential ∈ targets) (index : Nat) :
    ((initial.states targets (index + 1)).state.model memberDifferential).aggregateAllowance ≤
      initial.state.chain.switchFactor * initial.state.scheduleTarget targets index := by
  have bound := (initial.scheduledStep targets index).modelAllowance_le memberDifferential member
  have factorEq : (initial.states targets index).state.chain.switchFactor = initial.state.chain.switchFactor := by
    unfold SwitchedPathChain.switchFactor
    rw [initial.states_switchCount targets index]
  rw [factorEq] at bound
  exact bound

end RootClosedState

end Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints

namespace Purelib.Riemann.Topology.PreparedRootSafeCycleStates.ClosedBoundaryDoublePath

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Retain the owner-closed tour's exact switched state, closing equality and boundary-bank root chain. -/
def rootClosedInitial (tour : ClosedBoundaryDoublePath curve) (differential : Differentials.Basic.Differential genus) :
    RootClosedState curve differential (ownerName tour.joined.data.forwardOwner) where
  state := (PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule tour differential).toDifferential.initial
  closed := (PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule tour differential).toDifferential.closed
  roots := PreparedClosedBankRoots.ClosedBoundaryDoublePath.initialRootChain tour differential

end Purelib.Riemann.Topology.PreparedRootSafeCycleStates.ClosedBoundaryDoublePath

namespace Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Topology in
/-- Read the requested root-safe A-cycle stage using its original owner-closed seed and standard differential family. -/
def ownerClosedARootState {genus : Nat} (curve : Basic.HyperellipticCurve genus) (index : Fin genus) (stage : Nat) :
    RootClosedState curve (PeriodMatrix.standardDifferential index)
      (ownerName (PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeed curve
        index).joined.data.forwardOwner) :=
  let seed := PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeed curve index
  let differential := PeriodMatrix.standardDifferential index
  let targets := (PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule seed
    differential).toDifferential.targets
  (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial seed differential).states targets stage

end Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementPrograms
