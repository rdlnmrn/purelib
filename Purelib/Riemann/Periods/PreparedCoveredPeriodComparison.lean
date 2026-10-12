module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

public import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Requested primitive comparison on a covered stage of the original period

A computed covered stage supplies the primitive bank. Its descendant samples
still belong to the original schedule, with the original decay scale. Both
the polynomial floor and the spatial error are paid without requiring
primitive coverage of the original coarse parents.
-/

namespace Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann
open Purelib.Riemann.Integration.PreparedRefinementMovement.RootClosedState
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data
open Purelib.Data.Gaussian.Norm
open Purelib.Riemann.Integration.PreparedRefinementMovement
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedRefinementRootEndpoints
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus} {root : Named}

/-- Retain the root-subedge refinement across an explicit number of original schedule steps.

Composition preserves the first stage's actual parents and the exact descendant list at the final stage. -/
@[expose] def subedgesAfter (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
  (first : Nat) :
    (steps : Nat) → RootSubedgeRefinement (initial.states targets first).state.parents
      (initial.states targets (first + steps)).state.parents
  | 0 => RootContinuation.PreparedNestedRootRefinements.refl _
  | steps + 1 => RootContinuation.PreparedNestedRootRefinements.trans
      (initial.subedgesAfter targets first steps) (initial.scheduledStep targets (first + steps)).subedgeRefinement

/-- Retain the original schedule's root-subedge refinement between any ordered pair of stages. -/
@[expose] def subedgesBetween (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
    {first last : Nat} (later : first ≤ last) :
    RootSubedgeRefinement (initial.states targets first).state.parents (initial.states targets last).state.parents :=
  (initial.subedgesAfter targets first (last - first)).castChildren
    (congrArg (fun stage => (initial.states targets stage).state.parents) (by omega))

/-- Total parent movement does not increase across any finite number of original schedule steps. -/
theorem movementMass_after (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
  (first : Nat) :
    ∀ steps, movementMass (initial.states targets (first + steps)).state.parents ≤
      movementMass (initial.states targets first).state.parents
  | 0 => le_rfl
  | steps + 1 => (Step.movementMass_le
      (initial.scheduledStep targets (first + steps))).trans
      (initial.movementMass_after targets first steps)

/-- The later original schedule stage has no greater parent movement mass. -/
theorem movementMass_between (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
    {first last : Nat} (later : first ≤ last) :
    movementMass (initial.states targets last).state.parents ≤ movementMass (initial.states targets first).state.parents
      := by
  have bound := initial.movementMass_after targets first (last - first)
  rwa [show first + (last - first) = last by omega] at bound

end Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState

namespace Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann
open Purelib.Riemann.Integration.PreparedRefinementMovement.RootClosedState
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data
open Purelib.Data.Gaussian.Norm
open Purelib.Riemann.Integration.PreparedRefinementMovement
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedRefinementRootEndpoints
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover (CoveredPeriodStage)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay (DecayBudget)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (refinement_error_bound)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {root : Purelib.Riemann.Topology.PreparedRefinementRootChains.Named}

set_option genInjectivity false in
/-- A covered ancestor, primitive request and certified tail of the original period schedule.

The retained cover supplies the primitive bank, while the original schedule's decay scale and cached budget bound every
later period reading without requiring primitive coverage of the initial coarse parents. -/
structure CoveredPeriodRequest (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (count minimum : Nat) (target : Coordinate) where
  /-- The actual retained covered stage of the original schedule. -/ cover : CoveredPeriodStage initial targets count
    minimum
  /-- The controlled primitive-sum request on that cover's exact recast parents. -/ request : ControlledSumRequest
    (cover.retained.current.state.parents.map (recastCenteredEdge differential)) count target
  /-- The retained decay budget using the original schedule base and primitive requests. -/ budget : DecayBudget
    request.requests (initial.state.scheduleBase targets)
  /-- The selected finite stage for comparison with the original period tail. -/ stage : Nat
  /-- The comparison stage is no earlier than the retained covered ancestor. -/ stage_after : cover.stage ≤ stage
  /-- The comparison stage is strictly positive. -/ stage_positive : 0 < stage
  /-- The retained spatial error at the comparison stage is below half the target. -/ spatial_small :
    Basic.quarterRadius budget.spatialScale stage < target / 2

constructive_injectivity CoveredPeriodRequest

namespace CoveredPeriodRequest

variable {initial : RootClosedState curve source root} {targets : List
  (Differential genus)}
  {differential : Differential genus} {count minimum : Nat} {target :
    Coordinate}

/-- Construct a primitive tail comparison from an already retained period cover.

Recast that exact cover for the requested differential, acquire its controlled primitive sum, and cache a decay budget
and stage paying half the positive target beyond the covered ancestor. -/
@[expose] def ofCover (cover : CoveredPeriodStage initial targets count minimum) (differential : Basic.Differential
  genus)
    (target : Coordinate) (positive : 0 < target) (minimumIndex : Nat := 0) :
    CoveredPeriodRequest initial targets differential count minimum target := by
  let request := ControlledSumRequest.acquire (cover.recast differential)
    (Integration.PreparedDirectDyadicRefinements.allParentsProper_map_recast cover.retained.current.state.proper)
    target positive minimumIndex
  let budget := DecayBudget.ofMass request.requests (initial.state.scheduleBase targets) request.mass request.mass_eq
  let first := Search.firstQuarterBelow budget.spatialScale 0 (target / 2)
  let stage := max cover.stage first + 1
  have small : Basic.quarterRadius budget.spatialScale stage < target / 2 :=
    (quarterRadius_antitone (budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le)
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Nat.le_succ _))).trans_lt
      (Search.firstQuarterBelow_accurate _ (budget.spatialScale_nonnegative (initial.state.scheduleBase_positive
        targets).le)
        0 _ (Field.div_pos_direct positive (by decide)))
  exact ⟨cover, request, budget, stage, (Purelib.Data.Nat.Order.le_max_left _ _).trans (Nat.le_succ _), Nat.zero_lt_succ
    _, small⟩

/-- Acquire a covered period stage and retain its controlled primitive tail comparison.

The original schedule, differential, parent count, minimum stage and numerical floor are passed through to the retained
cover and request. -/
@[expose] def acquire (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (count minimum : Nat) (target : Coordinate) (positive : 0 < target)
    (minimumIndex : Nat := 0) : CoveredPeriodRequest initial targets differential count minimum target :=
  ofCover (CoveredPeriodStage.acquire initial targets count minimum) differential target positive minimumIndex

/-- The retained comparison stage respects the requested minimum stage. -/
theorem stage_ge (comparison : CoveredPeriodRequest initial targets differential count minimum target) :
    minimum ≤ comparison.stage := comparison.cover.stage_ge.trans comparison.stage_after

/-- Bound the primitive sum against a later flat model by the retained polynomial floor and decaying spatial error.

The differential belongs to the original target list; descendant root maps, movement mass and model allowance all come
from the same original schedule and covered ancestor. -/
private theorem error_le (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (member : differential ∈ targets) (stage : Nat) (later : comparison.cover.stage ≤ stage + 1) :
    Data.Gaussian.Norm.Basic.normSq (comparison.request.primitiveSum - (RootClosedState.flatModel initial targets
      differential
      (stage + 1)).integralSample) ≤
      comparison.budget.polynomialFloor + Basic.quarterRadius comparison.budget.spatialScale (stage + 1) := by
  let current := initial.states targets (stage + 1)
  let children := current.state.parents.map (recastCenteredEdge differential)
  let radius := Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1)
  have radiusNonnegative : 0 ≤ radius := Basic.quarterRadius_nonneg (initial.state.scheduleBase_positive targets).le _
  have movements : ∀ child ∈ children, child.edge.pointMovement ≤ radius := by
    intro child belongs
    obtain ⟨original, originalMember, rfl⟩ := List.Map.mem_map.mp belongs
    exact RootClosedState.states_childMovement_le initial targets stage originalMember
  have massBound : movementMass children ≤ comparison.budget.mass := by
    rw [comparison.budget.mass_eq, movementMass_recast, movementMass_recast, comparison.cover.retained.current_eq]
    exact initial.movementMass_between targets later
  have ancestry : RootSubedgeRefinement comparison.cover.retained.current.state.parents current.state.parents := by
    rw [comparison.cover.retained.current_eq]
    exact initial.subedgesBetween targets later
  have allowance := RootClosedState.flatAllowance_le
    initial targets differential member (stage + 1)
  have bound := refinement_error_bound comparison.request.requests
    (RootSubedgeRefinement.recast differential ancestry) movements
  rw [← comparison.budget.remainder_eq, ← comparison.budget.coefficient_eq] at bound
  have multiplierNonnegative := add_nonneg
    (Arithmetic.mul_nonneg_direct comparison.budget.remainder_nonnegative radiusNonnegative)
    comparison.budget.coefficient_nonnegative
  have paid := add_le_add (Arithmetic.mul_le_mul_of_nonneg_left_direct massBound multiplierNonnegative)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct allowance (by decide : (0 : Coordinate) ≤ 5 / 2))
  rw [comparison.request.primitiveSum_eq, comparison.request.increments_eq]
  rw [Basic.normSq_eq_canonical]
  exact (bound.trans paid).trans_eq (by
    rw [comparison.budget.polynomialFloor_eq, comparison.budget.spatialScale_eq]
    dsimp only [radius]
    rw [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- The retained primitive sum approximates every sufficiently late original switched-period reading.

Membership in the target list gives the full model comparison, retaining stationary handoffs with zero integral. The
cached polynomial floor and spatial decay together give squared error strictly below the requested target. -/
theorem accurate (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (member : differential ∈ targets) (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (comparison.request.primitiveSum - ((initial.states targets stage).state.model
      differential).integralSample) < target := by
  rw [RootClosedState.sample_eq_flat]
  have spatialSmall := (quarterRadius_antitone
    (comparison.budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le) later).trans_lt
      comparison.spatial_small
  have positive := comparison.stage_positive.trans_le later
  cases stage with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ stage =>
      have bounded := comparison.error_le member stage (comparison.stage_after.trans later)
      have strict := bounded.trans_lt (Arithmetic.add_lt_add_left_direct spatialSmall comparison.budget.polynomialFloor)
      have upper := Arithmetic.add_lt_add_right_direct (comparison.request.polynomialFloor_lt comparison.budget) (target
        / 2)
      have paid : target / 2 + target / 2 = target := by
        calc
          _ = (target / 2) * 2 := by ring1
          _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      exact strict.trans (upper.trans_eq paid)

end CoveredPeriodRequest
end Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds

end
