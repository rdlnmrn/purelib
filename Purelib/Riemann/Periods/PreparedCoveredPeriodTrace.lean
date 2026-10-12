module
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
public import Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.PathArea

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
public import Purelib.Riemann.Readings.PreparedDescendantSampleBounds
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Retained primitive traces on the original period schedule

The covered ancestor supplies the primitive polynomials; every later path
uses the original scheduler's descendant cells and root ancestry. The same
computed stage pays the complete trace error, including its initial value.
The polynomial trace is still sampled on those descendants, not identified
with an independently acquired prepared mesh. Stationary handoffs retain
their exact positions in the full model and have zero trace contribution.
-/

namespace Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.SwitchedPathChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Integration.Path.IncrementArea (traceArea)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements
  (SwitchedPathChain CenteredEdge Gaussian stationaryModel stationaryModel_integralSample)

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Geometry.Path.Gaussian.Lifted in
open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Riemann.Integration in
/-- Recasting a switched chain has the same trace area as its actual edge-model list.

Stationary handoffs retain their positions in the chain and contribute zero increments to the trace. -/
theorem recastCells_traceArea {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Basic.Differential genus}
    (target : Basic.Differential genus) :
    ∀ {parents : List (CenteredEdge curve source)} {first last : Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := first) (finish := last)) (start : Gaussian),
      Path.IncrementArea.traceArea start (Paths.PathArea.increments ⟨chain.recastCells target⟩) =
        Path.IncrementArea.traceArea start (Paths.PathArea.increments ⟨(parents.map (recastCenteredEdge target)).map
          PreparedSubdivisionModelCore.CenteredEdge.model⟩)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .edge parent tail, start => by
      exact congrArg (fun value =>
        Path.BoundaryRibbon.area start (start + (recastCenteredEdge target parent).model.integralSample) + value)
        (recastCells_traceArea target tail (start + (recastCenteredEdge target parent).model.integralSample))
  | _, _, _, .stationary coordinate _ tail, start => by
      rw [PreparedSwitchedRefinements.SwitchedPathChain.recastCells]
      change Path.BoundaryRibbon.area start (start + (stationaryModel coordinate).integralSample) +
        Path.IncrementArea.traceArea (start + (stationaryModel coordinate).integralSample)
          (Paths.PathArea.increments ⟨tail.recastCells target⟩) = _
      rw [stationaryModel_integralSample, _root_.add_zero, Path.IncrementArea.area_self, _root_.zero_add]
      exact recastCells_traceArea target tail start

end Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.SwitchedPathChain

namespace Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.RootClosedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Riemann.Periods.PreparedCoveredPeriodTrace in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The original scheduled model and its flattened edge model have equal complete trace areas. -/
theorem trace_eq_flat {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source : Basic.Differential
  genus} {root : Named}
    (initial : RootClosedState curve source root) (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (stage : Nat) (start : Gaussian.Basic.Canonical) :
    Path.IncrementArea.traceArea start (Paths.PathArea.increments ((initial.states targets stage).state.model
      differential)) =
      Path.IncrementArea.traceArea start (Paths.PathArea.increments (RootClosedState.flatModel initial targets
        differential stage)) :=
  SwitchedPathChain.recastCells_traceArea
    differential (initial.states targets stage).state.chain start

end Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.RootClosedState

namespace Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.CoveredPeriodRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast movementMass_nonnegative)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
  (refinementAreaPairs refinementAreaPairs_left_total refinement_trace_bound)
open Purelib.Riemann.Readings.PreparedDescendantSampleBounds.PreparedPrimitiveChargeBounds
  (sampleDensityMaximum sampleDensityMaximum_nonnegative refinement_sample_mass_bound)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
  (remainderMaximum remainderMaximum_nonnegative coefficientMaximum coefficientMaximum_nonnegative)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_antitone)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data in
/-- The exact rational carrier of the retained trace error budget. -/
private abbrev Coordinate := Rat.Fraction.Rational

variable {genus count minimum : Nat} {curve : HyperellipticCurve genus} {source
  differential : Differential genus}
  {root : Purelib.Riemann.Topology.PreparedRefinementRootChains.Named} {initial : RootClosedState curve source root}
  {targets : List (Differential genus)} {target :
    Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedRefinementRootEndpoints in
/-- Retain root-subedge ancestry from the covered ancestor to a later original scheduled state.

Both parent lists are recast to the requested differential using the exact original refinement chain. -/
def traceRefinement (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (stage : Nat) (later : comparison.cover.stage ≤ stage) :
    RootSubedgeRefinement (comparison.cover.retained.current.state.parents.map (recastCenteredEdge differential))
      ((initial.states targets stage).state.parents.map (recastCenteredEdge differential)) := by
  have ancestry : RootSubedgeRefinement comparison.cover.retained.current.state.parents
      (initial.states targets stage).state.parents := by
    rw [comparison.cover.retained.current_eq]
    exact initial.subedgesBetween targets later
  exact RootSubedgeRefinement.recast differential ancestry

/-- The retained primitive increments sampled along the actual scheduled descendants. -/
def primitiveTracePath (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (stage : Nat) (later : comparison.cover.stage ≤ stage) : List Gaussian :=
  (refinementAreaPairs comparison.request.requests (traceRefinement comparison stage later)).map Prod.fst

open Purelib.Data.Gaussian.Norm.Sum.Basic in
/-- The descendant primitive trace sums to the original retained primitive sum. -/
theorem primitiveTracePath_total (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (stage : Nat) (later : comparison.cover.stage ≤ stage) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (primitiveTracePath comparison stage later) =
      comparison.request.primitiveSum := by
  rw [primitiveTracePath, refinementAreaPairs_left_total, comparison.request.primitiveSum_eq,
    comparison.request.increments_eq]

/-- Later scheduled descendants have movement mass at most the retained ancestor budget. -/
private theorem trace_mass_le (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (stage : Nat) (later : comparison.cover.stage ≤ stage) :
    movementMass ((initial.states targets stage).state.parents.map (recastCenteredEdge differential)) ≤
      comparison.budget.mass := by
  rw [comparison.budget.mass_eq, movementMass_recast, movementMass_recast, comparison.cover.retained.current_eq]
  exact initial.movementMass_between targets later

open Purelib.Data in
/-- A fixed bound on descendant squared samples from the retained patches and base allowance. -/
def sampleBound (comparison : CoveredPeriodRequest initial targets differential count minimum target) :
  Rat.Fraction.Rational :=
  sampleDensityMaximum comparison.request.requests * comparison.budget.mass + (5 / 2) * initial.state.scheduleBase
    targets

open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
/-- The retained descendant sample bound is nonnegative. -/
theorem sampleBound_nonnegative (comparison : CoveredPeriodRequest initial targets differential count minimum target) :
    0 ≤ sampleBound comparison :=
  add_nonneg (Arithmetic.mul_nonneg_direct (sampleDensityMaximum_nonnegative comparison.request.requests)
    comparison.budget.mass_nonnegative)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 5 / 2) (initial.state.scheduleBase_positive
      targets).le)

open Purelib.Approximation.Rational.Geometric in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The actual descendant count times its squared sample sum is bounded by the retained sample budget. -/
private theorem samples_bounded (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (member : differential ∈ targets) (stage : Nat) (later : comparison.cover.stage ≤ stage) :
    (((initial.states targets stage).state.parents.map (recastCenteredEdge differential)).length :
      Rat.Fraction.Rational) *
      Basic.gaussianNormSqSum (Paths.PathArea.increments (RootClosedState.flatModel initial targets differential stage))
        ≤
        sampleBound comparison := by
  have bounded := refinement_sample_mass_bound comparison.request.requests (traceRefinement comparison stage later)
  have allowance := (RootClosedState.flatAllowance_le initial targets differential member stage).trans
    (Basic.quarterRadius_le_scale (initial.state.scheduleBase_positive targets).le stage)
  exact bounded.trans (Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (trace_mass_le comparison stage later)
      (sampleDensityMaximum_nonnegative comparison.request.requests))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct allowance (by decide : (0 : Rat.Fraction.Rational) ≤ 5 / 2)))

open Purelib.Approximation.Rational.Geometric in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The descendant trace charge is bounded by the retained polynomial floor and geometric spatial allowance. -/
private theorem trace_charge_le (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (member : differential ∈ targets) (stage : Nat) (later : comparison.cover.stage ≤ stage) :
    (remainderMaximum comparison.request.requests * Basic.quarterRadius (initial.state.scheduleBase targets) stage +
      coefficientMaximum comparison.request.requests) *
        movementMass ((initial.states targets stage).state.parents.map (recastCenteredEdge differential)) +
      (5 / 2) * (RootClosedState.flatModel initial targets differential stage).aggregateAllowance ≤
        comparison.budget.polynomialFloor + Basic.quarterRadius comparison.budget.spatialScale stage := by
  rw [← comparison.budget.remainder_eq, ← comparison.budget.coefficient_eq]
  have rateNonnegative := add_nonneg
    (Arithmetic.mul_nonneg_direct comparison.budget.remainder_nonnegative
      (Basic.quarterRadius_nonneg (initial.state.scheduleBase_positive targets).le stage))
        comparison.budget.coefficient_nonnegative
  have paid := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (trace_mass_le comparison stage later) rateNonnegative)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (RootClosedState.flatAllowance_le initial targets differential member
      stage)
      (by decide : (0 : Rat.Fraction.Rational) ≤ 5 / 2))
  exact paid.trans_eq (by
    rw [comparison.budget.polynomialFloor_eq, comparison.budget.spatialScale_eq]
    rw [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
    ring1)

open Purelib.Approximation.Rational.Geometric in
open Purelib.Approximation.Rational.Geometric.Basic in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
/-- At every paid later stage, the retained polynomial and spatial allowances sum to less than the target. -/
private theorem trace_budget_lt (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (stage : Nat) (later : comparison.stage ≤ stage) :
    comparison.budget.polynomialFloor + Basic.quarterRadius comparison.budget.spatialScale stage < target := by
  have spatial := (quarterRadius_antitone
    (comparison.budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le) later).trans_lt
      comparison.spatial_small
  have first := Arithmetic.add_lt_add_left_direct spatial comparison.budget.polynomialFloor
  have second := Arithmetic.add_lt_add_right_direct (comparison.request.polynomialFloor_lt comparison.budget) (target /
    2)
  exact first.trans (second.trans_eq (by
    calc
      target / 2 + target / 2 = (target / 2) * 2 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open Purelib.Approximation.Rational.Geometric in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Riemann.Integration.PreparedRefinementMovement in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- Bound complete primitive-trace error at every later original period stage.

The estimate retains the starting value and actual stationary switches. The same requested stage pays the descendant
trace charge using the sample bound from the original covered patches. -/
theorem trace_accurate (comparison : CoveredPeriodRequest initial targets differential count minimum target)
    (positive : 0 < target) (member : differential ∈ targets) (stage : Nat) (later : comparison.stage ≤ stage)
    (start : Gaussian) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea start (primitiveTracePath comparison stage
      (comparison.stage_after.trans later)) -
      Path.IncrementArea.traceArea start (Paths.PathArea.increments ((initial.states targets stage).state.model
        differential))) ≤
        64 * target * (sampleBound comparison + target) + 8 * Data.Gaussian.Norm.Basic.normSq start * target := by
  rw [RootClosedState.trace_eq_flat]
  have stagePositive := comparison.stage_positive.trans_le later
  cases stage with
  | zero => exact (Nat.not_lt_zero _ stagePositive).elim
  | succ stage =>
      let children := (initial.states targets (stage + 1)).state.parents.map (recastCenteredEdge differential)
      let radius := Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1)
      have radiusNonnegative : 0 ≤ radius := Basic.quarterRadius_nonneg (initial.state.scheduleBase_positive targets).le
        _
      have movements : ∀ child ∈ children, child.edge.pointMovement ≤ radius := by
        intro child belongs
        obtain ⟨original, originalMember, rfl⟩ := List.Map.mem_map.mp belongs
        exact RootClosedState.states_childMovement_le initial targets stage originalMember
      let error := (remainderMaximum comparison.request.requests * radius + coefficientMaximum
        comparison.request.requests) *
        movementMass children + (5 / 2) * (RootClosedState.flatModel initial targets differential (stage +
          1)).aggregateAllowance
      have errorLe : error ≤ target := ((trace_charge_le comparison member _ (comparison.stage_after.trans
        later)).trans_lt
        (trace_budget_lt comparison _ later)).le
      have boundedTrace := refinement_trace_bound comparison.request.requests
        (traceRefinement comparison (stage + 1) (comparison.stage_after.trans later)) start radiusNonnegative
        (sampleBound_nonnegative comparison) movements (samples_bounded comparison member _
          (comparison.stage_after.trans later))
      have errorNonnegative : 0 ≤ error := add_nonneg
        (Arithmetic.mul_nonneg_direct
          (add_nonneg (Arithmetic.mul_nonneg_direct (remainderMaximum_nonnegative comparison.request.requests)
            radiusNonnegative)
            (coefficientMaximum_nonnegative comparison.request.requests)) (movementMass_nonnegative children))
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 5 / 2)
          (RootClosedState.flatModel initial targets differential (stage + 1)).aggregateAllowance_nonneg)
      have first := Arithmetic.mul_le_mul_direct (Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by
          decide +kernel : (0 : Rat.Fraction.Rational) ≤ 64))
        (Arithmetic.add_le_add_direct le_rfl errorLe)
        (add_nonneg (sampleBound_nonnegative comparison) errorNonnegative)
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 64) positive.le)
      have last := Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 8) (Basic.normSq_nonneg start))
      have paid := Arithmetic.add_le_add_direct first last
      have boundedTrace' : Basic.Canonical.normSq
          (Path.IncrementArea.traceArea start
              (primitiveTracePath comparison (stage + 1) (comparison.stage_after.trans later)) -
            Path.IncrementArea.traceArea start
              (Paths.PathArea.increments
                (RootClosedState.flatModel initial targets differential (stage + 1)))) ≤
            64 * error * (sampleBound comparison + error) + 8 * Basic.Canonical.normSq start * error := by
        dsimp only at boundedTrace
        simpa only [error, primitiveTracePath,
          RootClosedState.flatModel] using boundedTrace
      have paid' : 64 * error * (sampleBound comparison + error) + 8 * Basic.Canonical.normSq start * error ≤
          64 * target * (sampleBound comparison + target) + 8 * Basic.Canonical.normSq start * target := by
        simpa only [Basic.normSq_eq_canonical] using paid
      simpa only [Basic.normSq_eq_canonical] using boundedTrace'.trans paid'

end Purelib.Riemann.Periods.PreparedCoveredPeriodTrace.CoveredPeriodRequest
