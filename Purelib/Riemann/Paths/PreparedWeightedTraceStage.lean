module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
public import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Riemann.Integration.PreparedScheduledDepthFloor
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths

public import Purelib.Riemann.Paths.PreparedWeightedTraceAllocation
public import Purelib.Riemann.Integration.PreparedOrientedDepthFloor

public section

/-! One original-schedule threshold pays the model error and actual spatial
depth floor at every later stage on the same retained source bank. -/
namespace Purelib.Riemann.Paths.PreparedWeightedTraceStage

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea.WeightedRefinement (errorBudget)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum coefficientMaximum_nonnegative
  remainderMaximum_nonnegative)
open Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets (ScheduleBudgets)
open Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget (coefficientTolerance)
open Purelib.Riemann.Paths.PreparedWeightedTraceAllocation (WeightedTraceAllocation)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass_nonnegative)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {root : Named} {requestTarget target sourceBound originBound resamplingScale : Coordinate}
  {initial : RootClosedState curve source root} {targets : List
    (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)}
  {requests : (row : Fin genus) → RequestedParents count requestTarget
    (initial.state.parents.map (recastCenteredEdge (standardDifferential row)))}

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Approximation in
set_option genInjectivity false in
/-- A schedule threshold paying both weighted model error and retained spatial depth.

The same original source bank, row requests and trace allocation determine the predecessor stage. Both guarantees hold
at every later stage of that schedule. -/
structure WeightedTraceStage (budgets : ScheduleBudgets initial targets requests)
    (allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale)
    (minimum : Nat) where
  /-- The retained schedule threshold sufficient for the requested spatial depth. -/ depthThreshold : Nat
  /-- The predecessor threshold combining spatial depth and weighted-error payment. -/ predecessor : Nat
  /-- The predecessor is the maximum of the error schedule stage and retained depth threshold. -/ predecessor_eq :
    predecessor = max (Integration.PreparedWeightedScheduleBudgets.ScheduleBudgets.spatialStage budgets allocation.half)
    depthThreshold
  /-- Every later schedule stage reaches the requested minimum spatial depth. -/ depth_enough : ∀ stage, predecessor ≤
    stage → minimum ≤
    Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial targets (stage + 1)
  /-- Every later schedule stage has aggregate row error strictly below the retained allocation tolerance. -/ error_lt :
    ∀ stage, predecessor ≤ stage →
    (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests (initial.states targets (stage + 1)).state.parents
      (Rational.Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1))) < allocation.tolerance

constructive_injectivity WeightedTraceStage

namespace WeightedTraceStage

open Purelib.Riemann in
open Purelib.Data in
/-- Combine a retained spatial threshold with the original weighted-error schedule.

Membership of every standard differential and the coefficient ceiling pay the allocation's two halves, while the
supplied depth threshold proves the minimum at every later schedule stage. -/
@[expose] def ofThreshold (budgets : ScheduleBudgets initial targets requests)
    (allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale)
    (members : ∀ row : Fin genus, standardDifferential row ∈ targets)
    (coefficientBound : ∀ row, coefficientMaximum (requests row) ≤
      Integration.PreparedWeightedCoefficientBudget.coefficientTolerance initial allocation.half)
    (minimum depthThreshold : Nat)
    (enough : ∀ stage, depthThreshold ≤ stage + 1 → minimum ≤
      Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial targets (stage + 1)) :
    WeightedTraceStage budgets allocation minimum := by
  let predecessor := max (Integration.PreparedWeightedScheduleBudgets.ScheduleBudgets.spatialStage budgets
    allocation.half) depthThreshold
  refine ⟨depthThreshold, predecessor, rfl, ?_, ?_⟩
  · intro stage later
    exact enough stage ((Purelib.Data.Nat.Order.le_max_right _ _).trans (later.trans (Nat.le_succ stage)))
  · intro stage later
    have spatialLater : Integration.PreparedWeightedScheduleBudgets.ScheduleBudgets.spatialStage budgets allocation.half
      ≤ stage + 1 :=
      (Purelib.Data.Nat.Order.le_max_left _ _).trans (later.trans (Nat.le_succ stage))
    have floorPaid := Integration.PreparedWeightedCoefficientBudget.coefficient_floor_paid budgets
      allocation.half_positive.le coefficientBound
    have small := (Integration.PreparedWeightedScheduleBudgets.ScheduleBudgets.weighted_error_lt budgets members
      allocation.half_positive (stage + 1) spatialLater).trans_le
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct floorPaid le_rfl)
    exact small.trans_eq allocation.halves

open Purelib.Riemann in
open Purelib.Integration in
/-- Select a combined trace stage from the original oriented parent bank.

A retained parent supplies the depth-floor witness when the bank is nonempty. The supplied empty-bank condition gives
zero requested depth without choosing a geometric witness. -/
@[expose] def build (budgets : ScheduleBudgets initial targets requests)
    (allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale)
    (members : ∀ row : Fin genus, standardDifferential row ∈ targets)
    (coefficientBound : ∀ row, coefficientMaximum (requests row) ≤
      Integration.PreparedWeightedCoefficientBudget.coefficientTolerance initial allocation.half)
    (oriented : ∀ parent ∈ initial.state.parents,
      0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (minimum : Nat) (emptyDepth : initial.state.parents = [] → minimum = 0) :
    WeightedTraceStage budgets allocation minimum := by
  cases parentsEq : initial.state.parents with
  | nil =>
      have zero := emptyDepth parentsEq
      exact ofThreshold budgets allocation members coefficientBound minimum 0
        (fun stage _ => zero.symm ▸ Nat.zero_le (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth
          initial targets (stage + 1)))
  | cons parent remaining =>
      have member : parent ∈ initial.state.parents := parentsEq.symm ▸ List.mem_cons_self
      exact ofThreshold budgets allocation members coefficientBound minimum
        (Integration.PreparedScheduledDepthFloor.RootClosedState.depthFloorStage initial targets parent minimum)
        (fun stage later => Integration.PreparedOrientedDepthFloor.RootClosedState.depthFloorStage_enough_of_oriented
          initial targets member
          (oriented parent member) minimum stage later)

variable {budgets : ScheduleBudgets initial targets requests}
  {allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale}
  {minimum : Nat}

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- Pay the complete resampling and weighted-model error from the retained trace allocation.

Every later schedule stage and sufficiently fine cover use the same nonnegative row-error sum, source and origin bounds,
and cached allocation tolerance. -/
theorem paid (selected : WeightedTraceStage (initial := initial) (targets := targets) (requests := requests)
    budgets allocation minimum) (stage : Nat) (later : selected.predecessor ≤ stage)
    {coverFloor : Nat} (coverLater : allocation.coverFloor ≤ coverFloor) :
    let error := (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests
      (initial.states targets (stage + 1)).state.parents
      (Rational.Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1)))
    2 * (Rational.Geometric.Basic.quarterRadius resamplingScale coverFloor + (64 * error * (sourceBound + error) + 8 *
      originBound * error)) ≤ target := by
  have radiusNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg
    (initial.state.scheduleBase_positive targets).le (stage + 1)
  have each (row : Fin genus) : 0 ≤ errorBudget requests
      (initial.states targets (stage + 1)).state.parents
      (Rational.Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1)) row := by
    unfold errorBudget
    exact add_nonneg
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
        (add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (remainderMaximum_nonnegative _) radiusNonnegative)
          (coefficientMaximum_nonnegative _)) (movementMass_nonnegative _))
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 5 / 2)
        (Polynomial.Gaussian.Path.Basic.PathModel.aggregateAllowance_nonneg _))
  have errorNonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le genus))
    (FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each))
  exact allocation.paid coverLater errorNonnegative (selected.error_lt stage later).le

end WeightedTraceStage
end Purelib.Riemann.Paths.PreparedWeightedTraceStage
