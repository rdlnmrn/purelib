module
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Readings.PreparedWeightedRefinementArea
public import Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-! Cached row budgets control the weighted model comparison throughout the
original schedule. Spatial refinement pays the decaying term, while the
polynomial coefficient floor remains explicit. -/
namespace Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea.WeightedRefinement (errorBudget)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay (DecayBudget)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_mul_right)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_le_scale
  quarterRadius_eq_mul_pow)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {root : Named} {target : Coordinate}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Dependent cached decay budgets for the original standard-differential request rows.

Every row uses the same retained initial root-closed schedule base, while keeping its exact request family and decay
coefficients. -/
def ScheduleBudgets (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential
  genus))
    (requests : (row : Fin genus) → RequestedParents count target
      (initial.state.parents.map (recastCenteredEdge (standardDifferential row)))) :=
  Vector.DependentVector (fun row => DecayBudget (requests row) (initial.state.scheduleBase targets))

namespace ScheduleBudgets

variable {initial : RootClosedState curve source root} {targets : List
  (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)}
  {requests : (row : Fin genus) → RequestedParents count target
    (initial.state.parents.map (recastCenteredEdge (standardDifferential row)))}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Build the original row budgets using one shared cached initial movement mass. -/
def build (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (requests : (row : Fin genus) → RequestedParents count target
      (initial.state.parents.map (recastCenteredEdge (standardDifferential row)))) :
    ScheduleBudgets initial targets requests :=
  let mass := movementMass initial.state.parents
  Vector.DependentVector.ofFn (fun row => DecayBudget.ofMass (requests row) (initial.state.scheduleBase targets) mass
    (movementMass_recast (standardDifferential row) initial.state.parents).symm)

open Purelib.Riemann.Integration in
/-- Each scheduled recast row's movement mass is bounded by its retained original budget mass. -/
private theorem mass_le (budgets : ScheduleBudgets initial targets requests) (row : Fin genus) (stage : Nat) :
    movementMass ((initial.states targets stage).state.parents.map (recastCenteredEdge (standardDifferential row))) ≤
      (budgets.get row).mass := by
  rw [(budgets.get row).mass_eq, movementMass_recast, movementMass_recast]
  exact PreparedRefinementMovement.RootClosedState.states_movementMass_le initial targets stage

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- A retained scheduled row error is bounded by its original polynomial floor plus spatial decay. -/
theorem error_le (budgets : ScheduleBudgets initial targets requests) (row : Fin genus)
    (member : standardDifferential row ∈ targets) (stage : Nat) :
    errorBudget requests (initial.states targets stage).state.parents
      (Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) stage) row ≤
        (budgets.get row).polynomialFloor + Geometric.Basic.quarterRadius (budgets.get row).spatialScale stage := by
  unfold errorBudget
  rw [← (budgets.get row).remainder_eq, ← (budgets.get row).coefficient_eq]
  have rateNonnegative := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (budgets.get row).remainder_nonnegative
      (Geometric.Basic.quarterRadius_nonneg (initial.state.scheduleBase_positive targets).le stage)) (budgets.get
        row).coefficient_nonnegative
  have paid := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (budgets.mass_le row stage) rateNonnegative)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (PreparedRootSafePeriodPrograms.RootClosedState.flatAllowance_le initial targets (standardDifferential row) member
      stage)
      (by decide : (0 : Coordinate) ≤ 5 / 2))
  exact paid.trans_eq (by
    rw [(budgets.get row).polynomialFloor_eq, (budgets.get row).spatialScale_eq]
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The genus-weighted row errors are bounded by retained floor sum plus summed spatial decay. -/
theorem weighted_error_le (budgets : ScheduleBudgets initial targets requests)
    (members : ∀ row : Fin genus, standardDifferential row ∈ targets) (stage : Nat) :
    (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests (initial.states targets stage).state.parents
      (Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) stage)) ≤
      (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor) +
        Geometric.Basic.quarterRadius ((genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get
          row).spatialScale)) stage := by
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row => budgets.error_le row (members row) stage))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  have split : FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor + Geometric.Basic.quarterRadius
    (budgets.get row).spatialScale stage) =
      FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor) +
        FiniteSum.Fin.sumFin (fun row => (budgets.get row).spatialScale) * (1 / 4 : Coordinate) ^ stage := by
    calc
      _ = FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor +
          (budgets.get row).spatialScale * (1 / 4 : Coordinate) ^ stage) :=
        FiniteSum.Fin.sumFin_congr (fun row => by rw [Geometric.Basic.quarterRadius_eq_mul_pow])
      _ = _ := by rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_right]
  rw [split] at bounded
  exact bounded.trans_eq (by rw [Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- The original genus-weighted sum of retained spatial scales is nonnegative. -/
private theorem scale_nonnegative (budgets : ScheduleBudgets initial targets requests) :
    0 ≤ (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).spatialScale) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    (FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row =>
        (budgets.get row).spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le)))

open Purelib.Algebra in
open Purelib.Approximation.Rational in
/-- Select the shared decay stage for the original genus-weighted spatial-scale sum. -/
def spatialStage (budgets : ScheduleBudgets initial targets requests) (tolerance : Coordinate) : Nat :=
  Geometric.Search.firstQuarterBelow
    ((genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).spatialScale)) 0 tolerance + 1

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- After the selected stage, the original weighted errors lie below the retained floor sum plus tolerance.

Every standard differential must belong to the original target list; the common stage and exact row-budget family
determine the same scheduled models. -/
theorem weighted_error_lt (budgets : ScheduleBudgets initial targets requests)
    (members : ∀ row : Fin genus, standardDifferential row ∈ targets)
    {tolerance : Coordinate} (positive : 0 < tolerance) (stage : Nat)
    (later : budgets.spatialStage tolerance ≤ stage) :
    (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests (initial.states targets stage).state.parents
      (Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) stage)) <
      (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor) + tolerance := by
  have indexLe := (Nat.le_succ _).trans later
  have small := (quarterRadius_antitone budgets.scale_nonnegative indexLe).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate _ budgets.scale_nonnegative 0 tolerance positive)
  exact (budgets.weighted_error_le members stage).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct small _)

end ScheduleBudgets
end Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets
