module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Pay the weighted coefficient floor before acquiring source polynomials,
using only genus and the original movement mass. -/
namespace Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum)
open Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets (ScheduleBudgets)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast movementMass_nonnegative)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {root : Named} {target : Coordinate}
  {initial : RootClosedState curve source root} {targets : List
    (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)}
  {requests : (row : Fin genus) → RequestedParents count target
    (initial.state.parents.map (recastCenteredEdge (standardDifferential row)))}

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- A shared coefficient cap bounds the original weighted floor by genus squared times initial movement mass. -/
theorem coefficient_floor_le (budgets : ScheduleBudgets initial targets requests) {cap : Coordinate}
    (bounded : ∀ row, coefficientMaximum (requests row) ≤ cap) :
    (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor) ≤
      (genus : Coordinate)^2 * movementMass initial.state.parents * cap := by
  have each (row : Fin genus) : (budgets.get row).polynomialFloor ≤ cap * movementMass initial.state.parents := by
    rw [(budgets.get row).polynomialFloor_eq, (budgets.get row).coefficient_eq,
      (budgets.get row).mass_eq, movementMass_recast]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (bounded row) (movementMass_nonnegative _)
  have total := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  exact total.trans_eq (by rw [FiniteSum.Fin.Rational.sum_constant]; ring1)

open Purelib.Approximation.Rational in
/-- Allocate coefficient accuracy from the original allowance and genus-squared movement mass. -/
def coefficientTolerance (initial : RootClosedState curve source root) (allowance : Coordinate) : Coordinate :=
  Budget.Weighted.allowance allowance ((genus : Coordinate)^2 * movementMass initial.state.parents)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- A positive original allowance gives a positive retained coefficient tolerance. -/
theorem coefficientTolerance_positive (initial : RootClosedState curve source root)
    {allowance : Coordinate} (positive : 0 < allowance) : 0 < coefficientTolerance initial allowance :=
  Budget.Weighted.allowance_positive positive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (movementMass_nonnegative _))

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The retained coefficient tolerance pays the original genus-weighted polynomial floor within its allowance.

The same initial movement mass and original row maxima determine the weight used by the constructive allowance bound. -/
theorem coefficient_floor_paid (budgets : ScheduleBudgets initial targets requests) {allowance : Coordinate}
    (nonnegative : 0 ≤ allowance)
    (bounded : ∀ row, coefficientMaximum (requests row) ≤ coefficientTolerance initial allowance) :
    (genus : Coordinate) * FiniteSum.Fin.sumFin (fun row => (budgets.get row).polynomialFloor) ≤ allowance :=
  (coefficient_floor_le budgets bounded).trans
    (Budget.Weighted.mul_allowance_le nonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (movementMass_nonnegative _)))

end Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
