module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Scalar accuracy selection paying the full mesh-fragment count

Select the ownership tolerance and a common residual index before preparing
polynomials. Both count factors are paid, even when the supplied count grows
with geometric refinement. Generated alternatives satisfy the same finite
equations and inequalities, without matching the canonical selected index.
-/

namespace Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

open Purelib.Riemann.Normalization.InverseRootPolynomial

variable {polynomial numerator : Riemann.Normalization.InverseRootPolynomial.Polynomial} {ambient :
  Box} {clearance :
  RegionClearance polynomial ambient}
  {bounds : PrimitiveOverlapBounds clearance numerator} {columns
    fragments pairs : Nat} {target : Coordinate}

open Purelib in
open Purelib.Data.Rat in
/-- The retained numerator upper bound times inverse upper bound is nonnegative.

The numerator ceiling is nonnegative and the inverse ceiling is positive.
Their retained product is therefore a nonnegative scalar bound. -/
theorem product_nonnegative (bounds : PrimitiveOverlapBounds clearance
  numerator) :
    0 ≤ bounds.numeratorUpper * bounds.inverseUpper :=
  Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le

set_option genInjectivity false in
open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- A retained fragment error allocation with compatible analytic and grid ownership bounds.

The certificate keeps the target, per-fragment allocation, ownership tolerance,
residual scale and minimum index, together with a grid request refined at least
that far. The pair count selects the retained odd-power overlap weight; zero
pairs uses the original numerator and inverse bound product. -/
structure FragmentAccuracy (bounds : PrimitiveOverlapBounds clearance
  numerator) (columns fragments : Nat) (target : Coordinate) (pairs : optParam Nat 0) where
  /-- The original target tolerance is strictly positive. -/ target_positive : 0 < target
  /-- The retained allocation for a single fragment contribution. -/ perFragment : Coordinate
  /-- The allocation equals the aggregate budget's per-term formula for the original fragment count. -/ perFragment_eq :
    perFragment = Budget.Aggregate.perTerm target fragments
  /-- The retained tolerance used to build the grid ownership request. -/ ownershipTolerance :
    Coordinate
  /-- The ownership tolerance equals one sixty-fourth of the per-fragment allocation. -/ ownershipTolerance_eq :
    ownershipTolerance = perFragment / 64
  /-- The retained analytic residual scale. -/ residualScale : Coordinate
  /-- The scale equals three times the retained odd-power overlap weight and ambient squared diagonal. -/
  residualScale_eq : residualScale = 3 * bounds.weight pairs * ambient.diagonalSq
  /-- The retained index at which the analytic residual is sufficiently small. -/ minimumIndex : Nat
  /-- Quarter-radius decay of the residual scale is below half the per-fragment allocation. -/ residual_accurate :
    Geometric.Basic.quarterRadius residualScale minimumIndex < perFragment / 2
  /-- The grid primitive accuracy request at the retained ownership tolerance. -/ grid :
    GridPrimitiveAccuracy bounds columns ownershipTolerance pairs
  /-- The retained grid index is at least the analytic minimum index. -/ grid_ge : minimumIndex ≤ grid.index

constructive_injectivity FragmentAccuracy

namespace FragmentAccuracy

open Purelib in
open Purelib.Data.Rat in
/-- The retained fragment residual scale is nonnegative.

The original odd-power overlap weight is nonnegative, and the ambient
squared diagonal supplies the final nonnegative factor. -/
theorem residualScale_nonnegative (bounds : PrimitiveOverlapBounds clearance
  numerator) (pairs : optParam Nat 0) :
    0 ≤ 3 * bounds.weight pairs * ambient.diagonalSq :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide)
      (bounds.weight_nonnegative pairs)) ambient.diagonalSq_nonneg

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- Construct the fragment allocation, find a sufficient residual-decay index and refine the grid request to that index.

The exact per-fragment and ownership budgets are retained alongside the
original geometry, polynomial bounds and odd denominator power. -/
@[expose] def build (bounds : PrimitiveOverlapBounds clearance numerator)
  (columns fragments : Nat) (target : Coordinate)
    (positive : 0 < target) (pairs : optParam Nat 0) : FragmentAccuracy bounds columns
      fragments target pairs :=
  let perFragment := Budget.Aggregate.perTerm target fragments
  have perPositive := Budget.Aggregate.perTerm_positive positive fragments
  let ownershipTolerance := perFragment / 64
  let residualScale := 3 * bounds.weight pairs * ambient.diagonalSq
  let minimumIndex := Geometric.Search.firstQuarterBelow residualScale 0 (perFragment / 2)
  let grid := GridPrimitiveAccuracy.build bounds columns ownershipTolerance
    (Field.div_pos_direct perPositive (by decide +kernel)) pairs
  { target_positive := positive, perFragment := perFragment, perFragment_eq := rfl
    ownershipTolerance := ownershipTolerance, ownershipTolerance_eq := rfl
    residualScale := residualScale, residualScale_eq := rfl
    minimumIndex := minimumIndex
    residual_accurate := Geometric.Search.firstQuarterBelow_accurate residualScale
      (residualScale_nonnegative bounds pairs) 0 _
      (Field.div_pos_direct perPositive (by decide))
    grid := GridPrimitiveAccuracy.atLeast grid minimumIndex, grid_ge
      := GridPrimitiveAccuracy.atLeast_index_ge grid minimumIndex }

open Purelib in
open Purelib.Approximation.Rational in
/-- The retained per-fragment allocation is positive. -/
theorem perFragment_positive (budget : FragmentAccuracy bounds
  columns fragments target pairs) : 0 < budget.perFragment := by
  rw [budget.perFragment_eq]
  exact Budget.Aggregate.perTerm_positive budget.target_positive fragments

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Thirty-two times the retained grid global bound is below half the per-fragment allocation. -/
theorem ownership_accurate (budget : FragmentAccuracy bounds columns
  fragments target pairs) :
    32 * budget.grid.globalBound < budget.perFragment / 2 := by
  have estimate := Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : Coordinate) < 32) budget.grid.accurate
  have paid : 32 * budget.ownershipTolerance = budget.perFragment / 2 := by
    rw [budget.ownershipTolerance_eq]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = budget.perFragment * (32 * (64 : Coordinate)⁻¹) := by ring1
      _ = _ := by rw [show (32 : Coordinate) * (64 : Coordinate)⁻¹ = (2 :
        Coordinate)⁻¹ by decide +kernel]
  exact estimate.trans_eq paid

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Riemann.Normalization in
/-- The retained analytic residual estimate is below half the per-fragment allocation. -/
theorem analytic_accurate (budget : FragmentAccuracy bounds columns
  fragments target pairs) :
    48 * Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex *
      bounds.weight pairs * ambient.diagonalSq < budget.perFragment / 2 := by
  have equal : 48 * Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex *
      bounds.weight pairs * ambient.diagonalSq = Geometric.Basic.quarterRadius
        budget.residualScale budget.minimumIndex := by
    rw [budget.residualScale_eq]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    calc
      _ = (48 * (1 / 16 : Coordinate)) * ((1 / 4) ^ budget.minimumIndex) *
        bounds.weight pairs * ambient.diagonalSq := by ring1
      _ = _ := by rw [show (48 : Coordinate) * (1 / 16) = 3 by decide +kernel]; ring1
  exact equal.trans_lt budget.residual_accurate

open Purelib in
open Purelib.Approximation.Rational in
/-- The squared fragment-count factor times the retained per-fragment allocation is below the original target. -/
theorem full_count_accurate (budget : FragmentAccuracy bounds columns
  fragments target pairs) :
    Budget.Aggregate.countCoordinate fragments * (Budget.Aggregate.countCoordinate fragments * budget.perFragment) <
      target := by
  rw [Budget.Aggregate.countCoordinate_eq, budget.perFragment_eq]
  exact Budget.Aggregate.count_mul_perTerm_lt budget.target_positive fragments

end FragmentAccuracy

end Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
