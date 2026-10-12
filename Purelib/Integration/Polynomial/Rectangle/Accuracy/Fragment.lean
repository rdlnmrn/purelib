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

variable {polynomial numerator : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial} {ambient :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {clearance :
  Purelib.Riemann.Comparison.PrimitiveEdgeComparison.RegionClearance polynomial ambient}
  {bounds : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator} {columns
    fragments : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

open Purelib in
open Purelib.Data.Rat in
/-- The retained numerator upper bound times inverse upper bound is nonnegative.

The numerator ceiling is nonnegative and the inverse ceiling is positive.
Their retained product is therefore a nonnegative scalar bound. -/
theorem product_nonnegative (bounds : Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance
  numerator) :
    0 ≤ bounds.numeratorUpper * bounds.inverseUpper :=
  Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le

namespace GridPrimitiveAccuracy

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- The retained grid primitive accuracy scale is nonnegative.

The retained grid scale is a product of the original nonnegative factors.
Its displayed square, count factors and ambient squared diagonal preserve
nonnegativity. -/
theorem scale_nonnegative (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) : 0 ≤
  request.scale := by
  rw [request.scale_eq, request.edgeScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (by decide))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Integration.Polynomial.Rectangle.Accuracy.Fragment.product_nonnegative bounds)) ambient.diagonalSq_nonneg)

open Purelib.Approximation.Rational in
open Purelib.Riemann.Integration in
/-- The retained grid global bound equals its scale times the quarter-radius decay at its index.

The global bound and scale use the same retained grid index. Their defining
scalar equations identify the original quarter-radius decay exactly. -/
theorem globalBound_eq_quarter (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) :
    request.globalBound = Geometric.Basic.quarterRadius request.scale request.index := by
  rw [request.globalBound_eq, request.edgeBound_eq, request.scale_eq]
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Riemann.Integration in
/-- Raise a grid accuracy request to the maximum of its original index and the supplied minimum.

The original scales are retained, and the edge and global bounds are recomputed at the new index with their accuracy
certificates. -/
@[expose] def atLeast (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) (minimum :
  Nat) :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target :=
  let index := max minimum request.index
  { edgeScale := request.edgeScale, edgeScale_eq := request.edgeScale_eq
    scale := request.scale, scale_eq := request.scale_eq
    index := index
    edgeBound := Geometric.Basic.quarterRadius request.edgeScale index, edgeBound_eq := rfl
    globalBound := Geometric.Basic.quarterRadius request.scale index
    globalBound_eq := by rw [request.scale_eq]; simp only [Geometric.Basic.quarterRadius_eq_mul_pow]; ring1
    accurate := (quarterRadius_antitone
      (Integration.Polynomial.Rectangle.Accuracy.Fragment.GridPrimitiveAccuracy.scale_nonnegative request)
      (Purelib.Data.Nat.Order.le_max_right _ _)).trans_lt
      ((Integration.Polynomial.Rectangle.Accuracy.Fragment.GridPrimitiveAccuracy.globalBound_eq_quarter
        request).symm.trans_lt request.accurate) }

open Purelib in
open Purelib.Riemann.Integration in
/-- The raised grid accuracy index is at least the requested minimum. -/
theorem atLeast_index_ge (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target) (minimum :
  Nat) :
    minimum ≤ (Integration.Polynomial.Rectangle.Accuracy.Fragment.GridPrimitiveAccuracy.atLeast request minimum).index
      := Purelib.Data.Nat.Order.le_max_left _ _

end GridPrimitiveAccuracy

set_option genInjectivity false in
open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- A retained fragment error allocation with compatible analytic and grid ownership bounds.

The certificate keeps the target, per-fragment allocation, ownership tolerance, residual scale and minimum index,
together with a grid request refined at least that far. -/
structure FragmentAccuracy (bounds : Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance
  numerator) (columns fragments : Nat) (target : InverseRootPolynomial.Coordinate) where
  /-- The original target tolerance is strictly positive. -/ target_positive : 0 < target
  /-- The retained allocation for a single fragment contribution. -/ perFragment : InverseRootPolynomial.Coordinate
  /-- The allocation equals the aggregate budget's per-term formula for the original fragment count. -/ perFragment_eq :
    perFragment = Budget.Aggregate.perTerm target fragments
  /-- The retained tolerance used to build the grid ownership request. -/ ownershipTolerance :
    InverseRootPolynomial.Coordinate
  /-- The ownership tolerance equals one sixty-fourth of the per-fragment allocation. -/ ownershipTolerance_eq :
    ownershipTolerance = perFragment / 64
  /-- The retained analytic residual scale. -/ residualScale : InverseRootPolynomial.Coordinate
  /-- The scale equals three times the numerator bound, inverse bound and ambient squared diagonal. -/ residualScale_eq
    : residualScale = 3 * (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq
  /-- The retained index at which the analytic residual is sufficiently small. -/ minimumIndex : Nat
  /-- Quarter-radius decay of the residual scale is below half the per-fragment allocation. -/ residual_accurate :
    Geometric.Basic.quarterRadius residualScale minimumIndex < perFragment / 2
  /-- The grid primitive accuracy request at the retained ownership tolerance. -/ grid :
    RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns ownershipTolerance
  /-- The retained grid index is at least the analytic minimum index. -/ grid_ge : minimumIndex ≤ grid.index

constructive_injectivity FragmentAccuracy

namespace FragmentAccuracy

open Purelib in
open Purelib.Data.Rat in
/-- The retained fragment residual scale is nonnegative.

The numerator and inverse ceilings retain their original nonnegative
product, and the ambient squared diagonal supplies the final nonnegative factor. -/
theorem residualScale_nonnegative (bounds : Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance
  numerator) :
    0 ≤ 3 * (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Integration.Polynomial.Rectangle.Accuracy.Fragment.product_nonnegative bounds)) ambient.diagonalSq_nonneg

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- Construct the fragment allocation, find a sufficient residual-decay index and refine the grid request to that index.

The exact per-fragment and ownership budgets are retained alongside the original geometry and polynomial bounds. -/
@[expose] def build (bounds : Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator)
  (columns fragments : Nat) (target : InverseRootPolynomial.Coordinate)
    (positive : 0 < target) : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy bounds columns
      fragments target :=
  let perFragment := Budget.Aggregate.perTerm target fragments
  have perPositive := Budget.Aggregate.perTerm_positive positive fragments
  let ownershipTolerance := perFragment / 64
  let residualScale := 3 * (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq
  let minimumIndex := Geometric.Search.firstQuarterBelow residualScale 0 (perFragment / 2)
  let grid := RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.build bounds columns ownershipTolerance
    (Fraction.Order.Field.div_pos_direct perPositive (by decide +kernel))
  { target_positive := positive, perFragment := perFragment, perFragment_eq := rfl
    ownershipTolerance := ownershipTolerance, ownershipTolerance_eq := rfl
    residualScale := residualScale, residualScale_eq := rfl
    minimumIndex := minimumIndex
    residual_accurate := Geometric.Search.firstQuarterBelow_accurate residualScale
      (Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy.residualScale_nonnegative bounds) 0 _
      (Fraction.Order.Field.div_pos_direct perPositive (by decide))
    grid := Integration.Polynomial.Rectangle.Accuracy.Fragment.GridPrimitiveAccuracy.atLeast grid minimumIndex, grid_ge
      := Integration.Polynomial.Rectangle.Accuracy.Fragment.GridPrimitiveAccuracy.atLeast_index_ge grid minimumIndex }

open Purelib in
open Purelib.Approximation.Rational in
/-- The retained per-fragment allocation is positive. -/
theorem perFragment_positive (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy bounds
  columns fragments target) : 0 < budget.perFragment := by
  rw [budget.perFragment_eq]
  exact Budget.Aggregate.perTerm_positive budget.target_positive fragments

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Thirty-two times the retained grid global bound is below half the per-fragment allocation. -/
theorem ownership_accurate (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy bounds columns
  fragments target) :
    32 * budget.grid.globalBound < budget.perFragment / 2 := by
  have estimate := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 32) budget.grid.accurate
  have paid : 32 * budget.ownershipTolerance = budget.perFragment / 2 := by
    rw [budget.ownershipTolerance_eq]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = budget.perFragment * (32 * (64 : InverseRootPolynomial.Coordinate)⁻¹) := by ring1
      _ = _ := by rw [show (32 : InverseRootPolynomial.Coordinate) * (64 : InverseRootPolynomial.Coordinate)⁻¹ = (2 :
        InverseRootPolynomial.Coordinate)⁻¹ by decide +kernel]
  exact estimate.trans_eq paid

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Riemann.Normalization in
/-- The retained analytic residual estimate is below half the per-fragment allocation. -/
theorem analytic_accurate (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy bounds columns
  fragments target) :
    48 * Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex *
      (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq < budget.perFragment / 2 := by
  have equal : 48 * Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex *
      (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq = Geometric.Basic.quarterRadius
        budget.residualScale budget.minimumIndex := by
    rw [budget.residualScale_eq]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    calc
      _ = (48 * (1 / 16 : InverseRootPolynomial.Coordinate)) * ((1 / 4) ^ budget.minimumIndex) *
        (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq := by ring1
      _ = _ := by rw [show (48 : InverseRootPolynomial.Coordinate) * (1 / 16) = 3 by decide +kernel]; ring1
  exact equal.trans_lt budget.residual_accurate

open Purelib in
open Purelib.Approximation.Rational in
/-- The squared fragment-count factor times the retained per-fragment allocation is below the original target. -/
theorem full_count_accurate (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy bounds columns
  fragments target) :
    Budget.Aggregate.countCoordinate fragments * (Budget.Aggregate.countCoordinate fragments * budget.perFragment) <
      target := by
  rw [Budget.Aggregate.countCoordinate_eq, budget.perFragment_eq]
  exact Budget.Aggregate.count_mul_perTerm_lt budget.target_positive fragments

end FragmentAccuracy

end Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
