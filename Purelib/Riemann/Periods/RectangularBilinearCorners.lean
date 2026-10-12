module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Integration.RectangularPrimitiveCorners
public import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Tactic.Ring

@[expose] public section

/-! Corner errors for two actual translated primitive banks, with no
primitive reevaluation or independent corner-smallness assumption. -/
namespace Purelib.Riemann.Periods.RectangularBilinearCorners

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveCorners (AlignedCorners)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)

open Purelib.Integration in
/-- Bound the three translated corner differences in every coarse grid junction.

The two adjacent differences use the supplied bound, and the diagonal difference uses four times that bound, all based
at the same upper-right corner. -/
def CornerDifferences {columns rows : Nat}
    (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) (bound : Coordinate) : Prop :=
  ∀ (column : Fin columns) (row : Fin rows),
    normSq ((values column.castSucc row.succ).lowerRight -
      (values column.castSucc row.castSucc).upperRight) ≤ bound ∧
    normSq ((values column.succ row.succ).lowerLeft -
      (values column.castSucc row.castSucc).upperRight) ≤ 4 * bound ∧
    normSq ((values column.succ row.castSucc).upperLeft -
      (values column.castSucc row.castSucc).upperRight) ≤ bound

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.LinearAlgebra in
/-- Derive the actual translated corner bounds from the original grid primitive request.

The aligned cached corners, original offsets and box-refinement evidence give all three comparisons without another
primitive evaluation. -/
theorem corner_differences (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} (corners : AlignedCorners anchors offsets)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) :
    CornerDifferences corners.values request.globalBound := by
  intro column row
  rw [corners.upperRight_eq, corners.lowerRight_eq, corners.lowerLeft_eq, corners.upperLeft_eq]
  exact ⟨Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_column_bound request anchors offsets refines
    column.castSucc row.succ row.castSucc
      (geometry.lowerRight_mem column.castSucc row.succ) (geometry.upperRight_mem column.castSucc row.castSucc),
    Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets refines
      column.succ column.castSucc row.succ row.castSucc
      (geometry.lowerLeft_mem column.succ row.succ) (geometry.upperRight_mem column.castSucc row.castSucc),
    Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_row_bound request anchors offsets refines
      column.succ column.castSucc row.castSucc
      (geometry.upperLeft_mem column.succ row.castSucc) (geometry.upperRight_mem column.castSucc row.castSucc)⟩

end GridPrimitiveAccuracy

namespace CornerDifferences

open Purelib.Data.Rat in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound the paired corner area by 64 times the maximum component bound squared.

The two original differential banks retain their actual cached corner values and their separate difference certificates.
-/
theorem paired_bound {columns rows : Nat}
    {first second : Polynomial.Rectangle.Boundary.Corners.Values columns rows} {left right : Coordinate}
    (firstBound : CornerDifferences first left) (secondBound : CornerDifferences second right)
    (column : Fin columns) (row : Fin rows) :
    normSq (Periods.BilinearGridBoundary.interiorCorner
      (Periods.BilinearGridBoundary.pairValues first second) column row) ≤
      64 * (max left right) ^ 2 := by
  have a := firstBound column row
  have b := secondBound column row
  have leftLe : left ≤ max left right := Fraction.Order.Basic.le_max_left _ _
  have rightLe : right ≤ max left right := Fraction.Order.Basic.le_max_right _ _
  have diagonalLeft := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftLe (show (0 : Coordinate) ≤ 4
    by decide)
  have diagonalRight := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightLe (show (0 : Coordinate) ≤
    4 by decide)
  simp only [Periods.BilinearGridBoundary.interiorCorner, Periods.BilinearGridBoundary.pairValues,
    Vector.Basic.vectorOfFn_apply, Periods.BilinearGridBoundary.CornerValues.pair]
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  apply (Periods.BilinearGridBoundary.cornerArea_bound
    (near := max left right) (far := 4 * max left right) ?_ ?_ ?_).trans_eq (by ring1)
  · exact ⟨a.1.trans leftLe, b.1.trans rightLe⟩
  · exact ⟨a.2.1.trans diagonalLeft, b.2.1.trans diagonalRight⟩
  · exact ⟨a.2.2.trans leftLe, b.2.2.trans rightLe⟩

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound the sum of paired corner areas using only the coarse junction count.

The squared count factor is the product of coarse rows and columns squared; the bound is independent of any fine
subdivision depth. -/
theorem paired_total_bound {columns rows : Nat}
    {first second : Polynomial.Rectangle.Boundary.Corners.Values columns rows} {left right : Coordinate}
    (firstBound : CornerDifferences first left) (secondBound : CornerDifferences second right) :
    normSq (Periods.BilinearGridBoundary.cornerSum
      (Periods.BilinearGridBoundary.pairValues first second)) ≤
      64 * ((columns : Coordinate) * (rows : Coordinate)) ^ 2 * (max left right) ^ 2 := by
  have rowBound (column : Fin columns) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => Periods.BilinearGridBoundary.interiorCorner
        (Periods.BilinearGridBoundary.pairValues first second) column row)) ≤
      (rows : Coordinate) ^ 2 * (64 * (max left right) ^ 2) := by
    apply Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    intro row
    have scalar := paired_bound firstBound secondBound column row
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => Periods.BilinearGridBoundary.interiorCorner
      (Periods.BilinearGridBoundary.pairValues first second) column row))
    ((rows : Coordinate) ^ 2 * (64 * (max left right) ^ 2)) rowBound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans_eq (by ring1)

end CornerDifferences
end Purelib.Riemann.Periods.RectangularBilinearCorners
