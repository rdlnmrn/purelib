module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
public import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Tactic.Ring

public section

/-! Paired endpoint and corner accounting on the actual coarse grid.
Existing scalar corner banks can be paired without primitive reevaluation. -/

namespace Purelib.Riemann.Periods.BilinearGridBoundary

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.BoundaryRibbon (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub sumFin_swap)
open Purelib.Data.Vector.Basic (vectorOfFn)
open Purelib.Integration.Polynomial.Rectangle.Boundary.Corners (sum_gaps)
open Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly (SideGrid localBoundary exteriorSides horizontalSeam
  verticalSeam seamSum localBoundary_eq)

set_option genInjectivity false in
/-- Paired primitive readings at the four corners of one model rectangle. -/
structure CornerValues where
  /-- The paired reading at the lower-left corner. -/ lowerLeft : PrimitivePoint
  /-- The paired reading at the lower-right corner. -/ lowerRight : PrimitivePoint
  /-- The paired reading at the upper-left corner. -/ upperLeft : PrimitivePoint
  /-- The paired reading at the upper-right corner. -/ upperRight : PrimitivePoint

constructive_injectivity CornerValues

open Purelib.Riemann in
/-- Pair two retained scalar corner records coordinate by coordinate. -/
@[expose] def CornerValues.pair (first second : Integration.RectangularPrimitiveGluing.CornerValues) : CornerValues :=
  ⟨⟨first.lowerLeft, second.lowerLeft⟩, ⟨first.lowerRight, second.lowerRight⟩,
    ⟨first.upperLeft, second.upperLeft⟩, ⟨first.upperRight, second.upperRight⟩⟩

open Purelib.Data in
/-- A structural rectangular grid of paired primitive corner records. -/
abbrev Values (columns rows : Nat) :=
  Data.Vector (Data.Vector CornerValues (rows + 1)) (columns + 1)

open Purelib.Integration in
open Purelib.Data in
/-- Pair two cached scalar corner grids without reevaluating their primitives. -/
@[expose] def pairValues {columns rows : Nat} (first second : Polynomial.Rectangle.Boundary.Corners.Values columns rows)
  : Values columns rows :=
  Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => CornerValues.pair (first column row) (second
    column row)

open Purelib.Data in
/-- The oriented bilinear area of a closed four-corner polygon. -/
@[expose] def cornerArea (a b c d : PrimitivePoint) : Gaussian.Basic.Canonical :=
  edgeArea a b + edgeArea b c + edgeArea c d + edgeArea d a

open Purelib.Topology in
/-- Express the four-corner area using two triangles based at the first point. -/
theorem cornerArea_eq_differences (a b c d : PrimitivePoint) :
    cornerArea a b c d = edgeArea (Polygon.Stokes.PrimitivePoint.sub b a) (Polygon.Stokes.PrimitivePoint.sub c a) +
      edgeArea (Polygon.Stokes.PrimitivePoint.sub c a) (Polygon.Stokes.PrimitivePoint.sub d a) := by
  simp only [cornerArea, edgeArea, Polygon.Stokes.PrimitivePoint.sub]
  ring1

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Bound the squared bilinear corner area by sixteen times the near and diagonal bounds.

The three retained displacement certificates bound both components of the paired primitive differences from the first
corner. -/
theorem cornerArea_bound {a b c d : PrimitivePoint} {near far : Path.BoundaryRibbon.Coordinate}
    (first : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Polygon.Stokes.PrimitivePoint.sub b a) near))
      (diagonal : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Polygon.Stokes.PrimitivePoint.sub c a) far))
      (last : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Polygon.Stokes.PrimitivePoint.sub d a) near)) :
    Data.Gaussian.Norm.Basic.normSq (cornerArea a b c d) ≤ 16 * near * far := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical, cornerArea_eq_differences]
  have sumBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (edgeArea (Polygon.Stokes.PrimitivePoint.sub b a)
      (Polygon.Stokes.PrimitivePoint.sub c a))
    (edgeArea (Polygon.Stokes.PrimitivePoint.sub c a)
      (Polygon.Stokes.PrimitivePoint.sub d a))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at sumBound
  have firstBound := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound first diagonal
  have lastBound := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound diagonal last
  have scalarBound := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add firstBound lastBound) (by decide : (0 : Rat.Fraction.Rational) ≤ 2)
  exact sumBound.trans (scalarBound.trans_eq (by ring1))

section
open Purelib.Data
/-- The difference of upper and lower joining-edge areas along a horizontal seam. -/
@[expose] def horizontalEndpoint {columns rows : Nat} (values : Values columns rows)
    (column : Fin columns) (row : Fin (rows + 1)) : Gaussian.Basic.Canonical :=
  edgeArea (values column.succ row).upperLeft (values column.castSucc row).upperRight -
    edgeArea (values column.succ row).lowerLeft (values column.castSucc row).lowerRight

/-- The difference of right and left joining-edge areas along a vertical seam. -/
@[expose] def verticalEndpoint {columns rows : Nat} (values : Values columns rows)
    (column : Fin (columns + 1)) (row : Fin rows) : Gaussian.Basic.Canonical :=
  edgeArea (values column row.castSucc).upperRight (values column row.succ).lowerRight -
    edgeArea (values column row.castSucc).upperLeft (values column row.succ).lowerLeft

/-- The oriented polygon joining the four model readings at an interior grid junction. -/
@[expose] def interiorCorner {columns rows : Nat} (values : Values columns rows) (column : Fin columns) (row : Fin rows)
  : Gaussian.Basic.Canonical :=
  cornerArea (values column.castSucc row.castSucc).upperRight (values column.castSucc row.succ).lowerRight
    (values column.succ row.succ).lowerLeft (values column.succ row.castSucc).upperLeft

end

section
open Purelib.Algebra
open Purelib.Data
/-- Sum the actual joining-edge corrections on the four exterior sides.

The boundary orientation is retained; neighboring primitive models may give nonzero joins. -/
@[expose] def exteriorJoins {columns rows : Nat} (values : Values columns rows) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun column : Fin columns =>
    edgeArea (values column.succ (Fin.last rows)).upperLeft (values column.castSucc (Fin.last rows)).upperRight -
      edgeArea (values column.succ 0).lowerLeft (values column.castSucc 0).lowerRight) +
  FiniteSum.Fin.sumFin (fun row : Fin rows =>
    edgeArea (values (Fin.last columns) row.castSucc).upperRight (values (Fin.last columns) row.succ).lowerRight -
      edgeArea (values 0 row.castSucc).upperLeft (values 0 row.succ).lowerLeft)

/-- Sum every horizontal and vertical seam endpoint correction. -/
@[expose] def endpointSum {columns rows : Nat} (values : Values columns rows) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (horizontalEndpoint values column)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (verticalEndpoint values column))

/-- Sum the paired primitive corner polygons at all interior coarse junctions. -/
@[expose] def cornerSum {columns rows : Nat} (values : Values columns rows) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (interiorCorner values column))

end

open Purelib.Algebra in
open Purelib.Integration in
/-- Decompose all seam endpoint corrections into exterior joins and interior corner polygons.

The exact finite identity counts every oriented endpoint once using the same retained corner grid. -/
theorem endpointSum_eq {columns rows : Nat} (values : Values columns rows) :
    endpointSum values = exteriorJoins values + cornerSum values := by
  let hHigh := fun (column : Fin columns) (row : Fin (rows + 1)) =>
    edgeArea (values column.succ row).upperLeft (values column.castSucc row).upperRight
  let hLow := fun (column : Fin columns) (row : Fin (rows + 1)) =>
    edgeArea (values column.succ row).lowerLeft (values column.castSucc row).lowerRight
  let vHigh := fun (column : Fin (columns + 1)) (row : Fin rows) =>
    edgeArea (values column row.castSucc).upperRight (values column row.succ).lowerRight
  let vLow := fun (column : Fin (columns + 1)) (row : Fin rows) =>
    edgeArea (values column row.castSucc).upperLeft (values column row.succ).lowerLeft
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin columns =>
    Polynomial.Rectangle.Boundary.Corners.sum_gaps (hHigh column) (hLow column))
  have vertical := FiniteSum.Fin.sumFin_congr (fun row : Fin rows => Polynomial.Rectangle.Boundary.Corners.sum_gaps (fun
    column => vHigh column row) (fun column => vLow column row))
  change FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => hHigh column row - hLow column row)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => vHigh column row - vLow column row)) = _
  rw [horizontal, FiniteSum.Fin.sumFin_swap (fun column row => vHigh column row - vLow column row), vertical,
    FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add]
  rw [FiniteSum.Fin.sumFin_swap (fun row column => vHigh column.castSucc row - vLow column.succ row)]
  have internal :
      FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => hHigh column
        row.castSucc - hLow column row.succ)) +
        FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => vHigh
          column.castSucc row - vLow column.succ row)) = cornerSum values := by
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [hHigh, hLow, vHigh, vLow, interiorCorner, cornerArea]
    simp only [edgeArea]
    ring1
  calc
    _ = exteriorJoins values +
        (FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => hHigh column
          row.castSucc - hLow column row.succ)) +
          FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => vHigh
            column.castSucc row - vLow column.succ row))) := by
      dsimp only [exteriorJoins, hHigh, hLow, vHigh, vLow]
      ring1
    _ = _ := by rw [internal]

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
/-- Sum seam areas after subtracting their actual paired endpoint corrections. -/
@[expose] def correctedSeamSum {columns rows : Nat} (sides : Polynomial.Rectangle.Boundary.Assembly.SideGrid columns
  rows)
    (corners : Values columns rows) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
    Polynomial.Rectangle.Boundary.Assembly.horizontalSeam sides column row - horizontalEndpoint corners column row)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
      Polynomial.Rectangle.Boundary.Assembly.verticalSeam sides column row - verticalEndpoint corners column row))

open Purelib.Algebra in
open Purelib.Integration in
/-- The corrected seam total equals the seam sum minus the endpoint sum. -/
theorem correctedSeamSum_eq {columns rows : Nat} (sides : Polynomial.Rectangle.Boundary.Assembly.SideGrid columns rows)
    (corners : Values columns rows) :
    correctedSeamSum sides corners = Polynomial.Rectangle.Boundary.Assembly.seamSum sides - endpointSum corners := by
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin columns =>
    FiniteSum.Fin.sumFin_sub (Polynomial.Rectangle.Boundary.Assembly.horizontalSeam sides column) (horizontalEndpoint
      corners column))
  have vertical := FiniteSum.Fin.sumFin_congr (fun column : Fin (columns + 1) =>
    FiniteSum.Fin.sumFin_sub (Polynomial.Rectangle.Boundary.Assembly.verticalSeam sides column) (verticalEndpoint
      corners column))
  unfold correctedSeamSum
  rw [horizontal, vertical, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub]
  unfold Polynomial.Rectangle.Boundary.Assembly.seamSum endpointSum
  ring1

open Purelib.Integration in
/-- The local boundary minus the joined exterior equals corrected seams plus interior corner polygons.

The stitched exterior retains the actual joining edges from the same corner data. -/
theorem localBoundary_sub_stitchedExterior {columns rows : Nat} (sides : Polynomial.Rectangle.Boundary.Assembly.SideGrid
  columns rows)
    (corners : Values columns rows) :
    Polynomial.Rectangle.Boundary.Assembly.localBoundary sides - (Polynomial.Rectangle.Boundary.Assembly.exteriorSides
      sides + exteriorJoins corners) =
      correctedSeamSum sides corners + cornerSum corners := by
  rw [Polynomial.Rectangle.Boundary.Assembly.localBoundary_eq, correctedSeamSum_eq, endpointSum_eq]
  ring1

end Purelib.Riemann.Periods.BilinearGridBoundary

end
