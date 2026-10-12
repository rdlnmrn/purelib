module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Integration.RectangularPrimitiveGluing
public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Assembly of open seam endpoints at coarse grid corners

Interior endpoint corrections form a closed four-value polygon.  Its area
depends quadratically on differences of nearby primitive values, not on their
absolute translations.  Exterior endpoints remain as explicit joining edges
between successive local boundary traces.  All sums use the fixed coarse
grid, independently of later spatial refinement.
-/

namespace Purelib.Integration.Polynomial.Rectangle.Boundary.Corners

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Path.BoundaryRibbon (Gaussian Coordinate area area_bound)

open Purelib.Integration.Path in
/-- Sum the four oriented corner edges in southwest, northwest, northeast, southeast order. -/
def cornerArea (southWest northWest northEast southEast : BoundaryRibbon.Gaussian) : Gaussian :=
  BoundaryRibbon.area southWest northWest + BoundaryRibbon.area northWest northEast + BoundaryRibbon.area northEast
    southEast + BoundaryRibbon.area southEast southWest

open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- The four-corner area is the sum of two skew areas formed from differences at the southwest corner. -/
theorem cornerArea_eq_differences (a b c d : BoundaryRibbon.Gaussian) :
    Polynomial.Rectangle.Boundary.Corners.cornerArea a b c d = BoundaryRibbon.area (b - a) (c - a) + BoundaryRibbon.area
      (c - a) (d - a) := by
  apply Basic.ext <;> simp only [Polynomial.Rectangle.Boundary.Corners.cornerArea, BoundaryRibbon.area,
    Data.Gaussian.Basic.conj, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;>
      ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- Near-corner and opposite-corner norm bounds control the squared corner area by sixteen times their product. -/
theorem cornerArea_bound {a b c d : BoundaryRibbon.Gaussian} {near far : BoundaryRibbon.Coordinate}
    (nearNonnegative : 0 ≤ near) (farNonnegative : 0 ≤ far)
    (first : Data.Gaussian.Norm.Basic.normSq (b - a) ≤ near) (diagonal : Data.Gaussian.Norm.Basic.normSq (c - a) ≤ far)
      (last :
      Data.Gaussian.Norm.Basic.normSq (d - a) ≤ near) :
    Data.Gaussian.Norm.Basic.normSq (Polynomial.Rectangle.Boundary.Corners.cornerArea a b c d) ≤ 16 * near * far := by
  have firstProduct := Fraction.Order.Arithmetic.mul_le_mul_direct first diagonal (Norm.Basic.normSq_nonneg _)
    nearNonnegative
  have lastProduct := Fraction.Order.Arithmetic.mul_le_mul_direct diagonal last (Norm.Basic.normSq_nonneg _)
    farNonnegative
  have firstArea : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (b - a) (c - a)) ≤ 4 * near * far := by
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq (b - a) * Data.Gaussian.Norm.Basic.normSq (c - a) :=
        BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq (b - a) * Data.Gaussian.Norm.Basic.normSq (c - a)) := by ring1
      _ ≤ 4 * (near * far) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstProduct (by decide)
      _ = _ := by ring1
  have lastArea : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (c - a) (d - a)) ≤ 4 * far * near := by
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq (c - a) * Data.Gaussian.Norm.Basic.normSq (d - a) :=
        BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq (c - a) * Data.Gaussian.Norm.Basic.normSq (d - a)) := by ring1
      _ ≤ 4 * (far * near) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastProduct (by decide)
      _ = _ := by ring1
  rw [Polynomial.Rectangle.Boundary.Corners.cornerArea_eq_differences]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstArea lastArea) (by decide)).trans_eq
      (by ring1))

open Purelib.Algebra in
open Purelib.Integration.Path in
/-- Split a nonempty finite sum into all but its last entry and its last entry. -/
private theorem sum_last {count : Nat} (values : Fin (count + 1) → BoundaryRibbon.Gaussian) :
    FiniteSum.Fin.sumFin values = FiniteSum.Fin.sumFin (fun index : Fin count => values index.castSucc) + values
      (Fin.last count) := by
  induction count with
  | zero =>
      rw [FiniteSum.Fin.sumFin_succ]
      change values 0 + 0 = 0 + values 0
      ring1
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ (fun index : Fin (count + 1) => values index.castSucc)]
      have tail := ih (fun index => values index.succ)
      rw [tail]
      have normalized : FiniteSum.Fin.sumFin (fun index : Fin count => values index.castSucc.succ) =
          FiniteSum.Fin.sumFin (fun index : Fin count => values index.succ.castSucc) :=
        FiniteSum.Fin.sumFin_congr (fun index => congrArg values (Fin.castSucc_succ index).symm)
      rw [normalized]
      change values 0 + (FiniteSum.Fin.sumFin (fun index : Fin count => values index.succ.castSucc) + values (Fin.last
        (count + 1))) =
        (values 0 + FiniteSum.Fin.sumFin (fun index : Fin count => values index.succ.castSucc)) + values (Fin.last
          (count + 1))
      ring1

section
open Purelib.Algebra
open Purelib.Integration
open Purelib.Integration.Path
/-- A sum of upper-minus-lower gaps splits into the outer endpoint gap and consecutive interior gaps. -/
theorem sum_gaps {count : Nat} (high low : Fin (count + 1) → BoundaryRibbon.Gaussian) :
    FiniteSum.Fin.sumFin (fun index => high index - low index) = high (Fin.last count) - low 0 +
      FiniteSum.Fin.sumFin (fun index : Fin count => high index.castSucc - low index.succ) := by
  rw [FiniteSum.Fin.sumFin_sub, Polynomial.Rectangle.Boundary.Corners.sum_last high, FiniteSum.Fin.sumFin_succ low,
    FiniteSum.Fin.sumFin_sub]
  ring1

/-- A sum of lower-minus-upper gaps splits into the first-lower minus last-upper endpoint difference and consecutive
forward gaps. -/
theorem sum_forward_gaps {count : Nat} (low high : Fin (count + 1) → BoundaryRibbon.Gaussian) :
    FiniteSum.Fin.sumFin (fun index => low index - high index) = low 0 - high (Fin.last count) +
      FiniteSum.Fin.sumFin (fun index : Fin count => low index.succ - high index.castSucc) := by
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_succ low, Polynomial.Rectangle.Boundary.Corners.sum_last high,
    FiniteSum.Fin.sumFin_sub]
  ring1

end

open Purelib.Data in
open Purelib.Riemann.Integration in
/-- A retained rectangular vector grid of four-corner values for every cell. -/
abbrev Values (columns rows : Nat) :=
  Data.Vector (Data.Vector RectangularPrimitiveGluing.CornerValues (rows + 1)) (columns + 1)

section
open Purelib.Integration
open Purelib.Integration.Path
/-- The upper minus lower endpoint correction across a retained horizontal pair of cells. -/
def horizontalEndpoint {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows)
    (column : Fin columns) (row : Fin (rows + 1)) : Gaussian :=
  BoundaryRibbon.area (values column.succ row).upperLeft (values column.castSucc row).upperRight -
    BoundaryRibbon.area (values column.succ row).lowerLeft (values column.castSucc row).lowerRight

/-- The right minus left endpoint correction across a retained vertical pair of cells. -/
def verticalEndpoint {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows)
    (column : Fin (columns + 1)) (row : Fin rows) : Gaussian :=
  BoundaryRibbon.area (values column row.castSucc).upperRight (values column row.succ).lowerRight -
    BoundaryRibbon.area (values column row.castSucc).upperLeft (values column row.succ).lowerLeft

end

open Purelib.Integration in
/-- The oriented area of the four original cell readings meeting at an interior grid corner. -/
def interiorCorner {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) (column :
  Fin columns) (row : Fin rows) : Gaussian :=
  Polynomial.Rectangle.Boundary.Corners.cornerArea (values column.castSucc row.castSucc).upperRight (values
    column.castSucc row.succ).lowerRight
    (values column.succ row.succ).lowerLeft (values column.succ row.castSucc).upperLeft

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- The signed sum of joining areas along the four exterior sides of the retained corner grid.

The orientation fixes each sign and keeps the joining edges between distinct neighboring readings; those readings need
not agree. -/
def exteriorJoins {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) : Gaussian
  :=
  FiniteSum.Fin.sumFin (fun column : Fin columns =>
    BoundaryRibbon.area (values column.succ (Fin.last rows)).upperLeft (values column.castSucc (Fin.last
      rows)).upperRight -
      BoundaryRibbon.area (values column.succ 0).lowerLeft (values column.castSucc 0).lowerRight) +
  FiniteSum.Fin.sumFin (fun row : Fin rows =>
    BoundaryRibbon.area (values (Fin.last columns) row.castSucc).upperRight (values (Fin.last columns)
      row.succ).lowerRight -
      BoundaryRibbon.area (values 0 row.castSucc).upperLeft (values 0 row.succ).lowerLeft)

section
open Purelib.Algebra
open Purelib.Integration
/-- Sum the retained horizontal and vertical seam endpoint corrections over the original grid. -/
def endpointSum {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (Polynomial.Rectangle.Boundary.Corners.horizontalEndpoint
    values column)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (Polynomial.Rectangle.Boundary.Corners.verticalEndpoint
      values column))

/-- Sum the four-cell corner areas over the exact interior grid corners. -/
def cornerSum {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (Polynomial.Rectangle.Boundary.Corners.interiorCorner values
    column))

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- The seam endpoint sum equals the exterior joining areas plus the interior corner sum.

Each original seam endpoint occurs exactly once, either in an exterior joining edge or in the four-reading polygon
around its original interior vertex. -/
theorem endpointSum_eq {columns rows : Nat} (values : Polynomial.Rectangle.Boundary.Corners.Values columns rows) :
    Polynomial.Rectangle.Boundary.Corners.endpointSum values = Polynomial.Rectangle.Boundary.Corners.exteriorJoins
      values + Polynomial.Rectangle.Boundary.Corners.cornerSum values := by
  let hHigh := fun (column : Fin columns) (row : Fin (rows + 1)) =>
    BoundaryRibbon.area (values column.succ row).upperLeft (values column.castSucc row).upperRight
  let hLow := fun (column : Fin columns) (row : Fin (rows + 1)) =>
    BoundaryRibbon.area (values column.succ row).lowerLeft (values column.castSucc row).lowerRight
  let vHigh := fun (column : Fin (columns + 1)) (row : Fin rows) =>
    BoundaryRibbon.area (values column row.castSucc).upperRight (values column row.succ).lowerRight
  let vLow := fun (column : Fin (columns + 1)) (row : Fin rows) =>
    BoundaryRibbon.area (values column row.castSucc).upperLeft (values column row.succ).lowerLeft
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
          column.castSucc row - vLow column.succ row)) = Polynomial.Rectangle.Boundary.Corners.cornerSum values := by
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [hHigh, hLow, vHigh, vLow, Polynomial.Rectangle.Boundary.Corners.interiorCorner,
      Polynomial.Rectangle.Boundary.Corners.cornerArea]
    apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re, Basic.sub_im,
      Basic.add_re,
      Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  calc
    _ = Polynomial.Rectangle.Boundary.Corners.exteriorJoins values +
        (FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => hHigh column
          row.castSucc - hLow column row.succ)) +
          FiniteSum.Fin.sumFin (fun column : Fin columns => FiniteSum.Fin.sumFin (fun row : Fin rows => vHigh
            column.castSucc row - vLow column.succ row))) := by
      dsimp only [Polynomial.Rectangle.Boundary.Corners.exteriorJoins, hHigh, hLow, vHigh, vLow]
      ring1
    _ = _ := by rw [internal]

end Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
