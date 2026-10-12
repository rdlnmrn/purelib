module

import Purelib.Algebra.FiniteSum.Fin

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Exact coarse-grid boundary assembly with independent cell primitives

Each cell may supply different primitive values along a shared side.  The
local boundary sum equals the exterior sides plus every oriented seam gap.
After retaining open seam endpoint corrections, the remainder is exactly the
fixed-grid corner term.  No exact primitive gluing is assumed.
-/

namespace Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly

open Purelib.Integration.Path.BoundaryRibbon (Gaussian Coordinate)

open Purelib.Integration.Path in
set_option genInjectivity false in
/-- Four oriented Gaussian side-area readings for one rectangular cell. -/
structure Sides where
  /-- The oriented bottom-side area reading. -/ bottom : BoundaryRibbon.Gaussian
  /-- The oriented right-side area reading. -/ right : BoundaryRibbon.Gaussian
  /-- The oriented top-side area reading. -/ top : BoundaryRibbon.Gaussian
  /-- The oriented left-side area reading. -/ left : BoundaryRibbon.Gaussian

constructive_injectivity Sides

open Purelib.Integration.Polynomial.Rectangle in
/-- The original rectangular grid of four-side area readings. -/
abbrev SideGrid (columns rows : Nat) := Fin (columns + 1) → Fin (rows + 1) → Boundary.Assembly.Sides

section
open Purelib.Algebra
open Purelib.Integration.Polynomial.Rectangle
/-- Sum bottom plus right minus top minus left over all retained grid cells. -/
def localBoundary {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
    (sides column row).bottom + (sides column row).right - (sides column row).top - (sides column row).left))

/-- The signed sum of the four outer side readings of the exact grid. -/
def exteriorSides {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => (sides column 0).bottom - (sides column (Fin.last rows)).top) +
    FiniteSum.Fin.sumFin (fun row => (sides (Fin.last columns) row).right - (sides 0 row).left)

end

section
open Purelib.Integration.Polynomial.Rectangle
/-- The right-side reading of the left cell minus the left-side reading of its right neighbor. -/
def horizontalSeam {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) (column : Fin columns) (row :
  Fin (rows + 1)) : Gaussian :=
  (sides column.castSucc row).right - (sides column.succ row).left

/-- The bottom-side reading of the upper cell minus the top-side reading of its lower neighbor. -/
def verticalSeam {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) (column : Fin (columns + 1))
  (row : Fin rows) : Gaussian :=
  (sides column row.succ).bottom - (sides column row.castSucc).top

end

section
open Purelib.Algebra
open Purelib.Integration.Polynomial.Rectangle
/-- Sum all horizontal and vertical seam differences over the retained grid. -/
def seamSum {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (Boundary.Assembly.horizontalSeam sides column)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (Boundary.Assembly.verticalSeam sides column))

/-- The total cell boundary equals the exterior sides plus the exact interior seam sum. -/
theorem localBoundary_eq {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows) :
    Boundary.Assembly.localBoundary sides = Boundary.Assembly.exteriorSides sides + Boundary.Assembly.seamSum sides :=
      by
  have cells : Boundary.Assembly.localBoundary sides =
      FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => (sides column row).bottom - (sides column
        row).top)) +
        FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => (sides column row).right - (sides column
          row).left)) := by
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    ring1
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin (columns + 1) =>
    Boundary.Corners.sum_forward_gaps (fun row => (sides column row).bottom) (fun row => (sides column row).top))
  have vertical := FiniteSum.Fin.sumFin_congr (fun row : Fin (rows + 1) =>
    Boundary.Corners.sum_gaps (fun column => (sides column row).right) (fun column => (sides column row).left))
  rw [cells, horizontal, FiniteSum.Fin.sumFin_swap (fun column row => (sides column row).right - (sides column
    row).left),
    vertical, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_swap (fun row column => (sides
      column.castSucc row).right - (sides column.succ row).left)]
  unfold Boundary.Assembly.exteriorSides Boundary.Assembly.seamSum Boundary.Assembly.horizontalSeam
    Boundary.Assembly.verticalSeam
  ring1

/-- Subtract each retained corner endpoint correction from its corresponding seam difference. -/
def correctedSeamSum {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows)
    (corners : Boundary.Corners.Values columns rows) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => Boundary.Assembly.horizontalSeam sides column row
    - Boundary.Corners.horizontalEndpoint corners column row)) +
    FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => Boundary.Assembly.verticalSeam sides column row
      - Boundary.Corners.verticalEndpoint corners column row))

/-- The corrected seam sum is the raw seam sum minus the exact endpoint sum. -/
theorem correctedSeamSum_eq {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows)
    (corners : Boundary.Corners.Values columns rows) :
    Boundary.Assembly.correctedSeamSum sides corners = Boundary.Assembly.seamSum sides - Boundary.Corners.endpointSum
      corners := by
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin columns =>
    FiniteSum.Fin.sumFin_sub (Boundary.Assembly.horizontalSeam sides column) (Boundary.Corners.horizontalEndpoint
      corners column))
  have vertical := FiniteSum.Fin.sumFin_congr (fun column : Fin (columns + 1) =>
    FiniteSum.Fin.sumFin_sub (Boundary.Assembly.verticalSeam sides column) (Boundary.Corners.verticalEndpoint corners
      column))
  unfold Boundary.Assembly.correctedSeamSum
  rw [horizontal, vertical, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub]
  unfold Boundary.Assembly.seamSum Boundary.Corners.endpointSum
  ring1

end

open Purelib.Integration.Polynomial.Rectangle in
/-- Subtracting the stitched exterior from local boundary leaves corrected seams plus interior corner areas.

The exterior uses both outer side readings and exterior joins. The remaining terms retain the original seam differences
and four-cell corner corrections separately. -/
theorem localBoundary_sub_stitchedExterior {columns rows : Nat} (sides : Boundary.Assembly.SideGrid columns rows)
    (corners : Boundary.Corners.Values columns rows) :
    Boundary.Assembly.localBoundary sides - (Boundary.Assembly.exteriorSides sides + Boundary.Corners.exteriorJoins
      corners) =
      Boundary.Assembly.correctedSeamSum sides corners + Boundary.Corners.cornerSum corners := by
  rw [Boundary.Assembly.localBoundary_eq, Boundary.Assembly.correctedSeamSum_eq, Boundary.Corners.endpointSum_eq]
  ring1

end Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
