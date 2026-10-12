module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
public import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Tactic.Ring

public section

/-!
# Exact exterior-minus-holes accounting on the actual branch grid

Regular cells and branch holes retain their literal four-edge grid loops.
The partition theorem and adjacent-edge cancellation give the punctured
surface boundary with every hole oriented clockwise.  This constructs the
base-grid incidence needed by a two-sheet cut surface, not its sheet gluing
or its symplectic A/B boundary word.
-/

namespace Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole FaceSplit PuncturedFaces)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues sumValues sumValues_congr sumValues_neg)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}

namespace RegularFace

/-- The literal four-edge grid boundary of the retained regular cell. -/
@[expose] def boundary (face : RegularFace bank) : Geometry.Grid.Walks.Walk bank.grid face.cell.box.anchor
  face.cell.box.anchor :=
  Geometry.Grid.CellBoundary.Cell.boundaryWalk face.cell face.member

/-- A retained regular face's boundary has zero raw winding. -/
theorem boundary_winding (face : RegularFace bank) : rawWinding face.boundary.path = 0 :=
  (Geometry.Grid.CellBoundary.Cell.boundaryWalk_winding face.cell face.member).trans face.winding_zero

end RegularFace

namespace BranchHole

/-- The literal four-edge grid boundary of the retained branch-hole cell. -/
@[expose] def boundary (hole : BranchHole bank) : Geometry.Grid.Walks.Walk bank.grid hole.cell.box.anchor
  hole.cell.box.anchor :=
  Geometry.Grid.CellBoundary.Cell.boundaryWalk hole.cell hole.member

/-- Reverse the retained branch-hole boundary to its inward orientation. -/
@[expose] def inwardBoundary (hole : BranchHole bank) : Geometry.Grid.Walks.Walk bank.grid hole.cell.box.anchor
  hole.cell.box.anchor :=
  hole.boundary.reverse

/-- The retained branch-hole boundary has raw winding four. -/
theorem boundary_winding (hole : BranchHole bank) : rawWinding hole.boundary.path = 4 := by
  rw [boundary, Geometry.Grid.CellBoundary.Cell.boundaryWalk_winding, ← hole.box_eq]
  exact hole.state.rawWindingFour

/-- The inward branch-hole boundary has raw winding minus four. -/
theorem inwardBoundary_winding (hole : BranchHole bank) : rawWinding hole.inwardBoundary.path = -4 := by
  rw [inwardBoundary, Geometry.Grid.Winding.Walk.reverse_winding, hole.boundary_winding]

/-- The inward hole walk reads as the negative of its actual cell-boundary value. -/
theorem inwardBoundary_value (hole : BranchHole bank) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    values.walk hole.inwardBoundary = -values.cellBoundary hole.cell := by
  rw [inwardBoundary, values.walk_reverse]
  exact congrArg Neg.neg (Geometry.Grid.CellBoundary.Cell.boundaryWalk_value hole.cell hole.member values)

end BranchHole

/-- The regular and hole sums together equal the original indexed cell sum.

Both lists are read from the same ordered classification spine, so every original occurrence is retained. -/
theorem FaceSplit.sum_eq (value : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve) → Gaussian.Basic.Canonical) :
    ∀ {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))} (split
      : FaceSplit bank cells),
      Geometry.Grid.CellBoundary.sumValues (fun face => value face.cell) split.regulars +
        Geometry.Grid.CellBoundary.sumValues (fun hole => value hole.cell) split.holes =
          Geometry.Grid.CellBoundary.sumValues value cells
  | _, .nil => by change (0 : Gaussian.Basic.Canonical) + 0 = 0; ring1
  | _, .regular face tail => by
      change (value face.cell + Geometry.Grid.CellBoundary.sumValues (fun face => value face.cell) tail.regulars) +
        Geometry.Grid.CellBoundary.sumValues (fun hole => value hole.cell) tail.holes = value face.cell +
          Geometry.Grid.CellBoundary.sumValues value _
      rw [add_assoc, tail.sum_eq value]
  | _, .hole face tail => by
      change Geometry.Grid.CellBoundary.sumValues (fun face => value face.cell) tail.regulars +
        (value face.cell + Geometry.Grid.CellBoundary.sumValues (fun hole => value hole.cell) tail.holes) = value
          face.cell + Geometry.Grid.CellBoundary.sumValues value _
      rw [← tail.sum_eq value]
      ring1

namespace PuncturedFaces

/-- The regular-cell and hole-boundary sums equal the retained grid perimeter. -/
theorem boundary_balance (faces : PuncturedFaces bank) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun face => values.cellBoundary face.cell) faces.regulars +
      Geometry.Grid.CellBoundary.sumValues (fun hole => values.cellBoundary hole.cell) faces.holes = values.perimeter
        bank.grid := by
  rw [faces.regulars_eq, faces.holes_eq, faces.split.sum_eq values.cellBoundary]
  exact values.sum_cells_eq_perimeter bank.grid

/-- The actual regular-face boundary sum equals exterior perimeter plus inward hole boundaries.

The original grid partition and reversed hole orientation retain all signed boundary occurrences. -/
theorem boundary_eq_exterior_sub_holes (faces : PuncturedFaces bank) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) faces.regulars =
      values.perimeter bank.grid + Geometry.Grid.CellBoundary.sumValues (fun hole => values.walk hole.inwardBoundary)
        faces.holes := by
  have regular := Geometry.Grid.CellBoundary.sumValues_congr (fun face : RegularFace bank => values.walk face.boundary)
    (fun face => values.cellBoundary face.cell) faces.regulars
    (fun face _ => Geometry.Grid.CellBoundary.Cell.boundaryWalk_value face.cell face.member values)
  have holes := Geometry.Grid.CellBoundary.sumValues_congr (fun hole : BranchHole bank => values.walk
    hole.inwardBoundary)
    (fun hole => -values.cellBoundary hole.cell) faces.holes (fun hole _ => hole.inwardBoundary_value values)
  rw [regular, holes, Geometry.Grid.CellBoundary.sumValues_neg, ← faces.boundary_balance values]
  ring1

set_option genInjectivity false in
/-- Cached regular, inward-hole and exterior boundary readbacks with exact equations.

Each value refers to the same retained grid partition and edge readings; the finite equations also validate externally
supplied caches. -/
structure BoundarySample (faces : PuncturedFaces bank) (values : Geometry.Grid.CellBoundary.EdgeValues) where
  /-- The cached sum of actual regular-face boundary readings. -/ regular : Gaussian.Basic.Canonical
  /-- The regular cache reads the original regular-face walks. -/ regular_eq : regular =
    Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) faces.regulars
  /-- The cached sum of inward-oriented hole readings. -/ inwardHoles : Gaussian.Basic.Canonical
  /-- The hole cache reads the original inward hole walks. -/ inwardHoles_eq : inwardHoles =
    Geometry.Grid.CellBoundary.sumValues (fun hole => values.walk hole.inwardBoundary) faces.holes
  /-- The cached exterior grid-perimeter value. -/ exterior : Gaussian.Basic.Canonical
  /-- The exterior cache equals the actual retained grid perimeter. -/ exterior_eq : exterior = values.perimeter
    bank.grid

constructive_injectivity BoundarySample

/-- Cache the three exact boundary sums on the retained punctured grid. -/
@[expose] def BoundarySample.build (faces : PuncturedFaces bank) (values : Geometry.Grid.CellBoundary.EdgeValues) :
  BoundarySample faces values :=
  ⟨sumValues (fun face => values.walk face.boundary) faces.regulars, rfl,
    Geometry.Grid.CellBoundary.sumValues (fun hole => values.walk hole.inwardBoundary) faces.holes, rfl,
    values.perimeter bank.grid, rfl⟩

/-- The cached regular value equals the cached exterior plus inward-hole values. -/
theorem BoundarySample.balance {faces : PuncturedFaces bank} {values : Geometry.Grid.CellBoundary.EdgeValues} (sample :
  BoundarySample faces values) :
    sample.regular = sample.exterior + sample.inwardHoles := by
  rw [sample.regular_eq, sample.exterior_eq, sample.inwardHoles_eq]
  exact faces.boundary_eq_exterior_sub_holes values

end PuncturedFaces

end Purelib.Riemann.Meshes.PuncturedGridFaces
