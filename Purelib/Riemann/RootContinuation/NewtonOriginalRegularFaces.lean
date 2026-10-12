module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map
public import Purelib.Riemann.Meshes.GridLiftedFaceSelection

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Polynomial.Geometry.Grid.Inclusion.CellBoundary
import Purelib.Polynomial.Geometry.Grid.CellSeparation
public import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.Riemann.Meshes.GridLiftedBoundary

@[expose] public section

/-! Exact subdivision of an original regular cell on the Newton mesh.
No shrunken branch hole belongs to this region; both lifted sheets and
all selected triangles are retained. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues sumValues sumValues_congr sumValues_zero)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (sumValues_filter)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Polynomial in
/-- No retained Newton branch hole refines an original regular cell. -/
private theorem regular_excludes_hole (grid : NewtonGrid preparation target radius)
    (face : RegularFace original) (hole : BranchHole grid.punctured.bank.toBranchCellBank) :
    ¬hole.cell.box.Refines face.cell.box := by
  intro inside
  have strict : hole.cell.box.StrictInterior (original.cell hole.index).box := by
    rw [hole.cell_eq]
    exact grid.shrunk.cell_strict hole.index
  have anchor := hole.cell.box.contains_anchor
  have originalInside : (original.cell hole.index).box.StrictContains hole.cell.box.anchor :=
    ⟨strict.left.trans_le anchor.1, anchor.2.1.trans_lt strict.right,
      strict.bottom.trans_le anchor.2.2.1, anchor.2.2.2.trans_lt strict.top⟩
  exact face.unassigned hole.index (Geometry.Grid.CellSeparation.cells_eq_of_common_point original.grid
    (original.cell_mem hole.index) face.member originalInside (inside.contains anchor)).symm

open Purelib.Polynomial in
set_option genInjectivity false in
/-- The Newton subdivision of one original regular cell.

The record retains the filtered regular face list and exact coordinate window; no shrunken branch hole belongs to this
region. -/
structure OriginalRegularFaces (grid : NewtonGrid preparation target radius) (face : RegularFace original) where
  /-- The existing Newton regular faces contained in the original cell. -/ faces : List (RegularFace
    grid.shrunk.prepared.toBranchCellBank)
  /-- The retained faces are exactly the original-cell refinement filter. -/ faces_eq : faces =
    grid.faces.regulars.filter (fun entry => decide (entry.cell.box.Refines face.cell.box))
  /-- The original regular cell's coordinate window in the refined grid. -/ window :
    Polynomial.Geometry.Grid.WindowBoundary.Window grid.shrunk.prepared.grid face.cell.box

constructive_injectivity OriginalRegularFaces

namespace OriginalRegularFaces

variable {grid : NewtonGrid preparation target radius} {face : RegularFace original}

open Purelib.Data in
open Purelib.Polynomial in
/-- Select the Newton faces refining an original regular cell.

Reuse the existing face classification and retained coordinate inclusion to construct the exact window. -/
def build (grid : NewtonGrid preparation target radius) (face : RegularFace original) : OriginalRegularFaces grid face
  := by
  have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem face.cell face.member
  have x := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.grid.vertical_ordered intervals.1
  have y := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.grid.horizontal_ordered intervals.2
  let included := grid.shrunk.included
  exact ⟨grid.faces.regulars.filter (fun entry => decide (entry.cell.box.Refines face.cell.box)), rfl,
    Polynomial.Geometry.Grid.WindowBoundary.Window.build _ face.cell.box
      (included.vertical _ (List.Map.mem_map_of_mem x.1))
      (included.vertical _ (List.Map.mem_map_of_mem x.2))
      (included.horizontal _ (List.Map.mem_map_of_mem y.1))
      (included.horizontal _ (List.Map.mem_map_of_mem y.2))⟩

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The retained regular-face sum equals the sum over the original cell's grid window. -/
theorem sum_balance (region : OriginalRegularFaces grid face) (value : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve) → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun entry => value entry.cell) region.faces =
      Geometry.Grid.CellBoundary.sumValues value region.window.cells := by
  rw [region.faces_eq, region.window.cells_eq, Geometry.Grid.WindowBoundary.sumValues_filter,
    Geometry.Grid.WindowBoundary.sumValues_filter]
  have balance := grid.faces.split.sum_eq (fun cell => if cell.box.Refines face.cell.box then value cell else 0)
  rw [← grid.faces.regulars_eq, ← grid.faces.holes_eq] at balance
  have holes : Geometry.Grid.CellBoundary.sumValues (fun hole => if hole.cell.box.Refines face.cell.box then value
    hole.cell else 0) grid.faces.holes = 0 := by
    rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun _ => 0) grid.faces.holes (by
      intro hole _
      rw [if_neg (regular_excludes_hole grid face hole)]), Geometry.Grid.CellBoundary.sumValues_zero]
  rw [holes, add_zero] at balance
  exact balance

open Purelib.Polynomial in
/-- The retained fine-face boundaries equal the original boundary after its actual subdivision.

The equality evaluates the resplit four-sided walk with every intermediate grid edge retained. -/
theorem boundary_balance (region : OriginalRegularFaces grid face) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun entry => values.walk entry.boundary) region.faces =
      values.walk (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) := by
  have readback := Geometry.Grid.CellBoundary.sumValues_congr
    (fun entry : RegularFace grid.shrunk.prepared.toBranchCellBank => values.walk entry.boundary)
    (fun entry => values.cellBoundary entry.cell) region.faces
    (fun entry _ => Geometry.Grid.CellBoundary.Cell.boundaryWalk_value entry.cell entry.member values)
  exact readback.trans ((region.sum_balance values.cellBoundary).trans
    ((region.window.sum_cells_eq_boundary values).trans
      (Geometry.Grid.Inclusion.CellBoundary.resplit_cell_value
        grid.shrunk.included face.cell face.member region.window values).symm))

section
open Purelib.Riemann
/-- Select both lifted sheets of the retained original-cell face region.

Reindex the existing lifted face selection by the exact retained-list equation. -/
def allLifted (region : OriginalRegularFaces grid face) (lifted : LiftedPuncturedGrid grid.punctured) :
    LiftedFaces lifted.vertices lifted.edges region.faces :=
  let selected := Meshes.GridLiftedFaceSelection.select
    (fun entry => decide (entry.cell.box.Refines face.cell.box)) lifted.mesh.lifts
  Meshes.GridLiftedFaceSelection.reindex selected.selected (selected.kept_eq.trans region.faces_eq.symm)

/-- The selected lifted region preserves the original filtered triangle list. -/
theorem allLifted_triangles (region : OriginalRegularFaces grid face) (lifted : LiftedPuncturedGrid grid.punctured) :
    (region.allLifted lifted).triangles =
      (Meshes.GridLiftedFaceSelection.select
        (fun entry => decide (entry.cell.box.Refines face.cell.box)) lifted.mesh.lifts).selected.triangles :=
  Meshes.GridLiftedFaceSelection.reindex_triangles _ _

end

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Conserve both-sheet triangle area across subdivision of an original regular cell.

For arbitrary projected primitive values, the exact finite incidence identity retains every triangle boundary and the
full resplit original walk. -/
theorem triangleEdges_area (region : OriginalRegularFaces grid face) (lifted : LiftedPuncturedGrid grid.punctured)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive ((region.allLifted lifted).triangles.flatMap OrientedTriangle.boundary) =
      lifted.edges.twoSheetArea lifted.vertices primitive
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) := by
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid.shrunk.prepared.grid start
    finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive
      (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
        grid.shrunk.prepared.toBranchCellBank point member).toLoop) walk
  rw [(region.allLifted lifted).triangleEdges_area primitive, LiftedFaces.actualBoundaries_area]
  have readback := Geometry.Grid.CellBoundary.sumValues_congr
    (fun entry : RegularFace grid.shrunk.prepared.toBranchCellBank => lifted.edges.twoSheetArea lifted.vertices
      primitive entry.boundary)
    (fun entry => values.walk entry.boundary) region.faces (fun entry _ => (walks entry.boundary).symm)
  exact readback.trans ((region.boundary_balance values).trans (walks _))

end OriginalRegularFaces
end Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
