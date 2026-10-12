module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceSelection
import Purelib.RootIsolation.SquareRoot.Grid.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.RootContinuation.NewtonOriginalBoundaryReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundary

@[expose] public section

/-! The full retained region between the original enclosing cell and the
new branch hole, using the existing lifted triangles on both sheets. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalLiftedBoundary

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr)
open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues (walk)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {lifted : LiftedPuncturedGrid grid.punctured}

section
open Purelib.Riemann.Meshes
/-- Select and reindex the original lifted regular faces in the retained annular window.

The executable box-refinement mask selects the original mesh lifts; its exact kept-face equality transports them to the
original annular face list. -/
def allLifted (outer : OriginalAnnularFaces grid index) (lifted : LiftedPuncturedGrid grid.punctured) :
    LiftedFaces lifted.vertices lifted.edges outer.faces :=
  let selected := GridLiftedFaceSelection.select
    (fun face => decide (face.cell.box.Refines (original.cell index).box)) lifted.mesh.lifts
  GridLiftedFaceSelection.reindex selected.selected
    (selected.kept_eq.trans outer.faces_eq.symm)

/-- Reindexing the selected original annular lifts preserves their exact ordered triangle list. -/
theorem allLifted_triangles (outer : OriginalAnnularFaces grid index) (lifted : LiftedPuncturedGrid grid.punctured) :
    (allLifted outer lifted).triangles =
      (GridLiftedFaceSelection.select
        (fun face => decide (face.cell.box.Refines (original.cell index).box)) lifted.mesh.lifts).selected.triangles :=
  GridLiftedFaceSelection.reindex_triangles _ _

end

open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The original selected triangle boundary area equals the retained outer two-sheet area plus inner boundary area.

The original window, hole index and inward orientation determine the balance, preserving the actual edge-value walks and
original boundary readback. -/
theorem triangleEdges_area (outer : OriginalAnnularFaces grid index) {inner : Meshes.Newton.Annulus.Faces.AnnularFaces
  grid index}
    (region : Meshes.Newton.Annulus.LiftedBoundary.Lifted inner lifted)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive ((allLifted outer lifted).triangles.flatMap OrientedTriangle.boundary) =
      lifted.edges.twoSheetArea lifted.vertices primitive
        (grid.shrunk.included.resplit (Geometry.Grid.CellBoundary.Cell.boundaryWalk
          (original.cell index) (original.cell_mem index))
          ((original.cell index).anchor_mem (original.cell_mem index))) + edgeListArea primitive region.inner := by
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid.shrunk.prepared.grid start finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive
      (fun point member => (Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
        grid.shrunk.prepared.toBranchCellBank point member).toLoop) walk
  have holeValue : values.walk region.hole.inwardBoundary =
      -values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index) := by
    rw [region.hole.inwardBoundary_value, region.hole.cell_eq, region.hole_index]
  have balance := outer.boundary_balance values
  have balance : Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) outer.faces =
      values.walk outer.window.boundary + values.walk region.hole.inwardBoundary := by
    rw [holeValue, ← balance]
    ring1
  rw [(allLifted outer lifted).triangleEdges_area primitive, LiftedFaces.actualBoundaries_area]
  have readback := Geometry.Grid.CellBoundary.sumValues_congr
    (fun face : RegularFace grid.shrunk.prepared.toBranchCellBank => lifted.edges.twoSheetArea lifted.vertices primitive
      face.boundary)
    (fun face => values.walk face.boundary) outer.faces (fun face _ => (walks face.boundary).symm)
  exact readback.trans (balance.trans (congrArg₂ (· + ·)
    ((walks outer.window.boundary).trans
      (NewtonOriginalBoundaryReadback.original_boundary_area outer primitive).symm)
    ((walks region.hole.inwardBoundary).trans (region.inner_area primitive).symm)))

end Purelib.Riemann.RootContinuation.NewtonOriginalLiftedBoundary
