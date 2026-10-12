module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.SquareRoot.Grid.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Inclusion.CellBoundary
public import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularArea

@[expose] public section

/-! Annular excision with the actual original cell walk, subdivided on the
retained Newton grid. Both sheets and the intervening triangle area remain. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalBoundaryReadback

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues (walk)
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

open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy in
open Purelib.Data in
open Purelib.Polynomial.Geometry.Grid in
open Purelib.Polynomial.Geometry.Grid.CellBoundary in
open Purelib.Polynomial.Geometry.Grid.Inclusion in
/-- The resplit original cell walk and retained outer window have equal two-sheet primitive area.

The exact grid inclusion and cached root-edge valuations compare both original sheets on their actual walks. -/
theorem original_boundary_area (outer : OriginalAnnularFaces grid index)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    lifted.edges.twoSheetArea lifted.vertices primitive
        (grid.shrunk.included.resplit (Cell.boundaryWalk (original.cell index) (original.cell_mem index))
          ((original.cell index).anchor_mem (original.cell_mem index))) =
      lifted.edges.twoSheetArea lifted.vertices primitive outer.window.boundary := by
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Gaussian.Basic.Canonical} (walk : Walks.Walk grid.shrunk.prepared.grid start finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive
      (fun point member => (BranchCellBank.referenceAt
        grid.shrunk.prepared.toBranchCellBank point member).toLoop) walk
  exact (walks _).symm.trans ((CellBoundary.resplit_cell_value grid.shrunk.included
    (original.cell index) (original.cell_mem index) outer.window values).trans (walks _))

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus in
open Purelib.Polynomial.Geometry.Grid.CellBoundary in
open Purelib.Riemann in
/-- Annular excision retains the actual original cell walk on the Newton grid.

The identity combines the outer-to-inner triangle region with the retained complement, preserving both sheets and the
complete intervening area. -/
theorem excision_with_original_walk (outer : OriginalAnnularFaces grid index) {inner : Faces.AnnularFaces grid index}
    (region : LiftedBoundary.Lifted inner lifted)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive ((RootContinuation.NewtonOriginalAnnularArea.betweenLifted outer lifted).triangles.flatMap
      OrientedTriangle.boundary) +
      (edgeListArea primitive lifted.mesh.triangulation.boundary - edgeListArea primitive region.inner) =
        edgeListArea primitive (region.complement.flatMap OrientedTriangle.boundary) +
          lifted.edges.twoSheetArea lifted.vertices primitive
            (grid.shrunk.included.resplit (Cell.boundaryWalk (original.cell index) (original.cell_mem index))
              ((original.cell index).anchor_mem (original.cell_mem index))) := by
  rw [original_boundary_area outer primitive]
  exact RootContinuation.NewtonOriginalAnnularArea.excision_with_original outer region primitive

end Purelib.Riemann.RootContinuation.NewtonOriginalBoundaryReadback
