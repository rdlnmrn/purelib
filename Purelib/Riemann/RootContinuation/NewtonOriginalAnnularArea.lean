module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceSelection
import Purelib.RootIsolation.SquareRoot.Grid.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundary

@[expose] public section

/-! The original enclosing branch cell and the Newton band differ by the
area of actual retained regular triangles on both sheets. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalAnnularArea

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues_congr)
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

open Purelib.Riemann in
/-- Select the retained lifted faces between the original branch cell and Newton band.

Two selections reuse the existing triangle bank and sheet transports, with exact face-list readbacks at each step. -/
def betweenLifted (outer : OriginalAnnularFaces grid index) (lifted : LiftedPuncturedGrid grid.punctured) :
    LiftedFaces lifted.vertices lifted.edges outer.between :=
  let whole := Meshes.GridLiftedFaceSelection.select
    (fun face => decide (face.cell.box.Refines (original.cell index).box)) lifted.mesh.lifts
  let inside := Meshes.GridLiftedFaceSelection.reindex whole.selected (whole.kept_eq.trans outer.faces_eq.symm)
  let gap := Meshes.GridLiftedFaceSelection.select
    (fun face => decide (¬face.cell.box.Refines (grid.bands.box index))) inside
  Meshes.GridLiftedFaceSelection.reindex gap.selected gap.kept_eq

open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The intervening triangle area equals the original two-sheet cell boundary area minus the Newton outer boundary area.

The supplied primitive is read on the same retained vertices and lifted edge owners. -/
theorem between_area (outer : OriginalAnnularFaces grid index) {inner :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index}
    (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted inner lifted) (primitive : Fin
      lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive ((betweenLifted outer lifted).triangles.flatMap OrientedTriangle.boundary) =
      lifted.edges.twoSheetArea lifted.vertices primitive outer.window.boundary - edgeListArea primitive region.outer :=
        by
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid.shrunk.prepared.grid start
    finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive
      (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
        grid.shrunk.prepared.toBranchCellBank point member).toLoop) walk
  rw [(betweenLifted outer lifted).triangleEdges_area primitive, LiftedFaces.actualBoundaries_area]
  have readback := Geometry.Grid.CellBoundary.sumValues_congr
    (fun face : RegularFace grid.shrunk.prepared.toBranchCellBank => lifted.edges.twoSheetArea lifted.vertices primitive
      face.boundary)
    (fun face => values.walk face.boundary) outer.between (fun face _ => (walks face.boundary).symm)
  exact readback.trans ((outer.between_boundary inner values).trans
    (congrArg₂ (· - ·) (walks outer.window.boundary) ((walks inner.boundary).trans (region.outer_area primitive).symm)))

open Purelib.Curves in
/-- Replace the Newton outer boundary by the original enclosing-cell boundary in the exact excision identity.

The intervening retained triangle area remains explicit together with the actual complementary and inner boundaries. -/
theorem excision_with_original (outer : OriginalAnnularFaces grid index) {inner :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index}
    (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted inner lifted) (primitive : Fin
      lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive ((betweenLifted outer lifted).triangles.flatMap OrientedTriangle.boundary) +
      (edgeListArea primitive lifted.mesh.triangulation.boundary - edgeListArea primitive region.inner) =
        edgeListArea primitive (region.complement.flatMap OrientedTriangle.boundary) +
          lifted.edges.twoSheetArea lifted.vertices primitive outer.window.boundary := by
  rw [between_area outer region primitive, region.excision_area primitive]
  ring1

end Purelib.Riemann.RootContinuation.NewtonOriginalAnnularArea
