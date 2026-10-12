module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Geometry

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Fixed corner indices for actual retained face-edge occurrences

The corner order is lower-left, lower-right, upper-right, upper-left.
Reversing an occurrence swaps its two corner indices without changing its
face or sheet. No geometric lookup or analytic preparation is repeated.
-/

section

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

/-- Read one original rectangle corner in lower-left, lower-right, upper-right, upper-left order. -/
def point (box : Rational.Box) : Fin 4 → Data.Gaussian.Basic.Canonical
  | ⟨0, _⟩ => ⟨box.xLower, box.yLower⟩
  | ⟨1, _⟩ => ⟨box.xUpper, box.yLower⟩
  | ⟨2, _⟩ => ⟨box.xUpper, box.yUpper⟩
  | ⟨3, _⟩ => ⟨box.xLower, box.yUpper⟩
  | ⟨_ + 4, impossible⟩ => (by omega : False).elim

/-- Every retained rectangle corner lies in the original closed rectangle. -/
theorem inside (box : Rational.Box) (corner : Fin 4) : box.Contains
  (point box corner) := by
  rcases corner with ⟨corner, bound⟩
  have cases : corner = 0 ∨ corner = 1 ∨ corner = 2 ∨ corner = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩
  · exact ⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩
  · exact ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩
  · exact ⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩

/-- The fixed oriented quadrilateral on the four original corner indices. -/
def quad : IndexedQuadrilaterals.IndexedQuadrilateral 4 := ⟨0, 1, 2, 3⟩

/-- The fixed corner-index edge reads back the original rectangle edge coordinates. -/
theorem edge_coordinates (box : Rational.Box) (kind : RectangleEdge.Kind) :
    (point box
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad.edge kind).start,
      point box
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad.edge kind).finish) =
      RectangleEdge.coordinates box kind := by
  cases kind <;> rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}

section

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

/-- The retained local corner indices read back the actual original lifted edge endpoints. -/
theorem corner_coordinates {edge :
  Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.point location.face.cell.box
      (FaceCorners.quad.edge location.kind).start,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.point location.face.cell.box
        (FaceCorners.quad.edge location.kind).finish) =
        (vertices.coordinate edge.start, vertices.coordinate edge.finish) := by
  rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.edge_coordinates, ←
    location.lifted.rectangleCoordinates.edge_coordinates, location.edge_eq]

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

end

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

/-- Read the retained edge occurrence's local corner indices, reversing them exactly for a backward occurrence. -/
def corners {edge : Stokes.OrientedEdge
  vertices.count} : MeshPathWalks.EdgeRoute mesh edge → Stokes.OrientedEdge 4
  | .forward location => FaceCorners.quad.edge location.kind
  | .backward location => (FaceCorners.quad.edge location.kind).reverse

/-- The retained local corner indices read back the actual original lifted edge endpoints. -/
theorem corner_coordinates {edge :
  Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    (Face.Corners.FaceCorners.point route.face.cell.box route.corners.start,
      Face.Corners.FaceCorners.point route.face.cell.box route.corners.finish)
      =
      (vertices.coordinate edge.start, vertices.coordinate edge.finish) := by
  cases route with
  | forward location => exact location.corner_coordinates
  | backward location => exact congrArg Prod.swap location.corner_coordinates

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

end
end
