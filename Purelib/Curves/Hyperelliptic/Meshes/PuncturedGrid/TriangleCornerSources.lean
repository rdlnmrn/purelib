module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Mesh.QuadrilateralDual

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-!
# Actual source triangles for retained face-corner increments

Triangle indices are decoded arithmetically from the retained face order.
The source-edge readback proves equality of lifted vertex indices, not only
of projected coordinates. Runtime selection does not traverse the lift bank.
-/

section

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

/-- Read the lower or upper original triangle of the fixed corner quadrilateral. -/
def triangle (upper : Bool) :
  OrientedTriangle 4 :=
  if upper then quad.secondTriangle else quad.firstTriangle

/-- Read the starting local triangle-corner index for the original rectangle edge kind. -/
def firstCorner : RectangleEdge.Kind →
  Fin 3
  | .bottom | .upDiagonal => 0
  | .right | .top => 1
  | .downDiagonal | .left => 2

/-- Read the finishing local triangle-corner index for the original rectangle edge kind. -/
def lastCorner : RectangleEdge.Kind →
  Fin 3
  | .bottom | .upDiagonal => 1
  | .right | .top => 2
  | .downDiagonal | .left => 0

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners in
/-- The retained local triangle corner indices project to the exact original quadrilateral edge. -/
theorem source_edge {count : Nat}
  (quad : IndexedQuadrilaterals.IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    (⟨corner (if QuadOccurrence.upperSide kind then quad.secondTriangle else quad.firstTriangle)
      (firstCorner kind),
      SewnPrimitiveFaces.corner (if QuadOccurrence.upperSide kind then quad.secondTriangle else quad.firstTriangle)
        (lastCorner kind)⟩ : OrientedEdge count) =
        quad.edge kind := by
  cases kind <;> rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

end

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- Retained corner equations determine the same lifted quadrilateral. This proof does not rerun any endpoint transport
or vertex lookup. -/
theorem quad_eq {face : RegularFace bank} {sheet
  : Fin 2}
    (first last : LiftedFace vertices edges face sheet) : first.quad = last.quad := by
  have lowerRight : first.lowerRight = last.lowerRight := first.bottom_eq.trans last.bottom_eq.symm
  have upperRight : first.upperRight = last.upperRight := by rw [first.right_eq, last.right_eq, lowerRight]
  have upperLeft : first.upperLeft = last.upperLeft := by rw [first.top_eq, last.top_eq, upperRight]
  change IndexedQuadrilateral.mk first.quad.first first.quad.second first.quad.third first.quad.fourth =
    IndexedQuadrilateral.mk last.quad.first last.quad.second last.quad.third last.quad.fourth
  rw [first.first_eq, last.first_eq, first.second_eq, last.second_eq, first.third_eq, last.third_eq,
    first.fourth_eq, last.fourth_eq, lowerRight, upperRight, upperLeft]

/-- Lifted rectangles at the same original face and sheet have equal retained quadrilaterals. -/
theorem quad_eq_of_face_eq {firstFace lastFace :
  RegularFace bank} {sheet : Fin 2}
    (equal : firstFace = lastFace) (first : LiftedFace vertices edges firstFace sheet)
    (last : LiftedFace vertices edges lastFace sheet) : first.quad = last.quad := by
  cases equal
  exact first.quad_eq last

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

section

variable {faces : PuncturedFaces bank}

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

/-- Compute the original triangle index directly from the retained face position, sheet and upper-triangle flag. -/
def triangleIndex (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin 2) (upper
  : Bool) :
    Fin mesh.triangles.length :=
  ⟨4 * position.val + 2 * sheet.val + if upper then 1 else 0, by
    rw [mesh.faceCount]
    have := position.isLt
    have := sheet.isLt
    split <;> omega⟩

/-- The arithmetic triangle index equals the index in the original retained face occurrence. -/
theorem triangleIndex_eq (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin 2)
  (upper : Bool) :
    mesh.triangleIndex position sheet upper = (mesh.locateFace position sheet).occurrence.triangle upper := by
  apply Fin.ext
  have indices := mesh.locateFace_indices position sheet
  cases upper
  · exact (Nat.add_zero _).trans indices.1.symm
  · exact indices.2.symm

/-- The arithmetic triangle index reads back the exact original lifted triangle. -/
theorem triangleIndex_face (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin
  2) (upper : Bool) :
    mesh.triangulation.faces (mesh.triangleIndex position sheet upper) =
      if upper then (mesh.locateFace position sheet).lifted.quad.secondTriangle else (mesh.locateFace position
        sheet).lifted.quad.firstTriangle := by
  rw [mesh.triangleIndex_eq]
  cases upper
  · exact (mesh.locateFace position sheet).occurrence.first_eq
  · exact (mesh.locateFace position sheet).occurrence.second_eq

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

end

variable {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}

section

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

/-- Read the original source triangle and local corner pair for the retained oriented edge occurrence. -/
def sourceEdge {edge : OrientedEdge vertices.count} (location : EdgeLocation mesh.lifts edge) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  ⟨mesh.triangleIndex location.position location.sheet (QuadOccurrence.upperSide location.kind),
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.firstCorner location.kind,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.lastCorner location.kind⟩

/-- The retained source triangle-corner pair projects to the exact original lifted edge indices. -/
theorem sourceEdge_project {edge : OrientedEdge vertices.count} (location : EdgeLocation mesh.lifts edge) :
    location.sourceEdge.project mesh.triangulation.faces = edge := by
  unfold SewnPrimitiveContacts.SourceEdge.project sourceEdge
  rw [mesh.triangleIndex_face, Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.source_edge]
  have same := LiftedFace.quad_eq_of_face_eq location.face_eq (mesh.locateFace location.position location.sheet).lifted
    location.lifted
  exact (congrArg (fun quad => quad.edge location.kind) same).trans location.edge_eq

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

end

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

/-- Read the original source triangle and local corner pair for the retained oriented edge occurrence. -/
def sourceEdge {edge : OrientedEdge
  vertices.count} : MeshPathWalks.EdgeRoute mesh edge → SewnPrimitiveContacts.SourceEdge mesh.triangles.length
  | .forward location => location.sourceEdge
  | .backward location =>
      let source := location.sourceEdge
      ⟨source.source, source.last, source.first⟩

/-- The retained source triangle-corner pair projects to the exact original lifted edge indices. -/
theorem sourceEdge_project {edge :
  OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    route.sourceEdge.project mesh.triangulation.faces = edge := by
  cases route with
  | forward location => exact location.sourceEdge_project
  | backward location => exact congrArg OrientedEdge.reverse location.sourceEdge_project

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

end
end
