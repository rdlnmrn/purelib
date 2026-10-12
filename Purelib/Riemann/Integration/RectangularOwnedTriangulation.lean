module
meta import Purelib.Elab.ConstructiveInjectivity
-- Exposed owner builders retain mapped-coordinate bound and readback certificates.
public import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

public import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Fine coordinate meshes retaining their coarse model owners

Every triangle retains a containing coarse rectangle.  Shared coordinates
use the existing finite triangulation algorithm, while a separate cached
owner bank provides one local-model choice per indexed vertex.  Neither
point-location search nor further model refinement is needed when the fine
triangles are indexed.  Generated meshes may use a deduplicated vertex bank
and any owners satisfying the same exact containment and readback equations.
-/

namespace Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Data.List

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Topology.Mesh.CoordinateTriangulation
open _root_.Purelib.Topology.Mesh renaming CoordinateTriangulation -> CoordinateTriangulation
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A geometric vertex retaining its cell index and containment certificate.

The column and row identify one cell of the supplied geometry. The stored
coordinate belongs to that exact cell and remains the readback value. -/
structure OwnedVertex {columns rows : Nat} (geometry : Geometry columns rows) where
  /-- The retained original cell-column index. -/ column : Fin (columns + 1)
  /-- The retained original cell-row index. -/ row : Fin (rows + 1)
  /-- The retained original geometric vertex coordinate. -/ point : Basic.Canonical
  /-- The retained point belongs to its exact original owner cell. -/ contains : (geometry.box column row).Contains
    point

constructive_injectivity OwnedVertex

open Purelib in
set_option genInjectivity false in
/-- A coordinate triangle with a cell owner containing all three vertices.

The retained column and row identify one rectangle of the supplied geometry.
Separate containment certificates concern the three ordered triangle corners. -/
structure ModelTriangle {columns rows : Nat} (geometry : Geometry columns rows) where
  /-- The retained original cell-column index. -/ column : Fin (columns + 1)
  /-- The retained original cell-row index. -/ row : Fin (rows + 1)
  /-- The original coordinate triangle. -/ triangle : Topology.Mesh.CoordinateTriangulation.CoordinateTriangle
  /-- The original triangle's first vertex belongs to its retained owner cell. -/ firstInside : (geometry.box column
    row).Contains triangle.first
  /-- The original triangle's second vertex belongs to its retained owner cell. -/ secondInside : (geometry.box column
    row).Contains triangle.second
  /-- The original triangle's third vertex belongs to its retained owner cell. -/ thirdInside : (geometry.box column
    row).Contains triangle.third

constructive_injectivity ModelTriangle

namespace ModelTriangle

variable {columns rows : Nat} {geometry : Geometry columns rows}

/-- List the three owned vertices of each triangle in face order.

Each face contributes its first, second and third corners with their retained
cell indices and containment certificates, followed by the unchanged tail. -/
@[expose] def ownedVertices : List (ModelTriangle geometry) → List (OwnedVertex geometry)
  | [] => []
  | face :: rest =>
      ⟨face.column, face.row, face.triangle.first, face.firstInside⟩ ::
      ⟨face.column, face.row, face.triangle.second, face.secondInside⟩ ::
      ⟨face.column, face.row, face.triangle.third, face.thirdInside⟩ :: ownedVertices rest

open Purelib in
/-- Forgetting retained vertex owners gives the flattened triangle-coordinate list.

Every face contributes the same three ordered coordinates to both lists.
Structural recursion compares their retained tails without changing ownership. -/
theorem ownedVertices_points (triangles : List (ModelTriangle geometry)) :
    Topology.Mesh.CoordinateTriangulation.triangleVertices (triangles.map ModelTriangle.triangle) =
      (ownedVertices triangles).map OwnedVertex.point := by
  induction triangles with
  | nil => rfl
  | cons face rest ih =>
      exact congrArg (List.cons face.triangle.first)
        (congrArg (List.cons face.triangle.second)
          (congrArg (List.cons face.triangle.third) ih))

end ModelTriangle

open Purelib in
open Purelib.Data in
set_option genInjectivity false in
/-- A coordinate triangulation with retained cell owners consistent at equal vertex coordinates.

The owner vector has exactly the mesh vertex count, preserves every original coordinate and chooses the same cell
indices for equal coordinates. -/
structure OwnedTriangulation {columns rows : Nat} {geometry : Geometry columns rows}
    (triangles : List (ModelTriangle geometry)) where
  /-- The original coordinate triangulation of the exact model-triangle list. -/ mesh :
    Topology.Mesh.CoordinateTriangulation (triangles.map ModelTriangle.triangle)
  /-- The retained owner vector indexed by the original mesh vertices. -/ owners : Data.Vector (OwnedVertex
    geometry) mesh.vertices.length
  /-- Each retained owner's coordinate equals its exact original mesh coordinate. -/ point_eq : ∀ vertex, (owners
    vertex).point = mesh.coordinate vertex
  /-- Equal original vertex coordinates retain equal cell-column and cell-row indices. -/ owner_consistent : ∀ first
    last, mesh.coordinate first = mesh.coordinate last →
    (owners first).column = (owners last).column ∧ (owners first).row = (owners last).row

constructive_injectivity OwnedTriangulation

namespace OwnedTriangulation

variable {columns rows : Nat} {geometry : Geometry columns rows}
    {triangles : List (ModelTriangle geometry)}

open Purelib in
open Purelib.Data in
/-- Construct the original coordinate triangulation and retain the first occurrence's owner at each vertex.

The exact flattened owned-vertex list supplies containment data; coordinate lookup shares the original owner indices
whenever coordinates coincide. -/
@[expose] def build (triangles : List (ModelTriangle geometry)) : OwnedTriangulation triangles :=
  let mesh := Topology.Mesh.CoordinateTriangulation.build (triangles.map ModelTriangle.triangle)
  let vertices := ModelTriangle.ownedVertices triangles
  have lengthEq : mesh.vertices.length = vertices.length := by
    change (Topology.Mesh.CoordinateTriangulation.triangleVertices (triangles.map ModelTriangle.triangle)).length =
      vertices.length
    rw [ModelTriangle.ownedVertices_points, Map.length_map]
  let firstOccurrence := fun vertex : Fin mesh.vertices.length =>
    Topology.Mesh.CoordinateTriangulation.lookupVertex (mesh.coordinate vertex) mesh.vertices (List.getElem_mem _)
  have readback (vertex : Fin mesh.vertices.length) :
      (vertices[vertex.val]'(vertex.isLt.trans_eq lengthEq)).point = mesh.coordinate vertex := by
    change (vertices[vertex.val]).point = (Topology.Mesh.CoordinateTriangulation.triangleVertices (triangles.map
      ModelTriangle.triangle))[vertex.val]
    have same : Topology.Mesh.CoordinateTriangulation.triangleVertices
        (triangles.map ModelTriangle.triangle) = vertices.map OwnedVertex.point :=
      ModelTriangle.ownedVertices_points triangles
    have sourceBound : vertex.val < vertices.length := vertex.isLt.trans_eq lengthEq
    have mappedBound : vertex.val < (vertices.map OwnedVertex.point).length := by
      rw [Map.length_map]
      exact sourceBound
    have coordinateTransport {left right : List Canonical} (equal : left = right)
        (leftBound : vertex.val < left.length) (rightBound : vertex.val < right.length) :
        left[vertex.val]'leftBound = right[vertex.val]'rightBound := by
      cases equal
      rfl
    exact (Map.getElem_map OwnedVertex.point vertices vertex.val sourceBound mappedBound).symm.trans
      (coordinateTransport same vertex.isLt mappedBound).symm
  { mesh := mesh
    owners := Vector.Basic.vectorOfFn fun vertex => vertices[(firstOccurrence vertex).index.val]'((firstOccurrence
      vertex).index.isLt.trans_eq lengthEq)
    point_eq := fun vertex => by
      rw [Vector.Basic.vectorOfFn_apply]
      exact (readback (firstOccurrence vertex).index).trans (firstOccurrence vertex).coordinate_eq
    owner_consistent := fun first last equal => by
      have same : (firstOccurrence first).index = (firstOccurrence last).index :=
        Topology.Mesh.CoordinateTriangulation.lookupVertex_same mesh.vertices _ _ equal
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply, same]
      exact ⟨rfl, rfl⟩ }

/-- The original model triangle at the retained mapped-face index. -/
@[expose] def faceSource (_surface : OwnedTriangulation triangles)
    (face : Fin (triangles.map ModelTriangle.triangle).length) : ModelTriangle geometry :=
  triangles[face.val]'(by simpa only [Map.length_map] using face.isLt)

/-- All three coordinates of an indexed mesh face belong to its source triangle's cell.

The mesh readback equations recover the original three ordered corners.
Their supplied containment certificates use the retained source cell indices. -/
theorem face_inside (surface : OwnedTriangulation triangles)
    (face : Fin (triangles.map ModelTriangle.triangle).length) :
    let source := surface.faceSource face
    let indexed := surface.mesh.triangulation.faces face
    (geometry.box source.column source.row).Contains (surface.mesh.coordinate indexed.first) ∧
    (geometry.box source.column source.row).Contains (surface.mesh.coordinate indexed.second) ∧
    (geometry.box source.column source.row).Contains (surface.mesh.coordinate indexed.third) := by
  have coordinates := surface.mesh.face_coordinates face
  dsimp only
  rw [coordinates.1, coordinates.2.1, coordinates.2.2,
    Map.getElem_map ModelTriangle.triangle triangles face.val
      (by rw [← Map.length_map ModelTriangle.triangle triangles]; exact face.isLt)
      face.isLt]
  exact ⟨(surface.faceSource face).firstInside, (surface.faceSource face).secondInside,
    (surface.faceSource face).thirdInside⟩

/-- Every retained mesh vertex belongs to its exact stored owner cell. -/
theorem owner_inside (surface : OwnedTriangulation triangles) (vertex : Fin surface.mesh.vertices.length) :
    (geometry.box (surface.owners vertex).column (surface.owners vertex).row).Contains (surface.mesh.coordinate vertex)
      :=
  surface.point_eq vertex ▸ (surface.owners vertex).contains

end OwnedTriangulation

end Purelib.Riemann.Integration.RectangularOwnedTriangulation
