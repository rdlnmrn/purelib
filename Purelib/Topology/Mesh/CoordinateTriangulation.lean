module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Mesh.EdgeCancellation
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

/-!
# Automatically indexed finite coordinate triangulations

Equal Gaussian-rational corner values use the same first-occurrence index.
The finite edge-cancellation algorithm therefore sees shared geometric edges
as literal reversed indexed edges.  All lookup and incidence witnesses are
constructed, rather than supplied as successful-check premises.
-/

namespace Purelib.Topology.Mesh

open Purelib.Data.List

open Purelib.Data
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon

-- The frozen owner puts `CoordinateTriangulation` inside a namespace with the same leaf.

namespace CoordinateTriangulation

set_option genInjectivity false in
/-- The finite geometric input for one oriented face.

The three Gaussian rational coordinates retain their cyclic order. Coordinate indexing uses these exact values without
changing their occurrence order. -/
public structure CoordinateTriangle where
  /-- First Gaussian rational corner in the oriented face order. -/ first : Gaussian.Basic.Canonical
  /-- Second Gaussian rational corner in the oriented face order. -/ second : Gaussian.Basic.Canonical
  /-- Third Gaussian rational corner in the oriented face order. -/ third : Gaussian.Basic.Canonical

constructive_injectivity CoordinateTriangle

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Retain a simple occurrence bank. Repeated coordinates are permitted, but all faces use their first occurrence, so
repetitions are not separate vertices. -/
@[expose] public def triangleVertices : List CoordinateTriangulation.CoordinateTriangle -> List Gaussian.Basic.Canonical
  | [] => []
  | triangle :: rest => triangle.first :: triangle.second :: triangle.third ::
    Purelib.Topology.Mesh.CoordinateTriangulation.triangleVertices rest

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Every corner of a displayed face occurs in the materialized vertex bank.

Structural membership follows the displayed face occurrence. Each corner is placed in its own retained position before
the unchanged tail bank. -/
public theorem triangleVertices_mem {triangles : List CoordinateTriangulation.CoordinateTriangle} {triangle :
  CoordinateTriangulation.CoordinateTriangle}
    (member : triangle ∈ triangles) :
    triangle.first ∈ CoordinateTriangulation.triangleVertices triangles ∧ triangle.second ∈
      CoordinateTriangulation.triangleVertices triangles ∧
      triangle.third ∈ CoordinateTriangulation.triangleVertices triangles := by
  induction triangles with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest inductionHypothesis =>
      rcases Membership.mem_cons.mp member with equal | inRest
      · subst triangle
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      · have tail := inductionHypothesis inRest
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail.1)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail.2.1)),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail.2.2))⟩

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Bounded coordinate lookup with its index-validity proof kept internal. -/
@[expose] public def vertexAt (vertices : List Gaussian.Basic.Canonical) (index : Fin vertices.length) :
  Gaussian.Basic.Canonical :=
  vertices[index.val]'index.isLt

end CoordinateTriangulation

namespace CoordinateTriangulation

set_option genInjectivity false in
/-- Total first-occurrence lookup with an exact coordinate readback equation.

The bounded index belongs to the original vertex bank and reads the requested Gaussian rational coordinate. Repeated
coordinates may share the same retained index. -/
public structure VertexLookup (vertices : List Gaussian.Basic.Canonical) (point : Gaussian.Basic.Canonical) where
  /-- Bounded position of the coordinate in the retained vertex bank. -/ index : Fin vertices.length
  /-- Reading the retained position gives the requested coordinate. -/ coordinate_eq : CoordinateTriangulation.vertexAt
    vertices index = point

constructive_injectivity VertexLookup

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Find the first occurrence of a coordinate in its finite vertex bank.

The supplied membership proof makes the search total; the result retains its bounded index and exact coordinate
equation. -/
@[expose] public def lookupVertex (point : Gaussian.Basic.Canonical) :
    (vertices : List Gaussian.Basic.Canonical) -> point ∈ vertices -> CoordinateTriangulation.VertexLookup vertices
      point
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member =>
      if equal : point = first then
        ⟨0, equal.symm⟩
      else
        have inRest : point ∈ rest := by
          rcases Membership.mem_cons.mp member with equalHead | inTail
          · exact (equal equalHead).elim
          · exact inTail
        let tail := Purelib.Topology.Mesh.CoordinateTriangulation.lookupVertex point rest inRest
        ⟨tail.index.succ, tail.coordinate_eq⟩

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Proof irrelevance ensures that a shared coordinate has one shared index, irrespective of which face established its
membership in the bank.

The original lookup procedure receives the same coordinate and finite bank in both calls. Different membership proofs
therefore retain the same selected index. -/
public theorem lookupVertex_same (vertices : List Gaussian.Basic.Canonical) {left right : Gaussian.Basic.Canonical}
    (leftMember : left ∈ vertices) (rightMember : right ∈ vertices) (equal : left = right) :
    (CoordinateTriangulation.lookupVertex left vertices leftMember).index = (CoordinateTriangulation.lookupVertex right
      vertices rightMember).index := by
  subst right
  rfl

end CoordinateTriangulation

namespace CoordinateTriangulation

/-- Index the three corners of a coordinate triangle in the supplied vertex bank.

Each lookup consumes the corresponding membership proof and preserves the given cyclic corner order. -/
@[expose] public def indexTriangle (vertices : List Gaussian.Basic.Canonical) (triangle :
  CoordinateTriangulation.CoordinateTriangle)
    (members : triangle.first ∈ vertices ∧ triangle.second ∈ vertices ∧ triangle.third ∈ vertices) :
    Stokes.OrientedTriangle vertices.length :=
  ⟨(CoordinateTriangulation.lookupVertex triangle.first vertices members.1).index,
    (CoordinateTriangulation.lookupVertex triangle.second vertices members.2.1).index,
    (CoordinateTriangulation.lookupVertex triangle.third vertices members.2.2).index⟩

end CoordinateTriangulation

set_option genInjectivity false in
/-- Cache all indexed faces, their coordinate realization, and their certified incidence. Generated data may use a
smaller deduplicated vertex bank: only these exact semantic equations, not a particular lookup algorithm, are required.

Every retained face reads back its three original coordinates, and the incidence certificate uses the exact cached face
table. The vertex bank may contain repeats or be deduplicated without changing these equations. -/
public structure CoordinateTriangulation (triangles : List CoordinateTriangulation.CoordinateTriangle) where
  /-- Retained Gaussian rational vertex bank, allowing repeated coordinates. -/ vertices : List Gaussian.Basic.Canonical
  /-- Cached indexed face for each original coordinate triangle. -/ faces : Data.Vector
    (Stokes.OrientedTriangle vertices.length) triangles.length
  /-- Each indexed first corner reads back the original first coordinate. -/ first_eq : forall index,
    CoordinateTriangulation.vertexAt vertices (faces index).first = (triangles[index.val]).first
  /-- Each indexed second corner reads back the original second coordinate. -/ second_eq : forall index,
    CoordinateTriangulation.vertexAt vertices (faces index).second = (triangles[index.val]).second
  /-- Each indexed third corner reads back the original third coordinate. -/ third_eq : forall index,
    CoordinateTriangulation.vertexAt vertices (faces index).third = (triangles[index.val]).third
  /-- Certified incidence decomposition of the retained indexed faces. -/ triangulation : Stokes.Triangulation
    vertices.length triangles.length
  /-- The incidence certificate uses the exact cached face table. -/ faces_eq : forall index, triangulation.faces index
    = faces index

constructive_injectivity CoordinateTriangulation

namespace CoordinateTriangulation

variable {triangles : List Purelib.Topology.Mesh.CoordinateTriangulation.CoordinateTriangle}

/-- Materialize shared face indices separately from incidence cancellation. This also exposes the shortest profiling
boundary for large input banks.

Each cached face consumes the three original corner memberships in the materialized vertex bank. Equal coordinates use
the same first-occurrence lookup while the oriented corner order is retained. -/
@[expose] public def indexedFaces (triangles : List CoordinateTriangulation.CoordinateTriangle) :
    Data.Vector (Stokes.OrientedTriangle (CoordinateTriangulation.triangleVertices triangles).length)
      triangles.length :=
  Data.Vector.Basic.vectorOfFn fun index : Fin triangles.length =>
    CoordinateTriangulation.indexTriangle (CoordinateTriangulation.triangleVertices triangles) triangles[index.val]
      (CoordinateTriangulation.triangleVertices_mem (List.getElem_mem _))

/-- Build shared coordinate indices and cancel internal edges by total finite algorithms. No coordinate or incidence
witness is demanded from the caller.

The builder retains its materialized vertex bank and indexed face cache. It constructs their exact coordinate readbacks
and the finite edge-cancellation incidence certificate. -/
@[expose] public def build (triangles : List CoordinateTriangulation.CoordinateTriangle) :
  CoordinateTriangulation triangles :=
  let vertices := CoordinateTriangulation.triangleVertices triangles
  let faces := CoordinateTriangulation.indexedFaces triangles
  { vertices := vertices
    faces := faces
    first_eq := fun index => by
      dsimp only [faces, CoordinateTriangulation.indexedFaces]
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact (CoordinateTriangulation.lookupVertex _ _ _).coordinate_eq
    second_eq := fun index => by
      dsimp only [faces, CoordinateTriangulation.indexedFaces]
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact (CoordinateTriangulation.lookupVertex _ _ _).coordinate_eq
    third_eq := fun index => by
      dsimp only [faces, CoordinateTriangulation.indexedFaces]
      rw [Data.Vector.Basic.vectorOfFn_apply]
      exact (CoordinateTriangulation.lookupVertex _ _ _).coordinate_eq
    triangulation := EdgeCancellation.triangulateFaces faces
    faces_eq := fun _ => rfl }

/-- Read the Gaussian rational coordinate of a retained mesh vertex. -/
@[expose] public def coordinate (mesh : CoordinateTriangulation triangles) (index : Fin
  mesh.vertices.length) : Gaussian.Basic.Canonical :=
  CoordinateTriangulation.vertexAt mesh.vertices index

/-- The indexed face reads back the three original coordinate corners in order. -/
public theorem face_coordinates (mesh : CoordinateTriangulation triangles) (index : Fin
  triangles.length) :
    mesh.coordinate (mesh.triangulation.faces index).first = (triangles[index.val]).first ∧
    mesh.coordinate (mesh.triangulation.faces index).second = (triangles[index.val]).second ∧
    mesh.coordinate (mesh.triangulation.faces index).third = (triangles[index.val]).third := by
  rw [mesh.faces_eq]
  exact ⟨mesh.first_eq index, mesh.second_eq index, mesh.third_eq index⟩

/-- The constructed indexed mesh satisfies exact finite Stokes for arbitrary primitive values on its shared vertex bank.
-/
public theorem wedgeSum_eq_boundaryArea (mesh : CoordinateTriangulation triangles)
    (primitive : Fin mesh.vertices.length -> Stokes.PrimitivePoint) :
    Stokes.triangleWedgeSum primitive mesh.triangulation.faces =
      Stokes.edgeListArea primitive mesh.triangulation.boundary :=
  mesh.triangulation.wedgeSum_eq_boundaryArea primitive

end CoordinateTriangulation

end Purelib.Topology.Mesh
