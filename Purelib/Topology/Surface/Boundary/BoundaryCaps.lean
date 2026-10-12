module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Finite fans attached with the opposite boundary orientation

Every displayed boundary edge contributes one triangle at a supplied new
apex. Exact endpoint closure cancels the radial edges. The resulting area is
minus the original boundary area for arbitrary primitive values; no sign or
positivity claim about those values is built into this incidence calculation.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryCaps

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint Triangulation edgeArea
  edgeArea_reverse edgeListArea edgeListArea_append triangleBoundaryArea triangleEdgeOccurrences
  triangleWedgeSum_eq_edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {count : Nat}

/-- Attach one triangle from the supplied apex to each boundary edge in reverse orientation. -/
@[expose] def fan (apex : Fin count) (word : List (Stokes.OrientedEdge count)) : List (Stokes.OrientedTriangle count) :=
  word.map (fun edge => ⟨apex, edge.finish, edge.start⟩)

/-- Sum the oriented boundary areas of the displayed triangle list. -/
@[expose] def area (points : Fin count → Stokes.PrimitivePoint) (triangles : List (Stokes.OrientedTriangle count)) :
  Gaussian.Basic.Canonical :=
  Stokes.edgeListArea points (triangles.flatMap OrientedTriangle.boundary)

section
open Purelib.Topology.Surface.Boundary
/-- A leading triangle contributes its boundary area before the remaining face areas. -/
theorem area_cons (points : Fin count → Stokes.PrimitivePoint) (triangle : Stokes.OrientedTriangle count)
    (triangles : List (Stokes.OrientedTriangle count)) :
    BoundaryCaps.area points (triangle :: triangles) =
      Stokes.triangleBoundaryArea (points triangle.first) (points triangle.second) (points triangle.third) +
        BoundaryCaps.area points triangles := by
  rw [BoundaryCaps.area, Purelib.Data.List.Flatten.flatMap_cons, Stokes.edgeListArea_append]
  simp only [-eq_self, -iff_self, OrientedTriangle.boundary, Stokes.edgeListArea, Stokes.triangleBoundaryArea]
  change _ = _ + Stokes.edgeListArea points (triangles.flatMap OrientedTriangle.boundary)
  ring1

/-- Concatenating triangle lists adds their complete boundary areas. -/
theorem area_append (points : Fin count → Stokes.PrimitivePoint) (first last : List (Stokes.OrientedTriangle count)) :
    BoundaryCaps.area points (first ++ last) = BoundaryCaps.area points first + BoundaryCaps.area points last := by
  rw [BoundaryCaps.area, Purelib.Data.List.Flatten.flatMap_append, Stokes.edgeListArea_append]
  rfl

/-- Relabeling triangle vertices commutes with their primitive-area readback. -/
theorem area_map {target : Nat} (vertex : Fin count → Fin target) (points : Fin target → Stokes.PrimitivePoint)
    (triangles : List (Stokes.OrientedTriangle count)) :
    BoundaryCaps.area points (triangles.map (OrientedTriangle.map vertex)) = BoundaryCaps.area (fun index => points
      (vertex index)) triangles := by
  induction triangles with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, BoundaryCaps.area_cons, BoundaryCaps.area_cons, ih]
      rfl

/-- A fan over an exact path has negative path area and the two radial endpoint terms. -/
theorem fan_area (points : Fin count → Stokes.PrimitivePoint) (apex : Fin count)
    {word : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first last) :
    BoundaryCaps.area points (BoundaryCaps.fan apex word) = -Stokes.edgeListArea points word + Stokes.edgeArea (points
      apex) (points last) - Stokes.edgeArea (points apex) (points first) := by
  induction path with
  | nil => change (0 : Gaussian.Basic.Canonical) = -0 + _ - _; ring1
  | @cons edge tail last path ih =>
      change BoundaryCaps.area points (⟨apex, edge.finish, edge.start⟩ :: BoundaryCaps.fan apex tail) = _
      rw [BoundaryCaps.area_cons, ih]
      simp only [-eq_self, -iff_self, Stokes.triangleBoundaryArea, Stokes.edgeListArea]
      rw [Stokes.edgeArea_reverse (points edge.finish) (points edge.start), Stokes.edgeArea_reverse (points edge.start)
        (points apex)]
      ring1

/-- A fan over a closed path has the negative of its boundary area. -/
theorem fan_closed_area (points : Fin count → Stokes.PrimitivePoint) (apex : Fin count)
    {word : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor) :
    BoundaryCaps.area points (BoundaryCaps.fan apex word) = -Stokes.edgeListArea points word := by
  rw [BoundaryCaps.fan_area points apex closed]
  ring1

/-- A fan contains one triangle per supplied edge occurrence. -/
theorem fan_length (apex : Fin count) (word : List (Stokes.OrientedEdge count)) : (BoundaryCaps.fan apex word).length =
  word.length := Purelib.Data.List.Map.length_map ..

end

/-- Relabeling endpoints commutes with an edge word's area sum. -/
theorem edgeArea_map {target : Nat} (vertex : Fin count → Fin target) (points : Fin target → Stokes.PrimitivePoint)
    (word : List (Stokes.OrientedEdge count)) :
    Stokes.edgeListArea points (word.map (OrientedEdge.map vertex)) = Stokes.edgeListArea (fun index => points (vertex
      index)) word := by
  induction word with
  | nil => rfl
  | cons edge tail ih =>
    exact congrArg (Stokes.edgeArea (points (vertex edge.start)) (points (vertex edge.finish)) + ·) ih

section
open Purelib.Topology.Surface.Boundary
/-- Each component has its own supplied apex. In particular, separate exterior sheets are never identified at one new
vertex. -/
@[expose] def fans {target : Nat} (vertex : Fin count → Fin target) :
    (words : List (List (Stokes.OrientedEdge count))) → (Fin words.length → Fin target) → List (Stokes.OrientedTriangle
      target)
  | [], _ => []
  | word :: words, apex => BoundaryCaps.fan (apex 0) (word.map (OrientedEdge.map vertex)) ++
    Purelib.Topology.Surface.Boundary.BoundaryCaps.fans vertex words (fun index => apex index.succ)

/-- Fans over closed components cancel their complete projected boundary area.

Each component uses its own supplied apex, and all original edge occurrences remain in the sum. -/
theorem fans_area {target : Nat} (vertex : Fin count → Fin target) (points : Fin target → Stokes.PrimitivePoint)
    (words : List (List (Stokes.OrientedEdge count))) (apex : Fin words.length → Fin target)
    (closed : ∀ word ∈ words, ∃ anchor, PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor
      anchor) :
    BoundaryCaps.area points (BoundaryCaps.fans vertex words apex) = -Stokes.edgeListArea (fun index => points (vertex
      index)) words.flatten := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      obtain ⟨anchor, path⟩ := closed word List.mem_cons_self
      rw [BoundaryCaps.fans, BoundaryCaps.area_append, BoundaryCaps.fan_closed_area points _
        (SewingProjection.pathEndpoints_map vertex path), BoundaryCaps.edgeArea_map,
        ih _ (fun other member => closed other (List.mem_cons_of_mem _ member)), List.flatten_cons,
          Stokes.edgeListArea_append]
      ring1

end

set_option genInjectivity false in
/-- Indexed faces and their automatically checked incidence are retained. Subsequent area computations do not rerun edge
cancellation. -/
structure Indexed (triangles : List (Stokes.OrientedTriangle count)) where
  /-- Retained bounded face table in the original triangle order. -/ faces : Data.Vector
    (Stokes.OrientedTriangle count) triangles.length
  /-- Materializing the face table recovers the original triangles exactly. -/ faces_eq : List.ofFn faces = triangles
  /-- Cached triangulation with certified boundary and internal-edge incidence. -/ triangulation : Stokes.Triangulation
    count triangles.length
  /-- The triangulation reads the exact retained face table. -/ triangulation_faces : ∀ index, triangulation.faces index
    = faces index

constructive_injectivity Indexed

namespace Indexed

open Purelib.Topology.Surface.Boundary
/-- Cache the supplied triangles as indexed faces with automatically certified incidence.

The retained equations tie the materialized face list and triangulation to those exact triangles. -/
@[expose] def build (triangles : List (Stokes.OrientedTriangle count)) : BoundaryCaps.Indexed triangles :=
  let faces := Data.Vector.Basic.vectorOfFn (fun index : Fin triangles.length => triangles[index.val])
  ⟨faces, (OfFn.Basic.ofFn_congr (fun index => Data.Vector.Basic.vectorOfFn_apply _ index)).trans
    (OfFn.Basic.ofFn_getElem triangles),
    EdgeCancellation.triangulateFaces faces, fun _ => rfl⟩

/-- The cached triangulation boundary has the area of the original triangle list. -/
theorem boundary_area {triangles : List (Stokes.OrientedTriangle count)} (indexed : BoundaryCaps.Indexed triangles)
    (points : Fin count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea points indexed.triangulation.boundary = BoundaryCaps.area points triangles := by
  rw [← indexed.triangulation.wedgeSum_eq_boundaryArea points, Stokes.triangleWedgeSum_eq_edgeListArea,
    Stokes.triangleEdgeOccurrences, OfFn.Basic.ofFn_congr indexed.triangulation_faces, indexed.faces_eq]
  rfl

end Indexed
end Purelib.Topology.Surface.Boundary.BoundaryCaps
