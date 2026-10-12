module

meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-!
# Indexed quadrilaterals and their actual diagonal cancellation

The diagonal of the two-triangle subdivision occurs in both orientations.
The explicit incidence reordering exposes exactly the four original sides,
independently of any chosen primitive values or geometric embedding.
-/

namespace Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle PrimitivePoint edgeArea_reverse
  edgeListArea pairedEdgeOccurrences triangleBoundaryArea triangleBoundaryArea_eq_wedgeArea triangleWedgeArea)

set_option genInjectivity false in
/-- Four ordered bounded vertices defining a quadrilateral subdivision.

The two triangles share the diagonal from the first vertex to the third; distinctness of the vertices is not required.
-/
structure IndexedQuadrilateral (count : Nat) where
  /-- The first bounded vertex in the boundary order. -/ first : Fin count
  /-- The second bounded vertex in the boundary order. -/ second : Fin count
  /-- The third bounded vertex in the boundary order. -/ third : Fin count
  /-- The fourth bounded vertex in the boundary order. -/ fourth : Fin count

constructive_injectivity IndexedQuadrilateral

namespace IndexedQuadrilateral

variable {count : Nat}

section
open Purelib.Topology.Mesh
/-- The oriented triangle on the first, second and third vertices. -/
@[expose] def firstTriangle (quad : IndexedQuadrilateral count) : Stokes.OrientedTriangle count :=
  ⟨quad.first, quad.second, quad.third⟩
/-- The oriented triangle on the first, third and fourth vertices. -/
@[expose] def secondTriangle (quad : IndexedQuadrilateral count) : Stokes.OrientedTriangle count
  := ⟨quad.first, quad.third, quad.fourth⟩
/-- The ordered pair of triangles in the quadrilateral subdivision. -/
@[expose] def triangles (quad : IndexedQuadrilateral count) : List (Stokes.OrientedTriangle count)
  := [quad.firstTriangle, quad.secondTriangle]

/-- The four oriented exterior sides in their cyclic order. -/
@[expose] def boundary (quad : IndexedQuadrilateral count) : List (Stokes.OrientedEdge count) :=
  [⟨quad.first, quad.second⟩, ⟨quad.second, quad.third⟩, ⟨quad.third, quad.fourth⟩, ⟨quad.fourth, quad.first⟩]

/-- The shared diagonal oriented from the third vertex to the first. -/
@[expose] def diagonal (quad : IndexedQuadrilateral count) : Stokes.OrientedEdge count :=
  ⟨quad.third, quad.first⟩

/-- Move the two diagonal occurrences past the last two exterior sides. -/
theorem incidence (quad : IndexedQuadrilateral count) :
    Stokes.EdgeReordering (quad.triangles.flatMap OrientedTriangle.boundary)
      (quad.boundary ++ Stokes.pairedEdgeOccurrences [quad.diagonal]) := by
  refine .cons ⟨quad.first, quad.second⟩ (.cons ⟨quad.second, quad.third⟩ ?_)
  exact EdgeReordering.append_swap [quad.diagonal, quad.diagonal.reverse]
    [⟨quad.third, quad.fourth⟩, ⟨quad.fourth, quad.first⟩] []

end

open Purelib.Topology.Mesh in
open Purelib.Topology.Mesh.IndexedQuadrilaterals in
/-- The two triangle wedge areas sum to the quadrilateral boundary area.

The equality holds for arbitrary primitive values at the indexed vertices; the two diagonal contributions cancel with
opposite orientations. -/
theorem wedge_eq_boundary (quad : IndexedQuadrilateral count) (primitive : Fin count →
  Stokes.PrimitivePoint) :
    Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.second) (primitive quad.third) +
      Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.third) (primitive quad.fourth) =
      Stokes.edgeListArea primitive quad.boundary := by
  rw [← Stokes.triangleBoundaryArea_eq_wedgeArea, ← Stokes.triangleBoundaryArea_eq_wedgeArea]
  simp only [Stokes.triangleBoundaryArea, boundary, Stokes.edgeListArea]
  rw [Stokes.edgeArea_reverse (primitive quad.third) (primitive quad.first)]
  ring1

end IndexedQuadrilateral

end Purelib.Topology.Mesh.IndexedQuadrilaterals
