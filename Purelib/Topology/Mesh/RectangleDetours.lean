module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
public import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
public import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.List

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Topology.Chain

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut.JumpPaths

public section

/-!
# Explicit side detours for rectangular triangle edges

The two diagonals use the bottom and right sides in opposite orders and
orientations. Endpoints are preserved exactly. Area is not silently declared
unchanged: its difference is the displayed first-triangle contribution.
-/

namespace Purelib.Topology.Mesh

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea
  triangleWedgeArea)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)

variable {count : Nat}

set_option backward.match.sparseCases false in
/-- Replace a rectangle diagonal by its two oriented bottom and right sides.

The upward diagonal takes these sides in order; the downward diagonal reverses the path. Exterior sides remain singleton
paths. -/
@[expose] def IndexedQuadrilaterals.IndexedQuadrilateral.detour (quad :
  IndexedQuadrilateral count) : RectangleEdge.Kind → List (Stokes.OrientedEdge count)
  | .upDiagonal => [(IndexedQuadrilateral.edge quad) .bottom, (IndexedQuadrilateral.edge quad) .right]
  | .downDiagonal => CutPath.reverse [(IndexedQuadrilateral.edge quad) .bottom, (IndexedQuadrilateral.edge quad) .right]
  | kind => [(IndexedQuadrilateral.edge quad) kind]

open Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral (detour)

/-- Each rectangular side detour retains the endpoints of its original edge. -/
theorem RectangleDetours.detour_endpoints (quad : IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish ((IndexedQuadrilateral.detour quad) kind)
      ((IndexedQuadrilateral.edge quad) kind).start ((IndexedQuadrilateral.edge quad) kind).finish := by
  cases kind with
  | bottom => exact .cons (.nil _)
  | right => exact .cons (.nil _)
  | top => exact .cons (.nil _)
  | left => exact .cons (.nil _)
  | upDiagonal => exact .cons (.cons (.nil _))
  | downDiagonal => exact CutPath.reverse_endpoints (.cons (.cons (.nil _)))

/-- Every rectangular edge kind occurs in the two subdivision triangle boundaries.

The retained two-triangle boundary enumerates all six oriented rectangle edge kinds. Each kind is witnessed by its
original position in that finite traversal. -/
theorem RectangleDetours.edge_member (quad : IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    (IndexedQuadrilateral.edge quad) kind ∈ quad.triangles.flatMap OrientedTriangle.boundary := by
  rw [(IndexedQuadrilateral.triangleEdges_eq quad)]
  exact Map.mem_map.mpr ⟨kind, by
    cases kind with
    | bottom => exact List.Mem.head _
    | right => exact List.Mem.tail _ (List.Mem.head _)
    | downDiagonal => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | upDiagonal => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    | top => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    | left =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    , rfl⟩

/-- Every edge of a rectangular detour is supported by the subdivision boundaries.

Support allows either orientation of a retained boundary edge. -/
theorem RectangleDetours.detour_supported (quad : IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    CutPath.Supported (quad.triangles.flatMap OrientedTriangle.boundary) ((IndexedQuadrilateral.detour quad) kind) := by
  have one (kind : RectangleEdge.Kind) : CutPath.Supported (quad.triangles.flatMap OrientedTriangle.boundary)
    [(IndexedQuadrilateral.edge quad) kind] := by
    intro edge member
    have same := Membership.mem_singleton.mp member
    subst edge
    exact Or.inl ((RectangleDetours.edge_member quad) kind)
  cases kind with
  | bottom => exact one _
  | right => exact one _
  | top => exact one _
  | left => exact one _
  | upDiagonal => exact CutPath.supported_append (one .bottom) (one .right)
  | downDiagonal => exact CutPath.supported_reverse (CutPath.supported_append (one .bottom) (one .right))

/-- Diagonal detours have length two and exterior-side detours have length one. -/
theorem RectangleDetours.detour_length (quad : IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    ((IndexedQuadrilateral.detour quad) kind).length = if kind = .upDiagonal ∨ kind = .downDiagonal then 2 else 1 := by
  cases kind <;> rfl

/-- Every rectangular detour contains at most two edges. -/
theorem RectangleDetours.detour_length_le (quad : IndexedQuadrilateral count) (kind : RectangleEdge.Kind) :
    ((IndexedQuadrilateral.detour quad) kind).length ≤ 2 := by
  rw [(RectangleDetours.detour_length quad)]
  split <;> omega

/-- A diagonal detour changes edge area by the signed first-triangle wedge area.

The upward diagonal adds that area, the downward diagonal subtracts it, and exterior-side detours preserve area exactly.
-/
theorem RectangleDetours.detour_area (quad : IndexedQuadrilateral count) (primitive : Fin count →
  Stokes.PrimitivePoint) (kind : RectangleEdge.Kind) :
    Stokes.edgeListArea primitive ((IndexedQuadrilateral.detour quad) kind) = Stokes.edgeArea (primitive
      ((IndexedQuadrilateral.edge quad) kind).start) (primitive ((IndexedQuadrilateral.edge quad) kind).finish) +
      (if kind = .upDiagonal then Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.second) (primitive
        quad.third)
       else if kind = .downDiagonal then -Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.second)
         (primitive quad.third)
       else 0) := by
  cases kind with
  | bottom =>
    rw [if_neg (by intro same; cases same), if_neg (by intro same; cases same)]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
  | right =>
    rw [if_neg (by intro same; cases same), if_neg (by intro same; cases same)]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
  | top =>
    rw [if_neg (by intro same; cases same), if_neg (by intro same; cases same)]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
  | left =>
    rw [if_neg (by intro same; cases same), if_neg (by intro same; cases same)]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
  | upDiagonal =>
    rw [if_pos rfl]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
    ring1
  | downDiagonal =>
    rw [if_neg (by intro same; cases same), if_pos rfl]
    dsimp only [IndexedQuadrilateral.detour, CutPath.reverse, List.reverse,
      List.reverseAux, List.map, List.append, IndexedQuadrilateral.edge,
      OrientedEdge.reverse, Stokes.edgeListArea, Stokes.edgeArea,
      Stokes.triangleWedgeArea]
    ring1

/-- Find an edge kind in a finite candidate list using retained membership evidence.

The returned bounded certificate identifies a kind whose quadrilateral edge equals the supplied edge; selection scans
the candidates in order. -/
@[expose] def RectangleDetours.selectKind (quad : IndexedQuadrilateral count) (edge : Stokes.OrientedEdge count) :
    (kinds : List RectangleEdge.Kind) → edge ∈ kinds.map (IndexedQuadrilateral.edge quad) → { kind : RectangleEdge.Kind
      // (IndexedQuadrilateral.edge quad) kind = edge }
  | [], member => (List.not_mem_nil member).elim
  | kind :: rest, member =>
      if same : (IndexedQuadrilateral.edge quad) kind = edge then ⟨kind, same⟩
      else Purelib.Topology.Mesh.RectangleDetours.selectKind quad edge rest ((Membership.mem_cons.mp
        member).resolve_left (Ne.symm same))

/-- Total finite selection of the actual triangle-edge kind. -/
@[expose] def RectangleDetours.kindOfEdge (quad : IndexedQuadrilateral count) (edge : Stokes.OrientedEdge count)
    (member : edge ∈ quad.triangles.flatMap OrientedTriangle.boundary) :
    { kind : RectangleEdge.Kind // (IndexedQuadrilateral.edge quad) kind = edge } :=
  RectangleDetours.selectKind quad edge RectangleEdge.kinds (by
    rw [← (IndexedQuadrilateral.triangleEdges_eq quad)]
    exact member)

end Purelib.Topology.Mesh
