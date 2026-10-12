module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
-- The exposed split map retains this owner's exact mapped-concatenation certificate.
public import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Surface.Sewing.VertexSewing
import Batteries.Logic

public section

/-!
# Lifting specified boundary occurrences through a vertex projection

The lookup uses the displayed prefix, not equality of surface labels.  In
particular, repeated images do not change which cut occurrence is selected.
-/

namespace Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

/-- Project a certified original path and both retained endpoints through the supplied vertex map. -/
theorem pathEndpoints_map {source target : Nat} (vertex : Fin source → Fin target)
    {edges : List (Stokes.OrientedEdge source)} {start finish : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edges.map (OrientedEdge.map vertex)) (vertex
      start) (vertex finish) := by
  induction path with
  | nil index => exact .nil (vertex index)
  | cons tail ih => exact .cons ih

/-- Pointwise equal composed vertex maps give identical projections of the original edge list.

Each ordered edge contributes its two retained endpoints. Scalar endpoint
equalities identify the composed projection along the same original list. -/
theorem edgeList_map_comp {first second third : Nat} (left : Fin first → Fin second) (right : Fin second → Fin third)
    (direct : Fin first → Fin third) (equal : ∀ index, right (left index) = direct index) (edges : List
      (Stokes.OrientedEdge first)) :
    (edges.map (OrientedEdge.map left)).map (OrientedEdge.map right) = edges.map (OrientedEdge.map direct) := by
  rw [Map.map_map]
  exact Map.map_congr_left (fun edge _ => congrArg₂ OrientedEdge.mk (equal edge.start) (equal edge.finish))

/-- Pointwise equal composed vertex maps give identical projections of the original triangle list.

Each triangle contributes its three retained ordered corners. The supplied
pointwise equalities identify their composed projections on the original spine. -/
theorem triangleList_map_comp {first second third : Nat} (left : Fin first → Fin second) (right : Fin second → Fin
  third)
    (direct : Fin first → Fin third) (equal : ∀ index, right (left index) = direct index) (triangles : List
      (Stokes.OrientedTriangle first)) :
    (triangles.map (OrientedTriangle.map left)).map (OrientedTriangle.map right) = triangles.map (OrientedTriangle.map
      direct) := by
  rw [Map.map_map]
  apply Map.map_congr_left
  intro triangle _
  change OrientedTriangle.mk (right (left triangle.first)) (right (left triangle.second)) (right (left triangle.third))
    = _
  rw [equal triangle.first, equal triangle.second, equal triangle.third]
  rfl

/-- Projecting original triangles commutes with expanding their ordered boundary edge occurrences.

Every face contributes the same three projected edges in its cyclic order.
The structural tail equality retains all boundary occurrences and repetitions. -/
theorem triangleBoundaries_map {source target : Nat} (vertex : Fin source → Fin target) :
    (triangles : List (Stokes.OrientedTriangle source)) →
    (triangles.map (OrientedTriangle.map vertex)).flatMap OrientedTriangle.boundary =
      (triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map vertex)
  | [] => rfl
  | triangle :: triangles => by
      simp only [List.map_cons, Flatten.flatMap_cons, Map.map_append,
        Purelib.Topology.Surface.Sewing.VertexSewing.OrientedTriangle.boundary_map]
      exact congrArg (List.append ((OrientedTriangle.map vertex triangle).boundary))
        (Purelib.Topology.Surface.Sewing.SewingProjection.triangleBoundaries_map vertex triangles)

/-- An injective vertex projection preserves nonloop edges in the original list. -/
theorem nonloop_map {source target : Nat} (vertex : Fin source → Fin target) (injective : Function.Injective vertex)
    {edges : List (Stokes.OrientedEdge source)} (nonloop : ∀ edge ∈ edges, edge.start ≠ edge.finish) :
    ∀ edge ∈ edges.map (OrientedEdge.map vertex), edge.start ≠ edge.finish := by
  intro edge member equal
  rcases Map.mem_map.mp member with ⟨original, originalMember, equation⟩
  cases equation
  exact nonloop original originalMember (injective equal)

/-- Reading projected edge starts agrees with projecting the original start list.

Each source edge retains its original first endpoint. Both mapped lists apply
the supplied vertex projection to that same endpoint in the same order. -/
theorem edgeStarts_map {source target : Nat} (vertex : Fin source → Fin target) (edges : List (Stokes.OrientedEdge
  source)) :
    (edges.map (OrientedEdge.map vertex)).map OrientedEdge.start = (edges.map OrientedEdge.start).map vertex := by
  rw [Map.map_map, Map.map_map]
  rfl

/-- A finite edge-occurrence reordering preserves edge membership.

Each original occurrence is transported through cons, adjacent swap and
composition certificates using its retained membership constructor. -/
theorem EdgeReordering.mem_iff {count : Nat} {left right : List (Stokes.OrientedEdge count)}
    (ordering : Stokes.EdgeReordering left right) (edge : Stokes.OrientedEdge count) : edge ∈ left ↔ edge ∈ right := by
  induction ordering with
  | nil => exact ⟨fun member => member, fun member => member⟩
  | cons head rest ih =>
      constructor
      · intro member
        cases member with
        | head => exact List.Mem.head _
        | tail _ member => exact List.Mem.tail _ (ih.mp member)
      · intro member
        cases member with
        | head => exact List.Mem.head _
        | tail _ member => exact List.Mem.tail _ (ih.mpr member)
  | swap first second remaining =>
      constructor
      · intro member
        cases member with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ member =>
            cases member with
            | head => exact List.Mem.head _
            | tail _ member => exact List.Mem.tail _ (List.Mem.tail _ member)
      · intro member
        cases member with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ member =>
            cases member with
            | head => exact List.Mem.head _
            | tail _ member => exact List.Mem.tail _ (List.Mem.tail _ member)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Reordering original edges preserves uniqueness of their start vertices.

The original occurrence certificate transports start membership through cons,
adjacent swap and composition while retaining the supplied nodup evidence. -/
theorem EdgeReordering.starts_nodup {count : Nat} {left right : List (Stokes.OrientedEdge count)}
    (ordering : Stokes.EdgeReordering left right) (simple : (left.map OrientedEdge.start).Nodup) :
    (right.map OrientedEdge.start).Nodup := by
  induction ordering with
  | nil => exact .nil
  | cons edge tail ih =>
      rcases List.pairwise_cons.mp simple with ⟨fresh, remaining⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih remaining⟩
      intro index member
      rcases Map.mem_map.mp member with ⟨original, inRight, equal⟩
      exact fresh index (Map.mem_map.mpr
        ⟨original, (EdgeReordering.mem_iff tail original).mpr inRight, equal⟩)
  | swap first second remaining =>
      rcases List.pairwise_cons.mp simple with ⟨firstFresh, restSimple⟩
      rcases List.pairwise_cons.mp restSimple with ⟨secondFresh, tailSimple⟩
      apply List.pairwise_cons.mpr
      constructor
      · intro index member
        rcases Membership.mem_cons.mp member with equal | member
        · cases equal
          exact Ne.symm (firstFresh second.start List.mem_cons_self)
        · exact secondFresh index member
      · exact List.pairwise_cons.mpr ⟨fun index member => firstFresh index (List.mem_cons_of_mem _ member), tailSimple⟩
  | trans first second ihFirst ihSecond => exact ihSecond (ihFirst simple)

namespace BoundarySplit

/-- The retained cyclic tail has unique starts and excludes the selected edge's original start. -/
theorem rest_simple {count : Nat} {boundary : List (Stokes.OrientedEdge count)} (split : PolygonStokes.BoundarySplit
  boundary)
    (simple : (boundary.map OrientedEdge.start).Nodup) :
    (split.rest.map OrientedEdge.start).Nodup ∧ ∀ edge ∈ split.rest, edge.start ≠ split.edge.start := by
  have rotated := SewingProjection.EdgeReordering.starts_nodup split.ordering simple
  rcases List.pairwise_cons.mp rotated with ⟨fresh, remaining⟩
  exact ⟨remaining, fun edge member => Ne.symm (fresh edge.start (Map.mem_map_of_mem member))⟩

/-- Every edge in the retained cyclic tail belongs to the original boundary.

The stored split equation retains the prefix and suffix as boundary occurrences.
Membership in their cyclic concatenation therefore supplies original membership. -/
theorem rest_mem {count : Nat} {boundary : List (Stokes.OrientedEdge count)} (split : PolygonStokes.BoundarySplit
  boundary)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ split.rest) : edge ∈ boundary := by
  cases split with
  | mk before seam after equation =>
      cases equation
      rcases Membership.mem_append.mp member with inAfter | inBefore
      · exact Membership.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ inAfter))
      · exact Membership.mem_append.mpr (Or.inl inBefore)

/-- Project the exact selected boundary occurrence with its prefix and suffix.

The supplied vertex map acts on every original edge in order. The retained
split equation certifies the projected occurrence without searching its labels. -/
@[expose] def map {source target : Nat} {boundary : List (Stokes.OrientedEdge source)} (vertex : Fin source → Fin
  target)
    (split : PolygonStokes.BoundarySplit boundary) : PolygonStokes.BoundarySplit (boundary.map (OrientedEdge.map
      vertex)) :=
  { before := split.before.map (OrientedEdge.map vertex)
    edge := OrientedEdge.map vertex split.edge
    after := split.after.map (OrientedEdge.map vertex)
    equation := (congrArg (List.map (OrientedEdge.map vertex)) split.equation).trans (by
      rw [Map.map_append, List.map_cons]) }

/-- Projection preserves the retained cyclic tail of the selected occurrence.

The projected split maps the original suffix and prefix separately. Their
concatenation is the mapped original cyclic tail in the same displayed order. -/
theorem map_rest {source target : Nat} {boundary : List (Stokes.OrientedEdge source)} (vertex : Fin source → Fin target)
    (split : PolygonStokes.BoundarySplit boundary) : (BoundarySplit.map vertex split).rest = split.rest.map
      (OrientedEdge.map vertex) :=
  (Map.map_append ..).symm

set_option genInjectivity false in
/-- An original selected occurrence lifted through an exact boundary projection.

Separate prefix, edge and suffix equations retain the occurrence even when projected vertex labels repeat. -/
structure Lift {source target : Nat} (vertex : Fin source → Fin target)
    {baseBoundary : List (Stokes.OrientedEdge target)} (base : PolygonStokes.BoundarySplit baseBoundary) (boundary :
      List (Stokes.OrientedEdge source)) where
  /-- Retained selected occurrence in the original source boundary. -/ split : PolygonStokes.BoundarySplit boundary
  /-- The lifted original prefix projects to the specified base prefix. -/ before_eq : split.before.map
    (OrientedEdge.map vertex) = base.before
  /-- The exact lifted original edge projects to the selected base edge. -/ edge_eq : OrientedEdge.map vertex split.edge
    = base.edge
  /-- The lifted original suffix projects to the specified base suffix. -/ after_eq : split.after.map (OrientedEdge.map
    vertex) = base.after

constructive_injectivity Lift

/-- Follow the displayed prefix to lift its selected occurrence and suffix.

The exact boundary-projection equation determines each retained source head.
Recursive descent follows the supplied prefix without choosing a repeated label. -/
@[expose] def liftPieces {source target : Nat} (vertex : Fin source → Fin target) :
    (before : List (Stokes.OrientedEdge target)) → (edge : Stokes.OrientedEdge target) → (after : List
      (Stokes.OrientedEdge target)) →
    (boundary : List (Stokes.OrientedEdge source)) → boundary.map (OrientedEdge.map vertex) = before ++ edge :: after →
    BoundarySplit.Lift vertex (⟨before, edge, after, rfl⟩ : PolygonStokes.BoundarySplit (before ++ edge :: after))
      boundary
  | [], _, _, [], equation => by cases equation
  | [], edge, after, first :: remaining, equation =>
      ⟨⟨[], first, remaining, rfl⟩, rfl, (List.cons.inj equation).1, (List.cons.inj equation).2⟩
  | _ :: _, _, _, [], equation => by cases equation
  | head :: before, edge, after, first :: remaining, equation =>
      let tail := Purelib.Topology.Surface.Sewing.SewingProjection.BoundarySplit.liftPieces vertex before edge after
        remaining (List.cons.inj equation).2
      { split := ⟨first :: tail.split.before, tail.split.edge, tail.split.after, congrArg (List.cons first)
        tail.split.equation⟩
        before_eq := congrArg₂ List.cons (List.cons.inj equation).1 tail.before_eq
        edge_eq := tail.edge_eq
        after_eq := tail.after_eq }

/-- Lift a selected occurrence from its exact boundary-projection equation.

The retained base split supplies the ordered prefix, selected edge and suffix.
Their original source occurrences are read from the supplied boundary. -/
@[expose] def lift {source target : Nat} (vertex : Fin source → Fin target)
    {baseBoundary : List (Stokes.OrientedEdge target)} (base : PolygonStokes.BoundarySplit baseBoundary)
    (boundary : List (Stokes.OrientedEdge source)) (equation : boundary.map (OrientedEdge.map vertex) = baseBoundary) :
    BoundarySplit.Lift vertex base boundary := by
  cases base with
  | mk before edge after splitEquation =>
      cases splitEquation
      exact BoundarySplit.liftPieces vertex before edge after boundary equation

/-- Projecting the lifted original cyclic tail recovers the selected base tail exactly.

Separate retained suffix and prefix equations identify both projected pieces.
Their concatenation recovers the supplied base split without a label search. -/
theorem Lift.rest_eq {source target : Nat} {vertex : Fin source → Fin target}
    {baseBoundary : List (Stokes.OrientedEdge target)} {base : PolygonStokes.BoundarySplit baseBoundary} {boundary :
      List (Stokes.OrientedEdge source)}
    (lifted : BoundarySplit.Lift vertex base boundary) : lifted.split.rest.map (OrientedEdge.map vertex) = base.rest :=
      by
  rw [BoundarySplit.rest, Map.map_append, lifted.after_eq, lifted.before_eq]
  rfl

end BoundarySplit

end Purelib.Topology.Surface.Sewing.SewingProjection
