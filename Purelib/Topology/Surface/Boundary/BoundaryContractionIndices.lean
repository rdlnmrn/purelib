module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
public import Purelib.Topology.Surface.Boundary.BoundaryContraction
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

public section

/-!
# Dense finite indices for contracted boundary vertices

Materialize the projection once. The dense carrier has exactly the retained
representatives, and its readback and factorization laws exclude unused
allocation slots. Lookups are explicit finite scans, with exact witnesses.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryContractionIndices

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

open Purelib.Topology.Surface.Boundary.BoundaryContraction
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryContraction -> BoundaryContraction

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {count : Nat} {occurrences : List (Stokes.OrientedEdge count)}
  {boundary : PolygonStokes.BoundaryCycleDecomposition occurrences} {active : List (Fin count)}

/-- Find the first position of a vertex in a finite list with a membership witness.

The result retains its bounded index and the exact element readback equation. -/
@[expose] def locate (vertex : Fin count) : (vertices : List (Fin count)) → vertex ∈ vertices →
    { index : Fin vertices.length // vertices[index.val] = vertex }
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member =>
      if same : vertex = first then ⟨0, same.symm⟩
      else
        let tail := locate vertex rest
          ((Purelib.Data.List.Membership.mem_cons.mp member).resolve_left same)
        ⟨tail.val.succ, tail.property⟩

/-- Reading a duplicate-free vertex list is injective on bounded indices. -/
private theorem at_injective {vertices : List (Fin count)} (unique : vertices.Nodup)
    {first last : Fin vertices.length} (same : vertices[first.val] = vertices[last.val]) : first = last := by
  apply Fin.ext
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · exact (Pairwise.pairwise_getElem unique _ _ first.isLt last.isLt before same).elim
  · exact equal
  · exact (Pairwise.pairwise_getElem unique _ _ last.isLt first.isLt after same.symm).elim

set_option genInjectivity false in
/-- A cached dense projection to the retained contracted representatives.

For active source vertices, reading back the projected index agrees exactly with the original contraction's
normalization. -/
structure Indexed (contraction : BoundaryContraction boundary active) where
  /-- Cached dense representative index for every original vertex. -/ projection : Data.Vector (Fin
    contraction.representatives.length) count
  /-- On active vertices, the dense readback is the retained normalized vertex. -/ representative_eq : ∀ vertex ∈
    active,
    contraction.representatives.get (projection vertex) = contraction.normalize vertex

constructive_injectivity Indexed

namespace Indexed

variable {contraction : BoundaryContraction boundary active}

open Purelib.Topology.Surface.Boundary
/-- Materialize dense representative indices for the retained boundary contraction.

Active vertices use their normalized representative; other slots use the normalized retained fallback. -/
@[expose] def build (contraction : BoundaryContraction boundary active) :
  Indexed contraction :=
  let select := fun vertex : Fin count =>
    if member : vertex ∈ active then (locate (contraction.normalize vertex)
      contraction.representatives (contraction.supported member)).val
    else (locate (contraction.normalize contraction.fallback) contraction.representatives
      (contraction.supported contraction.fallback_active)).val
  { projection := Data.Vector.Basic.vectorOfFn select
    representative_eq := fun vertex member => by
      rw [Data.Vector.Basic.vectorOfFn_apply]
      dsimp only [select]
      rw [dif_pos member]
      exact (locate (contraction.normalize vertex) contraction.representatives
        (contraction.supported member)).property }

/-- Projecting the vertex at a retained representative index returns that index. -/
theorem readback (indexed : Indexed contraction) (index : Fin
  contraction.representatives.length) :
    indexed.projection contraction.representatives[index.val] = index := by
  apply at_injective contraction.unique
  have member : contraction.representatives[index.val] ∈ contraction.representatives := List.getElem_mem index.isLt
  exact (indexed.representative_eq _ (contraction.representative_active member)).trans (contraction.readback member)

/-- On active vertices, dense projections agree exactly when their normalizations agree. -/
theorem projection_eq_iff (indexed : Indexed contraction) {first last : Fin count}
    (firstActive : first ∈ active) (lastActive : last ∈ active) :
    indexed.projection first = indexed.projection last ↔ contraction.normalize first = contraction.normalize last := by
  constructor
  · intro equal
    exact (indexed.representative_eq first firstActive).symm.trans
      ((congrArg (fun index : Fin contraction.representatives.length => contraction.representatives[index.val])
        equal).trans
        (indexed.representative_eq last lastActive))
  · intro equal
    apply at_injective contraction.unique
    exact (indexed.representative_eq first firstActive).trans (equal.trans (indexed.representative_eq last
      lastActive).symm)

/-- The dense projection identifies both endpoints of every physical boundary edge. -/
theorem edge_collapsed (indexed : Indexed contraction) {edge : Stokes.OrientedEdge count}
    (member : edge ∈ boundary.cycles.flatten) : indexed.projection edge.start = indexed.projection edge.finish := by
  obtain ⟨cycle, cycleMember, edgeMember⟩ := SimpleBoundaryCycles.mem_flatten.mp member
  obtain ⟨anchor, closed⟩ := boundary.closed cycle cycleMember
  have included (vertex : Fin count) (present : vertex ∈ cycle.map OrientedEdge.start) : vertex ∈ active := by
    apply contraction.boundary_active
    rw [contraction.groups_eq]
    exact SimpleBoundaryCycles.mem_flatten.mpr ⟨cycle.map OrientedEdge.start,
      Map.mem_map_of_mem cycleMember, present⟩
  exact (indexed.projection_eq_iff (included _ (Map.mem_map_of_mem edgeMember))
    (included _ (SimpleBoundaryCycles.finish_mem closed edgeMember))).mpr (contraction.edge_collapsed member)

/-- Read an assignment on the retained representative at each dense index. -/
@[expose] def factor {Beta : Type} (_indexed : Indexed contraction) (values : Fin count →
  Beta) :
    Fin contraction.representatives.length → Beta := fun index => values contraction.representatives[index.val]

/-- An assignment constant on physical edges factors through the dense projection on active vertices. -/
theorem factor_eq {Beta : Type} (indexed : Indexed contraction) (values : Fin count → Beta)
    (constant : ∀ edge ∈ boundary.cycles.flatten, values edge.start = values edge.finish)
    {vertex : Fin count} (member : vertex ∈ active) : indexed.factor values (indexed.projection vertex) = values vertex
      := by
  exact (congrArg values (indexed.representative_eq vertex member)).trans (contraction.factor values constant vertex)

/-- Agreement on projected active vertices determines a unique assignment on dense indices. -/
theorem factor_unique {Beta : Type} (indexed : Indexed contraction)
    (first last : Fin contraction.representatives.length → Beta)
    (same : ∀ vertex ∈ active, first (indexed.projection vertex) = last (indexed.projection vertex))
    (index : Fin contraction.representatives.length) : first index = last index := by
  have equal := same contraction.representatives[index.val]
    (contraction.representative_active (List.getElem_mem index.isLt))
  rw [indexed.readback] at equal
  exact equal

end Indexed
end Purelib.Topology.Surface.Boundary.BoundaryContractionIndices

end
