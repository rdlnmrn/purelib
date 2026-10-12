module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Cut.PotentialCompatibility
import Purelib.Data.Vector.Basic
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-! Cached, antisymmetric surface readings of a compatible cut-boundary potential. -/

namespace Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)

open Purelib.Topology.Surface.Cut.PotentialCompatibility

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

namespace PotentialReadings

/-- Return the first cached reading for an edge, or zero when no entry has that key. -/
@[expose] def lookup {vertices : Nat} : List (Stokes.OrientedEdge vertices × Gaussian.Basic.Canonical) →
  Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical
  | [], _ => 0
  | entry :: rest, edge => if entry.1 = edge then entry.2 else lookup
    rest edge

end PotentialReadings

section
open Purelib.Topology.Surface.Cut
namespace PotentialReadings

/-- Looking up an edge absent from the cached keys returns zero. -/
private theorem lookup_absent {vertices : Nat} (entries : List (Stokes.OrientedEdge vertices ×
  Gaussian.Basic.Canonical))
    (edge : Stokes.OrientedEdge vertices) (missing : edge ∉ entries.map Prod.fst) : lookup entries
      edge = 0 := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have different : entry.1 ≠ edge := fun same => missing (same ▸ List.mem_cons_self)
      have tail : edge ∉ rest.map Prod.fst := fun member => missing (List.mem_cons_of_mem _ member)
      rw [lookup, if_neg different, ih tail]

end PotentialReadings

namespace PotentialReadings

/-- Unique cached keys make lookup return the exact value of each retained entry. -/
private theorem lookup_member {vertices : Nat} (entries : List (Stokes.OrientedEdge vertices ×
  Gaussian.Basic.Canonical))
    (unique : (entries.map Prod.fst).Nodup) (entry : Stokes.OrientedEdge vertices × Gaussian.Basic.Canonical)
    (member : entry ∈ entries) : lookup entries entry.1 = entry.2 := by
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      obtain ⟨headFresh, restUnique⟩ := List.pairwise_cons.mp unique
      have absent : head.1 ∉ rest.map Prod.fst := fun present => headFresh _ present rfl
      rcases Membership.mem_cons.mp member with same | member
      · subst entry
        rw [lookup, if_pos rfl]
      · have different : head.1 ≠ entry.1 := fun same => absent
          (same.symm ▸ Map.mem_map_of_mem member)
        rw [lookup, if_neg different]
        exact ih restUnique member

end PotentialReadings

end

variable {vertices facesCount : Nat} {faces : Fin facesCount → Stokes.OrientedTriangle vertices}
  {indices : List (Fin facesCount)} {boundary : List (Stokes.OrientedEdge vertices)}
  (patch : Patch.CutPatch faces indices boundary)
  (sourceValue : Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical)
  (potential : Boundary.BoundaryPotential patch.boundary (fun edge => sourceValue (OrientedEdge.map
    patch.vertexLabels edge)))

set_option genInjectivity false in
/-- Cached primitive increments on the retained triangle incidences.

Each entry retains its oriented edge key and the increment computed for that
occurrence. Lookup consumes the same cached entries in their original order. -/
structure PotentialReadings where
  /-- Cached projected edges paired with their retained cut-potential increments. -/ entries : List (Stokes.OrientedEdge
    vertices × Gaussian.Basic.Canonical)
  /-- The entries are exactly the ordered increment map over the original triangle incidences. -/ entries_eq : entries =
    (patch.triangles.flatMap OrientedTriangle.boundary).map
    (fun edge => (OrientedEdge.map patch.vertexLabels edge, potential.values edge.finish - potential.values edge.start))

constructive_injectivity PotentialReadings

namespace PotentialReadings

open Purelib.Topology.Surface.Cut in
/-- Cache the potential increment for every original projected cut-triangle edge occurrence. -/
@[expose] def build : PotentialReadings patch sourceValue potential :=
  ⟨(patch.triangles.flatMap OrientedTriangle.boundary).map
    (fun edge => (OrientedEdge.map patch.vertexLabels edge, potential.values edge.finish - potential.values
      edge.start)), rfl⟩

variable {patch sourceValue potential} (data : PotentialReadings patch
  sourceValue potential)

/-- Cached reading keys are exactly the projected original cut-triangle incidence list. -/
theorem keys_eq : data.entries.map Prod.fst =
    (patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels) := by
  rw [data.entries_eq, Map.map_map]
  rfl

section
open Purelib.Topology.Surface.Cut
/-- Read the cached increment at the supplied oriented surface edge. -/
@[expose] def raw (edge : Stokes.OrientedEdge vertices) : Gaussian.Basic.Canonical := lookup
  data.entries edge

/-- The raw reading is zero outside the retained projected incidence keys. -/
theorem raw_absent (edge : Stokes.OrientedEdge vertices) (missing : edge ∉ data.entries.map Prod.fst) : data.raw edge =
  0 :=
  lookup_absent data.entries edge missing

/-- Unique projected incidence makes each raw reading the exact retained cut-potential difference. -/
theorem raw_occurrence
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (edge : Stokes.OrientedEdge patch.count) (member : edge ∈ patch.triangles.flatMap OrientedTriangle.boundary) :
    data.raw (OrientedEdge.map patch.vertexLabels edge) = potential.values edge.finish - potential.values edge.start :=
      by
  apply lookup_member data.entries (data.keys_eq ▸ unique)
    (OrientedEdge.map patch.vertexLabels edge, potential.values edge.finish - potential.values edge.start)
  rw [data.entries_eq]
  exact Map.mem_map_of_mem member

end

/-- Compatible boundary values make raw readings antisymmetric when both edge orientations occur. -/
theorem raw_opposite
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (anti : ∀ edge, sourceValue edge.reverse = -sourceValue edge)
    (edge : Stokes.OrientedEdge vertices) (first : edge ∈ data.entries.map Prod.fst)
    (last : edge.reverse ∈ data.entries.map Prod.fst) : data.raw edge.reverse = -data.raw edge := by
  rw [data.keys_eq] at first last
  obtain ⟨firstEdge, firstMember, firstEq⟩ := Map.mem_map.mp first
  obtain ⟨lastEdge, lastMember, lastEq⟩ := Map.mem_map.mp last
  have same := CutPatch.potential_opposite patch unique sourceValue anti potential firstMember lastMember
    (lastEq.trans (congrArg OrientedEdge.reverse firstEq.symm))
  have firstRead := data.raw_occurrence unique firstEdge firstMember
  have lastRead := data.raw_occurrence unique lastEdge lastMember
  rw [firstEq] at firstRead
  rw [lastEq] at lastRead
  exact lastRead.trans (same.trans (congrArg Neg.neg firstRead.symm))

/-- An unsupported orientation reads the negative cached value of its reverse. -/
@[expose] def value (edge : Stokes.OrientedEdge vertices) : Gaussian.Basic.Canonical :=
  if edge ∈ data.entries.map Prod.fst then data.raw edge else -data.raw edge.reverse

open Purelib.Topology.Surface.Cut.PotentialReadings
open _root_.Purelib.Topology.Surface.Cut renaming PotentialReadings -> PotentialReadings
/-- The completed surface reading changes sign under edge reversal. -/
theorem value_reverse
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (anti : ∀ edge, sourceValue edge.reverse = -sourceValue edge) (edge : Stokes.OrientedEdge vertices) :
    data.value edge.reverse = -data.value edge := by
  unfold value
  rw [OrientedEdge.reverse_reverse]
  by_cases first : edge ∈ data.entries.map Prod.fst
  · by_cases last : edge.reverse ∈ data.entries.map Prod.fst
    · rw [if_pos first, if_pos last]
      exact raw_opposite data unique anti edge first last
    · rw [if_pos first, if_neg last]
  · by_cases last : edge.reverse ∈ data.entries.map Prod.fst
    · rw [if_neg first, if_pos last, neg_neg]
    · rw [if_neg first, if_neg last, data.raw_absent edge first, data.raw_absent edge.reverse last, neg_zero, neg_zero]

/-- On original cut-triangle incidence, the completed reading is the exact retained potential difference. -/
theorem value_occurrence
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (edge : Stokes.OrientedEdge patch.count) (member : edge ∈ patch.triangles.flatMap OrientedTriangle.boundary) :
    data.value (OrientedEdge.map patch.vertexLabels edge) = potential.values edge.finish - potential.values edge.start
      := by
  have present : OrientedEdge.map patch.vertexLabels edge ∈ data.entries.map Prod.fst :=
    data.keys_eq ▸ Map.mem_map_of_mem member
  rw [value, if_pos present]
  exact data.raw_occurrence unique edge member

/-- On the original projected boundary, the completed reading equals the supplied source reading. -/
theorem value_boundary
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (edge : Stokes.OrientedEdge patch.count) (member : edge ∈ patch.boundary) :
    data.value (OrientedEdge.map patch.vertexLabels edge) = sourceValue (OrientedEdge.map patch.vertexLabels edge) :=
  (value_occurrence data unique edge ((EdgeReordering.mem_iff patch.incidence edge).mpr
    (Membership.mem_append.mpr (Or.inl member)))).trans
    (potential.increments edge member)

end PotentialReadings
end Purelib.Topology.Surface.Cut

end
