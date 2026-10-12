module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Mesh.CornerWalks
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Topology.Surface.Chord.PairChordCoverage
public import Purelib.Topology.Surface.Cut.VertexGluing
public import Purelib.Topology.Surface.Chord.Coordinates
import Purelib.Tactic.Ring

/-!
# Completeness of actual cut-chord periods and physical-boundary values

The finite boundary potential descends through precisely the recorded
vertex identifications. If chord periods and physical-boundary values
vanish, every closed supported surface word consequently has value zero.
No face-zero premise is used: retraction corrections remain separate.
-/

public section

namespace Purelib.Riemann.Periods.CutPeriodCompleteness

open Purelib

open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.VertexGluing (PairVertexJoin)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.CornerWalks (VertexConnection)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry)
open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append wordValue_reordering)

section
open Purelib.Topology
open Purelib.Data
/-- Summing a word after vertex relabeling equals summing the pulled-back edge valuation. -/
theorem SewingRetraction.wordValue_map {source target : Nat} (labels : Fin source → Fin target)
    (value : OrientedEdge target → Gaussian.Basic.Canonical) (edges : List (OrientedEdge source)) :
    Surface.Sewing.SewingRetraction.wordValue value (edges.map (Surface.Sewing.VertexSewing.OrientedEdge.map labels)) =
      Surface.Sewing.SewingRetraction.wordValue (fun edge => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
      edge)) edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => exact congrArg (value (Surface.Sewing.VertexSewing.OrientedEdge.map labels edge) + ·) ih

/-- A valuation matching every paired endpoint is constant along the generated vertex-join relation. -/
theorem PairVertexJoin.values_eq {source target : Nat} {labels : Fin source → Fin target}
    {pairs : List (Surface.Word.ProjectedEdgePairs.ProjectedEdgePair labels)} (values : Fin source →
      Gaussian.Basic.Canonical)
    (matched : ∀ pair ∈ pairs, values pair.first.start = values pair.second.finish ∧ values pair.first.finish = values
      pair.second.start)
    {first last : Fin source} (joined : Surface.Cut.VertexGluing.PairVertexJoin pairs first last) : values first =
      values last := by
  induction joined with
  | refl => rfl
  | start pair member => exact (matched pair member).1
  | finish pair member => exact (matched pair member).2
  | symm previous ih => exact ih.symm
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

end

namespace ProjectedEdgePairing

variable {source target : Nat} {labels : Fin source → Fin target} {boundary : List (OrientedEdge source)}

section
open Purelib.Topology
open Purelib.Data
/-- Oppositely paired edge occurrences have total value zero under an antisymmetric valuation. -/
private theorem paired_value_zero (value : OrientedEdge target → Gaussian.Basic.Canonical) (anti : ∀ edge, value
  edge.reverse = -value edge)
    (pairs : List (Surface.Word.ProjectedEdgePairs.ProjectedEdgePair labels)) :
    Surface.Sewing.SewingRetraction.wordValue (fun edge => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
      edge)) (Surface.Word.ProjectedEdgePairs.ProjectedEdgePair.occurrences pairs) = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      change value (Surface.Sewing.VertexSewing.OrientedEdge.map labels pair.first) + (value
        (Surface.Sewing.VertexSewing.OrientedEdge.map labels pair.second) + _) = 0
      rw [pair.opposite, anti, ih]
      ring1

/-- An antisymmetric paired boundary valuation vanishes when every retained physical edge has value zero. -/
theorem boundary_value_zero (pairing : Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing labels boundary)
    (value : OrientedEdge target → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (physical : ∀ edge ∈ pairing.boundary, value (Surface.Sewing.VertexSewing.OrientedEdge.map labels edge) = 0) :
    Surface.Sewing.SewingRetraction.wordValue (fun edge => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
      edge)) boundary = 0 := by
  have allZero : ∀ edges : List (OrientedEdge source), (∀ edge ∈ edges, value
    (Surface.Sewing.VertexSewing.OrientedEdge.map labels edge) = 0) →
      Surface.Sewing.SewingRetraction.wordValue (fun edge => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
        edge)) edges = 0 := by
    intro edges
    induction edges with
    | nil => exact fun _ => rfl
    | cons edge rest ih =>
        intro zero
        rw [Surface.Sewing.SewingRetraction.wordValue, zero edge List.mem_cons_self, ih (fun next member => zero next
          (List.mem_cons_of_mem _ member)), add_zero]
  rw [Surface.Sewing.SewingRetraction.wordValue_reordering _ pairing.incidence,
    Surface.Sewing.SewingRetraction.wordValue_append, allZero pairing.boundary physical,
    paired_value_zero value anti, add_zero]

/-- Every retained paired-generator chord has zero coordinate contraction.

The contraction includes all physical coefficients of that actual chord and uses the projected generator edge values. -/
@[expose] def ChordsZero (pairing : Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing labels boundary) (value :
  OrientedEdge target → Gaussian.Basic.Canonical) : Prop :=
  ∀ (index : Fin (Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing).alphabet.count),
    (Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false →
    ∀ chord : Topology.Surface.Cut.Chord.CutBoundaryWord (Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord
      pairing) index,
      Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (Surface.Chord.Coordinates.coordinates chord).totals
        (fun column => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
          ((Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing).alphabet.generators column))) = 0

end

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
/-- Vanishing chord contractions identify the boundary potential at both endpoints of each recorded pair.

The projected boundary is duplicate-free, the boundary path is closed, and the edge valuation is antisymmetric. -/
theorem potential_pair_eq (pairing : Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing labels boundary)
    (unique : (boundary.map (Surface.Sewing.VertexSewing.OrientedEdge.map labels)).Nodup)
    (value : OrientedEdge target → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    {anchor : Fin source} (closed : Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary
      anchor anchor)
    (potential : Topology.Surface.Boundary.BoundaryPotential boundary (fun edge => value
      (Surface.Sewing.VertexSewing.OrientedEdge.map labels edge)))
    (zero : ChordsZero pairing value) (pair : Surface.Word.ProjectedEdgePairs.ProjectedEdgePair labels) (member : pair ∈
      pairing.pairs) :
    potential.values pair.first.start = potential.values pair.second.finish ∧
      potential.values pair.first.finish = potential.values pair.second.start := by
  let selected := Surface.Chord.PairChordCoverage.ProjectedEdgePairing.pairChord pairing unique pair member
  have chordZero := (Surface.Boundary.BoundaryCoordinates.WordCoordinates.value_eq
    (Surface.Chord.Coordinates.coordinates selected.chord) value anti).trans (zero selected.index selected.paired
    selected.chord)
  have pathValue := potential.path_value (fun edge => anti (Surface.Sewing.VertexSewing.OrientedEdge.map labels edge))
    (selected.chord.interval_path closed) selected.chord.interval_supported
  have mapped : Surface.Sewing.SewingRetraction.wordValue value (selected.chord.interval.map (fun entry =>
    Surface.Sewing.VertexSewing.OrientedEdge.map labels entry.edge)) =
      Surface.Sewing.SewingRetraction.wordValue (fun edge => value (Surface.Sewing.VertexSewing.OrientedEdge.map labels
        edge)) (selected.chord.interval.map Surface.Cut.BoundaryWord.CutWordEntry.edge) := by
    rw [← Periods.CutPeriodCompleteness.SewingRetraction.wordValue_map, Data.List.Map.map_map]
    rfl
  have difference := pathValue.symm.trans (mapped.symm.trans chordZero)
  rw [selected.first_eq, selected.second_eq] at difference
  have firstEq : potential.values pair.first.start = potential.values pair.second.finish :=
    (Gaussian.Basic.gaussian_eq_of_sub_eq_zero difference).symm
  have firstIncrement := potential.increments pair.first
    (Surface.Chord.PairChordCoverage.ProjectedEdgePairing.pair_edges_mem pairing member).1
  have secondIncrement := potential.increments pair.second
    (Surface.Chord.PairChordCoverage.ProjectedEdgePairing.pair_edges_mem pairing member).2
  rw [pair.opposite, anti] at secondIncrement
  refine ⟨firstEq, Gaussian.Basic.gaussian_eq_of_sub_eq_zero ?_⟩
  calc
    potential.values pair.first.finish - potential.values pair.second.start =
        (potential.values pair.first.finish - potential.values pair.first.start) +
          (potential.values pair.second.finish - potential.values pair.second.start) := by rw [firstEq]; ring1
    _ = 0 := by rw [firstIncrement, secondIncrement]; ring1

end ProjectedEdgePairing

namespace CutPatch

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (OrientedEdge vertexCount)}

open Purelib.Topology
open Purelib.Data
/-- Lift a supported oriented edge to active cut vertices and its exact potential increment.

Forward and reversed boundary support both retain the original vertex labels; antisymmetry handles reversed increments.
-/
private theorem lifted_step (patch : Surface.Cut.Patch.CutPatch faces indices boundary)
    (value : OrientedEdge vertexCount → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (potential : Topology.Surface.Boundary.BoundaryPotential patch.boundary (fun edge => value
      (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels edge)))
    {edge : OrientedEdge vertexCount}
    (supported : edge ∈ patch.boundary.map (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels) ∨
      edge.reverse ∈ patch.boundary.map (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels)) :
    ∃ first last : Fin patch.count, Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch first ∧
      Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch last ∧
      patch.vertexLabels first = edge.start ∧ patch.vertexLabels last = edge.finish ∧
        value edge = potential.values last - potential.values first := by
  rcases supported with forward | backward
  · obtain ⟨lifted, member, same⟩ := List.Map.mem_map.mp forward
    exact ⟨lifted.start, lifted.finish, Surface.Cut.VertexGluing.CutPatch.boundary_vertex_active patch member (Or.inl
      rfl),
      Surface.Cut.VertexGluing.CutPatch.boundary_vertex_active patch member (Or.inr rfl), congrArg OrientedEdge.start
        same, congrArg OrientedEdge.finish same,
      (congrArg value same).symm.trans (potential.increments lifted member).symm⟩
  · obtain ⟨lifted, member, same⟩ := List.Map.mem_map.mp backward
    have reversed : Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels lifted.reverse = edge :=
      (congrArg OrientedEdge.reverse same).trans (OrientedEdge.reverse_reverse edge)
    exact ⟨lifted.finish, lifted.start, Surface.Cut.VertexGluing.CutPatch.boundary_vertex_active patch member (Or.inr
      rfl),
      Surface.Cut.VertexGluing.CutPatch.boundary_vertex_active patch member (Or.inl rfl), congrArg OrientedEdge.finish
        same, congrArg OrientedEdge.start same,
      (congrArg value reversed).symm.trans
        (potential.supported_increment (fun edge => anti (Surface.Sewing.VertexSewing.OrientedEdge.map
          patch.vertexLabels edge)) (Or.inr (by
          rw [OrientedEdge.reverse_reverse]; exact member)))⟩

/-- A supported path's value telescopes to the difference of its lifted endpoint potentials.

The cached cut potential agrees at active vertices with the same projected label, so every consecutive lifted step joins
consistently. -/
private theorem path_value_of_descent (patch : Surface.Cut.Patch.CutPatch faces indices boundary)
    (value : OrientedEdge vertexCount → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (potential : Topology.Surface.Boundary.BoundaryPotential patch.boundary (fun edge => value
      (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels edge)))
    (descends : ∀ first last, Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch first →
      Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch last →
      patch.vertexLabels first = patch.vertexLabels last → potential.values first = potential.values last)
    {edges : List (OrientedEdge vertexCount)} {start finish : Fin vertexCount}
    (path : Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish)
    (supported : Surface.Cut.JumpPaths.CutPath.Supported (patch.boundary.map
      (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels)) edges)
    (first last : Fin patch.count) (firstActive : Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch first)
      (lastActive : Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch last)
    (firstLabel : patch.vertexLabels first = start) (lastLabel : patch.vertexLabels last = finish) :
    Surface.Sewing.SewingRetraction.wordValue value edges = potential.values last - potential.values first := by
  induction path generalizing first with
  | nil =>
      have same := descends first last firstActive lastActive (firstLabel.trans lastLabel.symm)
      rw [same, sub_self]
      rfl
  | @cons edge rest finish tail ih =>
      obtain ⟨left, right, leftActive, rightActive, leftLabel, rightLabel, increment⟩ :=
        lifted_step patch value anti potential (supported edge List.mem_cons_self)
      have same := descends first left firstActive leftActive (firstLabel.trans leftLabel.symm)
      rw [Surface.Sewing.SewingRetraction.wordValue, increment, ih (fun next member => supported next
        (List.mem_cons_of_mem _ member)) right rightActive rightLabel lastLabel, same]
      ring1

/-- Every supported closed path has value zero when the cut potential descends through its labels.

The proof uses finite telescoping and the actual supported boundary path. -/
theorem closed_value_of_descent (patch : Surface.Cut.Patch.CutPatch faces indices boundary)
    (value : OrientedEdge vertexCount → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (potential : Topology.Surface.Boundary.BoundaryPotential patch.boundary (fun edge => value
      (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels edge)))
    (descends : ∀ first last, Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch first →
      Surface.Cut.VertexGluing.CutPatch.ActiveVertex patch last →
      patch.vertexLabels first = patch.vertexLabels last → potential.values first = potential.values last)
    {edges : List (OrientedEdge vertexCount)} {anchor : Fin vertexCount}
    (closed : Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (supported : Surface.Cut.JumpPaths.CutPath.Supported (patch.boundary.map
      (Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels)) edges) :
      Surface.Sewing.SewingRetraction.wordValue value edges = 0 := by
  cases closed with
  | nil => rfl
  | @cons edge rest finish tail =>
      obtain ⟨first, _, firstActive, _, firstLabel, _, _⟩ :=
        lifted_step patch value anti potential (supported edge List.mem_cons_self)
      exact (path_value_of_descent patch value anti potential descends (.cons tail) supported
        first first firstActive firstActive firstLabel firstLabel).trans (sub_self _)

end CutPatch

namespace SewingForest.SinglePolygon

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {forest : Topology.Surface.Sewing.SewingForest faces}

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
/-- Vanishing cut-chord and physical-edge values force every supported closed boundary word to vanish.

The single-polygon sewing has unique nonloop edge occurrences and the retained vertex connectivity. Those conditions
make the cached boundary potential descend through exactly the recorded vertex identifications. -/
theorem closed_value_zero (polygon : Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest)
    (unique : (triangleEdgeOccurrences faces).Nodup)
    (nonloop : ∀ edge ∈ triangleEdgeOccurrences faces, edge.start ≠ edge.finish)
    (connected : Mesh.CornerWalks.VertexConnection faces)
    (pairing : Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels
      polygon.patch.cut.boundary)
    (value : OrientedEdge vertexCount → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (physical : ∀ edge ∈ pairing.boundary, value (Surface.Sewing.VertexSewing.OrientedEdge.map
      polygon.patch.cut.vertexLabels edge) = 0)
    (chords : Periods.CutPeriodCompleteness.ProjectedEdgePairing.ChordsZero pairing value)
    {edges : List (OrientedEdge vertexCount)} {anchor : Fin vertexCount}
    (closed : Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (supported : Surface.Cut.JumpPaths.CutPath.Supported polygon.patch.boundary edges) :
      Surface.Sewing.SewingRetraction.wordValue value edges = 0 := by
  let potential := Topology.Surface.Boundary.BoundaryPotential.build (fun edge => value
    (Surface.Sewing.VertexSewing.OrientedEdge.map polygon.patch.cut.vertexLabels edge))
    polygon.patch.cut.closed polygon.patch.cut.simple
      (Periods.CutPeriodCompleteness.ProjectedEdgePairing.boundary_value_zero pairing value anti physical)
  have cutUnique : (polygon.patch.cut.boundary.map (Surface.Sewing.VertexSewing.OrientedEdge.map
    polygon.patch.cut.vertexLabels)).Nodup := by
    rw [polygon.patch.cut.boundary_eq]
    exact Surface.Cut.BoundaryPairs.SewnPatch.boundary_unique polygon.patch
      (Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.originalEdges_unique polygon unique)
  have matchedPairs := Periods.CutPeriodCompleteness.ProjectedEdgePairing.potential_pair_eq pairing cutUnique value anti
    polygon.patch.cut.closed potential chords
  apply Periods.CutPeriodCompleteness.CutPatch.closed_value_of_descent polygon.patch.cut value anti potential ?_ closed
    ?_
  · intro first last firstActive lastActive same
    exact Periods.CutPeriodCompleteness.PairVertexJoin.values_eq potential.values matchedPairs
      ((Surface.Cut.VertexGluing.SewingForest.SinglePolygon.vertexJoin_iff polygon unique nonloop connected pairing
        firstActive lastActive).mpr same)
  · rw [polygon.patch.cut.boundary_eq]
    exact supported

end SewingForest.SinglePolygon
end Purelib.Riemann.Periods.CutPeriodCompleteness

end
