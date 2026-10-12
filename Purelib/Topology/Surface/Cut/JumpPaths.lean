module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

public section

/-!
# Closed mesh words recording the actual cut-primitive jumps

Two prefixes of the retained cyclic cut boundary give a path between the
two cut occurrences of a surface vertex. Its projection is closed, and the
sum of its cut-primitive increments is exactly the endpoint jump. Both words
are cached. No abstract homology label is substituted for the actual word.
-/

namespace Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Topology.Surface.Sewing.SewingProjection (pathEndpoints_map)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)

namespace BoundarySplit

variable {count : Nat} {boundary : List (Stokes.OrientedEdge count)}

set_option genInjectivity false in
/-- A selected boundary occurrence whose edge is the requested original edge.

The retained split fixes the actual selected occurrence and its surrounding prefix and suffix. Its edge equality
identifies that occurrence with the requested bounded edge. -/
structure Selected (boundary : List (Stokes.OrientedEdge count)) (edge : Stokes.OrientedEdge count) where
  /-- Original boundary split retaining the selected edge occurrence and its context. -/ split :
    PolygonStokes.BoundarySplit boundary
  /-- The selected occurrence is the requested original edge. -/ edge_eq : split.edge = edge

constructive_injectivity Selected

open Purelib.Topology.Surface.Cut.JumpPaths in
/-- Total lookup of an occurrence already proved to belong to this finite list. On a simple cut boundary its directed
edge occurs only once.

The scan tests each retained occurrence in order. A failed equality transports its membership witness to the original
tail without changing the selected edge or prefix cache. -/
@[expose] def select (edge : Stokes.OrientedEdge count) : (boundary : List (Stokes.OrientedEdge count)) →
    edge ∈ boundary → BoundarySplit.Selected boundary edge
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member =>
      if same : first = edge then ⟨⟨[], first, rest, rfl⟩, same⟩
      else
        let tail := Purelib.Topology.Surface.Cut.JumpPaths.BoundarySplit.select edge rest ((Membership.mem_cons.mp
          member).resolve_left (Ne.symm same))
        ⟨⟨first :: tail.split.before, tail.split.edge, tail.split.after,
            congrArg (List.cons first) tail.split.equation⟩, tail.edge_eq⟩

/-- The selected prefix runs from the boundary anchor to the selected edge's start. -/
theorem before_path (split : PolygonStokes.BoundarySplit boundary) {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish split.before anchor split.edge.start := by
  rw [split.equation] at closed
  obtain ⟨middle, before, after⟩ := PathEndpoints.split_append split.before (split.edge :: split.after) closed
  cases after with
  | cons tail => exact before

open Purelib.Topology.Surface.Cut.JumpPaths in
/-- The selected prefix followed by its edge runs to that edge's finish. -/
theorem through_path (split : PolygonStokes.BoundarySplit boundary) {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (split.before ++ [split.edge]) anchor
      split.edge.finish :=
  PathEndpoints.append (BoundarySplit.before_path split closed) (.cons (.nil _))

/-- Every edge of the selected prefix belongs to the original boundary.

The defining split equation places the retained prefix before the selected occurrence. Concatenation membership carries
every prefix occurrence into that same original boundary. -/
theorem before_mem (split : PolygonStokes.BoundarySplit boundary) {edge : Stokes.OrientedEdge count}
    (member : edge ∈ split.before) : edge ∈ boundary := by
  rw [split.equation]
  exact Membership.mem_append.mpr (Or.inl member)

end BoundarySplit

namespace CutPath

/-- Reverse the order and orientation of every cut-path edge. -/
@[expose] def reverse {count : Nat} (edges : List (Stokes.OrientedEdge count)) : List (Stokes.OrientedEdge count) :=
  edges.reverse.map OrientedEdge.reverse

open Purelib.Topology.Surface.Cut.JumpPaths in
/-- Reversing a cut path interchanges its certified endpoints.

Reversing the retained ordered edge list reverses each edge orientation. Structural induction composes the reversed tail
with the reversed head while preserving the original bounded endpoints. -/
theorem reverse_endpoints {count : Nat} {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (CutPath.reverse edges) finish start := by
  induction path with
  | nil => exact .nil _
  | @cons edge rest finish tail ih =>
      simp only [CutPath.reverse, Reverse.reverse_cons, Map.map_append, List.map_cons, List.map_nil]
      exact PathEndpoints.append ih (.cons (.nil _))

/-- Sum the primitive endpoint differences along an ordered cut-edge list. -/
@[expose] def increment {count : Nat} (primitive : Fin count → Stokes.PrimitivePoint) : List (Stokes.OrientedEdge count)
  → Stokes.PrimitivePoint
  | [] => PrimitivePoint.zero
  | edge :: rest => (PrimitivePoint.sub (primitive edge.finish) (primitive edge.start)).add
    (Purelib.Topology.Surface.Cut.JumpPaths.CutPath.increment primitive rest)

open Purelib.Topology.Surface.Cut.JumpPaths in
/-- This is finite telescoping on the cut bank. Applying it on the projected closed word instead would incorrectly force
the jump to vanish. -/
theorem increment_eq {count : Nat} (primitive : Fin count → Stokes.PrimitivePoint)
    {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    CutPath.increment primitive edges = PrimitivePoint.sub (primitive finish) (primitive start) := by
  induction path with
  | nil index =>
      change PrimitivePoint.mk 0 0 = PrimitivePoint.mk _ _
      congr 1 <;> ring1
  | @cons edge rest finish tail ih =>
      rw [CutPath.increment, ih]
      change PrimitivePoint.mk _ _ = PrimitivePoint.mk _ _
      congr 1 <;> dsimp only [PrimitivePoint.sub] <;> ring1

/-- A path may traverse an actual mesh edge in either orientation. -/
@[expose] def Supported {count : Nat} (ambient path : List (Stokes.OrientedEdge count)) : Prop :=
  ∀ edge ∈ path, edge ∈ ambient ∨ edge.reverse ∈ ambient

section
open Purelib.Topology.Surface.Cut.JumpPaths
/-- Concatenating two supported edge lists preserves support in the same ambient list.

Each concatenated occurrence comes from one of the two retained lists. Its original support witness gives one of the
same two orientations in the unchanged ambient edge list. -/
theorem supported_append {count : Nat} {ambient first second : List (Stokes.OrientedEdge count)}
    (left : CutPath.Supported ambient first) (right : CutPath.Supported ambient second) : CutPath.Supported ambient
      (first ++ second) := by
  intro edge member
  rcases Membership.mem_append.mp member with firstMember | secondMember
  · exact left edge firstMember
  · exact right edge secondMember

/-- Reversing edge order and orientations preserves unoriented ambient support.

Membership in the reversed mapped list identifies its original edge occurrence. The original support witness then
determines the reversed orientation using edge reversal twice. -/
theorem supported_reverse {count : Nat} {ambient path : List (Stokes.OrientedEdge count)}
    (supported : CutPath.Supported ambient path) : CutPath.Supported ambient (CutPath.reverse path) := by
  intro edge member
  obtain ⟨original, originalMember, equal⟩ := Map.mem_map.mp member
  cases equal
  rcases supported original ((Reverse.mem_reverse _).mp originalMember) with forward | backward
  · exact Or.inr (by rw [OrientedEdge.reverse_reverse]; exact forward)
  · exact Or.inl backward

/-- Projecting both an edge list and its ambient list preserves support. -/
theorem supported_map {source target : Nat} (labels : Fin source → Fin target)
    {ambient path : List (Stokes.OrientedEdge source)} (supported : CutPath.Supported ambient path) :
    CutPath.Supported (ambient.map (OrientedEdge.map labels)) (path.map (OrientedEdge.map labels)) := by
  intro edge member
  obtain ⟨original, originalMember, equal⟩ := Map.mem_map.mp member
  cases equal
  rcases supported original originalMember with forward | backward
  · exact Or.inl (Map.mem_map_of_mem forward)
  · exact Or.inr (Map.mem_map_of_mem (f := OrientedEdge.map labels) backward)

/-- Enlarge the ambient list of a supported cut path. -/
theorem supported_mono {count : Nat} {first last path : List (Stokes.OrientedEdge count)}
    (supported : CutPath.Supported first path) (subset : ∀ edge ∈ first, edge ∈ last) : CutPath.Supported last path :=
      by
  intro edge member
  rcases supported edge member with forward | backward
  · exact Or.inl (subset edge forward)
  · exact Or.inr (subset edge.reverse backward)

end

set_option genInjectivity false in
/-- The original cut word and its surface projection are separate cached lists, with an exact endpoint path in the cut
bank.

The original cut-bank endpoints index the retained path certificate. The surface list is the cached ordered projection
of that same cut-edge list, with an equality recording the readback. -/
structure Projected {source target : Nat} (labels : Fin source → Fin target) (start finish : Fin source) where
  /-- Cached ordered path in the original cut-vertex bank. -/ cutEdges : List (Stokes.OrientedEdge source)
  /-- Cached projection of that exact cut-edge path. -/ surfaceEdges : List (Stokes.OrientedEdge target)
  /-- The surface-edge list is the ordered projection of the retained cut edges. -/ projection_eq : surfaceEdges =
    cutEdges.map (OrientedEdge.map labels)
  /-- Certified original start and finish of the retained cut path. -/ endpoints : PathBoundary.PathEndpoints
    OrientedEdge.start OrientedEdge.finish cutEdges start finish

constructive_injectivity Projected

namespace Projected

variable {source target : Nat} {labels : Fin source → Fin target} {start finish : Fin source}

open Purelib.Topology.Surface.Cut.JumpPaths
/-- Cache the original cut-edge list and its exact projection with retained endpoints. -/
@[expose] def build (labels : Fin source → Fin target) (cutEdges : List (Stokes.OrientedEdge source))
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cutEdges start finish) : CutPath.Projected
      labels start finish :=
  ⟨cutEdges, cutEdges.map (OrientedEdge.map labels), rfl, path⟩

/-- Equal projected endpoint labels make the retained projected path closed. -/
theorem closed (path : CutPath.Projected labels start finish) (same : labels finish = labels start) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish path.surfaceEdges (labels start) (labels start) :=
      by
  rw [path.projection_eq]
  exact (SewingProjection.pathEndpoints_map labels path.endpoints).castFinish same

/-- A closed retained projection has zero integer boundary at each surface vertex. -/
theorem boundary_zero (path : CutPath.Projected labels start finish) (same : labels finish = labels start) (vertex : Fin
  target) :
    PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish path.surfaceEdges vertex = 0 := by
  rw [PathBoundary.wordBoundaryAt_eq_endpoints (path.closed same)]
  ring1

end Projected
end CutPath

set_option genInjectivity false in
open Purelib.Topology.Surface.Cut.JumpPaths in
/-- Actual prefix paths for both endpoint jumps of one paired cut. Their word equations preserve the selected traversal,
rather than merely recording the existence of some path between the same vertices.

Both selected original occurrences and both derived cut paths remain cached separately. The two equations fix their
exact prefix traversal and preserve the corresponding source and target vertices. -/
structure CutJumpPaths {source target : Nat} (labels : Fin source → Fin target)
    (boundary : List (Stokes.OrientedEdge source)) (pair : ProjectedEdgePairs.ProjectedEdgePair labels) where
  /-- Retained occurrence of the pair's first edge in the original boundary. -/ first : BoundarySplit.Selected boundary
    pair.first
  /-- Retained occurrence of the pair's second edge in the original boundary. -/ second : BoundarySplit.Selected
    boundary pair.second
  /-- Cached path from the first edge's start to the second edge's finish. -/ start : CutPath.Projected labels
    pair.first.start pair.second.finish
  /-- The start path is the reversed first prefix followed by the second prefix and edge. -/ start_eq : start.cutEdges =
    CutPath.reverse first.split.before ++ second.split.before ++ [pair.second]
  /-- Cached path from the first edge's finish to the second edge's start. -/ finish : CutPath.Projected labels
    pair.first.finish pair.second.start
  /-- The finish path reverses the first prefix and edge, then follows the second prefix. -/ finish_eq : finish.cutEdges
    = CutPath.reverse (first.split.before ++ [pair.first]) ++ second.split.before

constructive_injectivity CutJumpPaths

namespace CutJumpPaths

variable {source target : Nat} {labels : Fin source → Fin target}
  {boundary : List (Stokes.OrientedEdge source)} {pair : ProjectedEdgePairs.ProjectedEdgePair labels}

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.JumpPaths in
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath in
/-- Select both original edge occurrences and cache their two endpoint-jump paths.

The closed cut boundary supplies prefixes from the common anchor; reversing and concatenating those prefixes gives the
specified cut endpoints. -/
@[expose] def build (labels : Fin source → Fin target) (boundary : List (Stokes.OrientedEdge source))
    {anchor : Fin source} (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor
      anchor)
    (pair : ProjectedEdgePairs.ProjectedEdgePair labels) (firstMember : pair.first ∈ boundary) (secondMember :
      pair.second ∈ boundary) :
    JumpPaths.CutJumpPaths labels boundary pair :=
  let first := BoundarySplit.select pair.first boundary firstMember
  let second := BoundarySplit.select pair.second boundary secondMember
  have firstBefore : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish first.split.before anchor
    pair.first.start :=
    (BoundarySplit.before_path first.split closed).castFinish (congrArg OrientedEdge.start first.edge_eq)
  have firstThrough : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (first.split.before ++
    [pair.first]) anchor pair.first.finish :=
    PathEndpoints.append firstBefore (.cons (.nil _))
  have secondBefore : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish second.split.before anchor
    pair.second.start :=
    (BoundarySplit.before_path second.split closed).castFinish (congrArg OrientedEdge.start second.edge_eq)
  have secondThrough : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (second.split.before ++
    [pair.second]) anchor pair.second.finish :=
    PathEndpoints.append secondBefore (.cons (.nil _))
  { first := first
    second := second
    start := Projected.build labels _ (PathEndpoints.append (CutPath.reverse_endpoints firstBefore) secondThrough)
    start_eq := Append.append_assoc _ _ _ |>.symm
    finish := Projected.build labels _ (PathEndpoints.append (CutPath.reverse_endpoints firstThrough) secondBefore)
    finish_eq := rfl }

section
open Purelib.Topology.Surface.Cut
/-- The start-jump path closes after projection because the paired edges project oppositely. -/
theorem start_closed (paths : JumpPaths.CutJumpPaths labels boundary pair) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish paths.start.surfaceEdges
      (labels pair.first.start) (labels pair.first.start) :=
  paths.start.closed (congrArg OrientedEdge.finish pair.opposite)

/-- The finish-jump path closes after projection because the paired edges project oppositely. -/
theorem finish_closed (paths : JumpPaths.CutJumpPaths labels boundary pair) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish paths.finish.surfaceEdges
      (labels pair.first.finish) (labels pair.first.finish) :=
  paths.finish.closed (congrArg OrientedEdge.start pair.opposite)

end

section
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.JumpPaths
/-- The start-jump path sums to the difference between the paired start-aligned primitive values. -/
theorem start_increment (paths : JumpPaths.CutJumpPaths labels boundary pair) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    CutPath.increment primitive paths.start.cutEdges = PrimitivePoint.sub (primitive pair.second.finish) (primitive
      pair.first.start) :=
  CutPath.increment_eq primitive paths.start.endpoints

/-- The finish-jump path sums to the difference between the paired finish-aligned primitive values. -/
theorem finish_increment (paths : JumpPaths.CutJumpPaths labels boundary pair) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    CutPath.increment primitive paths.finish.cutEdges = PrimitivePoint.sub (primitive pair.second.start) (primitive
      pair.first.finish) :=
  CutPath.increment_eq primitive paths.finish.endpoints

/-- The retained start-jump path reads the corresponding cached primitive sample jump. -/
theorem sample_startJump {primitive : Fin source → Stokes.PrimitivePoint}
    (sample : ProjectedEdgePair.Sample (labels := labels) primitive)
    (paths : JumpPaths.CutJumpPaths labels boundary sample.pair) :
    CutPath.increment primitive paths.start.cutEdges = sample.startJump :=
  (paths.start_increment primitive).trans sample.startJump_eq.symm

/-- The retained finish-jump path reads the corresponding cached primitive sample jump. -/
theorem sample_finishJump {primitive : Fin source → Stokes.PrimitivePoint}
    (sample : ProjectedEdgePair.Sample (labels := labels) primitive)
    (paths : JumpPaths.CutJumpPaths labels boundary sample.pair) :
    CutPath.increment primitive paths.finish.cutEdges = sample.finishJump :=
  (paths.finish_increment primitive).trans sample.finishJump_eq.symm

end

section
open Purelib.Topology.Surface.Cut.JumpPaths
/-- The selected boundary prefix projects into the original projected boundary support. -/
private theorem prefix_supported {edge : Stokes.OrientedEdge source} (selected : BoundarySplit.Selected boundary edge) :
    CutPath.Supported boundary selected.split.before :=
  fun _ member => Or.inl (BoundarySplit.before_mem selected.split member)

/-- The selected prefix and edge project into the original projected boundary support.

The prefix support certificate and the selected edge occurrence give support for their retained concatenation. Both
parts refer to the same original boundary and selected split. -/
private theorem through_supported {edge : Stokes.OrientedEdge source} (selected : BoundarySplit.Selected boundary edge)
  :
    CutPath.Supported boundary (selected.split.before ++ [edge]) :=
  CutPath.supported_append (CutJumpPaths.prefix_supported selected) (by
    intro next member
    rcases Membership.mem_cons.mp member with same | member
    · cases same
      exact Or.inl (selected.edge_eq ▸ selected.split.edge_mem)
    · exact (List.not_mem_nil member).elim)

end

open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.JumpPaths
/-- The projected start-jump path is supported in the projected original boundary.

The cached start path consists of the reversed first prefix and the second prefix through its selected edge. Support
transports those retained occurrences through their exact projected edge list. -/
theorem start_supported (paths : JumpPaths.CutJumpPaths labels boundary pair) :
    CutPath.Supported (boundary.map (OrientedEdge.map labels)) paths.start.surfaceEdges := by
  rw [paths.start.projection_eq]
  apply CutPath.supported_map
  rw [paths.start_eq, Append.append_assoc]
  exact CutPath.supported_append (CutPath.supported_reverse (CutJumpPaths.prefix_supported paths.first))
    (CutJumpPaths.through_supported paths.second)

/-- The projected finish-jump path is supported in the projected original boundary.

The cached finish path reverses the first prefix through its selected edge and appends the second prefix. Both retained
paths project into the same original boundary support. -/
theorem finish_supported (paths : JumpPaths.CutJumpPaths labels boundary pair) :
    CutPath.Supported (boundary.map (OrientedEdge.map labels)) paths.finish.surfaceEdges := by
  rw [paths.finish.projection_eq]
  apply CutPath.supported_map
  rw [paths.finish_eq]
  exact CutPath.supported_append (CutPath.supported_reverse (CutJumpPaths.through_supported paths.first))
    (CutJumpPaths.prefix_supported paths.second)

end CutJumpPaths

end Purelib.Topology.Surface.Cut.JumpPaths
