module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
public import Purelib.Topology.Chain.PathBoundary

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

public section

/-!
# Read a finite state trace on the vertices of a simple boundary

The state at each displayed source is read from its literal prefix. Closure
handles the final endpoint; source uniqueness handles every other endpoint.
The complete lookup table is cached, so later gluing uses exact readback.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryStateReading

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {Alpha : Type} {source target : Nat}

/-- Apply the ordered finite transition list to an initial state. -/
@[expose] def advance (step : Alpha → Fin target → Fin target) : List Alpha → Fin target → Fin target
  | [], current => current
  | entry :: entries, current => Purelib.Topology.Surface.Boundary.BoundaryStateReading.advance step entries (step entry
    current)

/-- Read the transition state at the first occurrence of a boundary source vertex.

If no source matches, the terminal state is returned, so the finite lookup remains total. -/
@[expose] def read (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target) :
    List Alpha → Fin target → Fin source → Fin target
  | [], current, _ => current
  | entry :: entries, current, vertex =>
      if vertex = (edge entry).start then current else Purelib.Topology.Surface.Boundary.BoundaryStateReading.read edge
        step entries (step entry current) vertex

open Purelib.Topology.Surface.Boundary
/-- Advancing through concatenated traces equals advancing through their parts in order. -/
theorem advance_append (step : Alpha → Fin target → Fin target) (first last : List Alpha) (current : Fin target) :
    BoundaryStateReading.advance step (first ++ last) current = BoundaryStateReading.advance step last
      (BoundaryStateReading.advance step first current) := by
  induction first generalizing current with
  | nil => rfl
  | cons entry entries ih => exact ih _

/-- Reading the initial vertex of an exact boundary path returns the initial state. -/
theorem read_start (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target)
    {entries : List Alpha} {first last : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map edge) first last) (current :
      Fin target) :
    BoundaryStateReading.read edge step entries current first = current := by
  cases entries with
  | nil => rfl
  | cons entry entries => cases path; exact if_pos rfl

/-- Reading a source in a simple boundary gives the state after its literal prefix. -/
theorem read_split (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target)
    (before : List Alpha) (entry : Alpha) (after : List Alpha)
    (simple : (((before ++ entry :: after).map edge).map OrientedEdge.start).Nodup) (current : Fin target) :
    BoundaryStateReading.read edge step (before ++ entry :: after) current (edge entry).start =
      BoundaryStateReading.advance step before current := by
  induction before generalizing current with
  | nil => exact if_pos rfl
  | cons head before ih =>
      have parts := List.pairwise_cons.mp simple
      have different : (edge entry).start ≠ (edge head).start := Ne.symm (parts.1 _
        (Map.mem_map_of_mem (Map.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self))))
      rw [List.cons_append, BoundaryStateReading.read, if_neg different]
      exact ih parts.2 _

/-- Reading an edge's finish gives the state immediately after its transition.

The edge trace is closed and has unique sources, and the complete transition trace must return to its initial state. -/
theorem read_finish (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target)
    (before : List Alpha) (entry : Alpha) (after : List Alpha) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish ((before ++ entry :: after).map edge)
      anchor anchor)
    (simple : (((before ++ entry :: after).map edge).map OrientedEdge.start).Nodup) (current : Fin target)
    (returns : BoundaryStateReading.advance step (before ++ entry :: after) current = current) :
    BoundaryStateReading.read edge step (before ++ entry :: after) current (edge entry).finish = step entry
      (BoundaryStateReading.advance step before current) := by
  have path := closed
  rw [Purelib.Data.List.Map.map_append, List.map_cons] at path
  obtain ⟨middle, _, rest⟩ := PathEndpoints.split_append (before.map edge) (edge entry :: after.map edge) path
  cases rest with
  | cons tail =>
      cases after with
      | nil =>
          have finishEq : (edge entry).finish = anchor := by cases tail; rfl
          rw [finishEq, BoundaryStateReading.read_start edge step closed]
          rw [BoundaryStateReading.advance_append] at returns
          exact returns.symm
      | cons next remaining =>
          have head_start {first last : Fin source}
              (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edge next :: remaining.map
                edge) first last) :
              first = (edge next).start := by cases path; rfl
          have nextEq := head_start tail
          rw [nextEq]
          have atNext := BoundaryStateReading.read_split edge step (before ++ [entry]) next remaining
            (by simpa only [Purelib.Data.List.Append.append_assoc, List.cons_append, List.nil_append] using simple)
              current
          simpa only [Purelib.Data.List.Append.append_assoc, List.cons_append, List.nil_append,
            BoundaryStateReading.advance_append, BoundaryStateReading.advance] using atNext

end Purelib.Topology.Surface.Boundary.BoundaryStateReading

namespace Purelib.Topology.Surface.Boundary.BoundaryStateReading

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

set_option genInjectivity false in
open Purelib.Topology.Surface.Boundary in
/-- A table of states indexed by the original cut vertices. The prefix readback ties every edge to the actual, ordered
transition trace. -/
structure PolygonStokes {Alpha : Type} {source target : Nat}
    (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target)
    (entries : List Alpha) (anchor : Fin source) (initial : Fin target) where
  /-- Cached transition state at each original cut vertex. -/ values : Data.Vector (Fin target) source
  /-- The retained anchor state equals the supplied initial state. -/ anchor_eq : values anchor = initial
  /-- Every source state is the transition result of its literal preceding prefix. -/ start_eq : ∀ before entry after,
    entries = before ++ entry :: after →
    values (edge entry).start = BoundaryStateReading.advance step before initial
  /-- Every finish state is the result of applying its transition to the prefix state. -/ finish_eq : ∀ before entry
    after, entries = before ++ entry :: after →
    values (edge entry).finish = step entry (BoundaryStateReading.advance step before initial)

constructive_injectivity PolygonStokes

namespace PolygonStokes

variable {Alpha : Type} {source target : Nat}

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.BoundaryStateReading in
/-- Cache all boundary vertex states from the retained ordered transition trace.

Closure, unique sources, and return of the complete trace certify the anchor and each edge's before-and-after state. -/
@[expose] def build (edge : Alpha → Stokes.OrientedEdge source) (step : Alpha → Fin target → Fin target)
    (entries : List Alpha) (anchor : Fin source) (initial : Fin target)
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map edge) anchor anchor)
    (simple : ((entries.map edge).map OrientedEdge.start).Nodup)
    (returns : BoundaryStateReading.advance step entries initial = initial) : PolygonStokes edge
      step entries anchor initial where
  values := Data.Vector.Basic.vectorOfFn (BoundaryStateReading.read edge step entries initial)
  anchor_eq := (Data.Vector.Basic.vectorOfFn_apply _ anchor).trans (BoundaryStateReading.read_start edge step closed
    initial)
  start_eq := fun before entry after equal => by
    rw [Data.Vector.Basic.vectorOfFn_apply, equal]
    exact BoundaryStateReading.read_split edge step before entry after (equal ▸ simple) initial
  finish_eq := fun before entry after equal => by
    rw [Data.Vector.Basic.vectorOfFn_apply, equal]
    exact BoundaryStateReading.read_finish edge step before entry after (equal ▸ closed) (equal ▸ simple) initial (equal
      ▸ returns)

end PolygonStokes
end Purelib.Topology.Surface.Boundary.BoundaryStateReading

end
