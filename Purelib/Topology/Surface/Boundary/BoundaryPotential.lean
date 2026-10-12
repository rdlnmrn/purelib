module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.PolygonSewing
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership

public section

/-!
# Exact finite potentials on a simple closed boundary

Prefix sums construct a potential whenever the total boundary value is
zero. The resulting vector is cached once, with exact edge increments;
subsequent path telescoping consumes that vector, not repeated prefix sums.
-/

namespace Purelib.Topology.Surface.Boundary

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Chain
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)

namespace BoundaryPotential

variable {count : Nat}

/-- Sum edge readings before the first occurrence of the requested source vertex.

The original ordered edge word supplies the finite prefix. Its first matching
source stops the accumulation, and an absent source retains the full word total. -/
@[expose]
def prefixValue (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) : List (Stokes.OrientedEdge count) → Fin
  count → Gaussian.Basic.Canonical
  | [], _ => 0
  | edge :: rest, vertex => if vertex = edge.start then 0 else value edge +
    prefixValue value rest vertex

/-- The prefix value at the exact initial path vertex is zero. -/
private theorem prefix_at_start (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
    {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
      BoundaryPotential.prefixValue value edges start = 0 := by
  cases path
  · rfl
  · exact if_pos rfl

/-- At a source in a simple edge word, the prefix value is the preceding word total.

Distinct source vertices exclude the selected source from the preceding
entries. Structural recursion accumulates exactly that prefix. -/
private theorem prefix_at_split (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
    (before : List (Stokes.OrientedEdge count)) (edge : Stokes.OrientedEdge count) (after : List (Stokes.OrientedEdge
      count))
    (simple : ((before ++ edge :: after).map OrientedEdge.start).Nodup) :
    BoundaryPotential.prefixValue value (before ++ edge :: after) edge.start = SewingRetraction.wordValue value before
      := by
  induction before with
  | nil => exact if_pos rfl
  | cons first rest ih =>
      have parts := List.pairwise_cons.mp simple
      have distinct : edge.start ≠ first.start := Ne.symm (parts.1 edge.start
        (Map.mem_map_of_mem (Membership.mem_append.mpr (Or.inr List.mem_cons_self))))
      change (if edge.start = first.start then 0 else value first + BoundaryPotential.prefixValue value (rest ++ edge ::
        after) edge.start) = _
      rw [if_neg distinct, ih parts.2]
      rfl

/-- Prefix values recover each edge reading on a simple closed boundary of total zero.

The split identifies one edge in a simple closed path. Its zero total
reading makes the retained prefix difference equal that edge reading. -/
theorem prefix_increment (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
    {boundary : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor)
    (simple : (boundary.map OrientedEdge.start).Nodup) (zero : SewingRetraction.wordValue value boundary = 0)
    (split : PolygonStokes.BoundarySplit boundary) :
    BoundaryPotential.prefixValue value boundary split.edge.finish - BoundaryPotential.prefixValue value boundary
      split.edge.start = value split.edge := by
  rcases split with ⟨before, edge, after, equation⟩
  cases equation
  change BoundaryPotential.prefixValue value (before ++ edge :: after) edge.finish -
    BoundaryPotential.prefixValue value (before ++ edge :: after) edge.start = value edge
  have atStart := BoundaryPotential.prefix_at_split value before edge after simple
  obtain ⟨middle, _, remaining⟩ := PathEndpoints.split_append before (edge :: after) closed
  cases remaining with
  | cons tail =>
      cases after with
      | nil =>
          have finishEq : edge.finish = anchor := by cases tail; rfl
          rw [finishEq, BoundaryPotential.prefix_at_start value closed, atStart]
          rw [SewingRetraction.wordValue_append, SewingRetraction.wordValue,
            SewingRetraction.wordValue, add_zero] at zero
          exact (congrArg (fun total => total - SewingRetraction.wordValue value before) zero).symm.trans (by ring1)
      | cons next rest =>
          have head_start {start finish : Fin count} (path : PathBoundary.PathEndpoints OrientedEdge.start
            OrientedEdge.finish (next :: rest) start finish) :
              start = next.start := by cases path; rfl
          have atFinish : BoundaryPotential.prefixValue value (before ++ edge :: next :: rest) edge.finish =
            SewingRetraction.wordValue value before + value edge := by
            rw [head_start tail]
            have atNext := BoundaryPotential.prefix_at_split value (before ++ [edge]) next rest
              (by simpa only [Append.append_assoc, List.cons_append, List.nil_append] using simple)
            simpa only [Append.append_assoc, List.cons_append, List.nil_append, SewingRetraction.wordValue_append,
              SewingRetraction.wordValue, add_zero] using atNext
          rw [atFinish, atStart]
          ring1

end BoundaryPotential

set_option genInjectivity false in
/-- Retain a potential vector with exact boundary edge increments.

The original vertex indices address the cached Gaussian values. Each displayed
boundary occurrence has its finish-minus-start reading certificate. -/
structure BoundaryPotential {count : Nat} (boundary : List (Stokes.OrientedEdge count)) (value : Stokes.OrientedEdge
  count → Gaussian.Basic.Canonical) where
  /-- Cached Gaussian rational potential at every original vertex. -/ values : Data.Vector
    Gaussian.Basic.Canonical count
  /-- Every boundary edge reading equals the retained finish potential minus the start potential. -/ increments : ∀ edge
    ∈ boundary, values edge.finish - values edge.start = value edge

constructive_injectivity BoundaryPotential

namespace BoundaryPotential

variable {count : Nat} {boundary : List (Stokes.OrientedEdge count)} {value : Stokes.OrientedEdge count →
  Gaussian.Basic.Canonical}

/-- Cache vertex prefix values for a simple closed boundary with zero total reading.

The result retains exact edge-increment equations; later path evaluations reuse the cached vector. -/
@[expose]
def build (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) {boundary : List (Stokes.OrientedEdge count)}
  {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor)
    (simple : (boundary.map OrientedEdge.start).Nodup) (zero : SewingRetraction.wordValue value boundary = 0) :
      BoundaryPotential boundary value :=
  { values := Data.Vector.Basic.vectorOfFn (BoundaryPotential.prefixValue value boundary)
    increments := fun edge member => by
      rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
      let selected := BoundarySplit.select edge boundary member
      have increment := BoundaryPotential.prefix_increment value closed simple zero selected.split
      rw [selected.edge_eq] at increment
      exact increment }

/-- An antisymmetric reading on either supported orientation equals the cached endpoint difference. -/
theorem supported_increment (potential : BoundaryPotential boundary value) (anti : ∀ edge, value
  edge.reverse = -value edge)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ boundary ∨ edge.reverse ∈ boundary) :
    value edge = potential.values edge.finish - potential.values edge.start := by
  rcases member with forward | backward
  · exact (potential.increments edge forward).symm
  · have increment := potential.increments edge.reverse backward
    rw [anti] at increment
    have negated := congrArg Neg.neg increment
    change -(potential.values edge.start - potential.values edge.finish) = -(-value edge) at negated
    rw [neg_neg] at negated
    exact negated.symm.trans (by ring1)

/-- A supported path reading telescopes to its cached potential difference. -/
theorem path_value (potential : BoundaryPotential boundary value) (anti : ∀ edge, value edge.reverse =
  -value edge)
    {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish)
    (supported : CutPath.Supported boundary edges) : SewingRetraction.wordValue value edges = potential.values finish -
      potential.values start := by
  induction path with
  | nil => change 0 = _ - _; exact (sub_self _).symm
  | @cons edge rest finish tail ih =>
      rw [SewingRetraction.wordValue, potential.supported_increment anti (supported edge List.mem_cons_self),
        ih (fun next member => supported next (List.mem_cons_of_mem _ member))]
      ring1

end BoundaryPotential
end Purelib.Topology.Surface.Boundary
