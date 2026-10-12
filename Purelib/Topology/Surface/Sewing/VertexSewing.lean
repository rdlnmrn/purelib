module
import Purelib.Data.Nat.Subtraction

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Explicit endpoint-only vertex sewing

The two vertex banks are disjoint before the displayed seam endpoints are
identified.  Original surface labels play no role in deciding equality.
Two unused slots are permitted in the resulting bank; no quotient, search,
or choice-derived enumeration is needed.
-/

namespace Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Nat

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle pairedEdgeOccurrences)

namespace OrientedEdge

/-- Decide equality of finite oriented edges by comparing both retained endpoints. -/
instance {count : Nat} : DecidableEq (Stokes.OrientedEdge count) := fun first second =>
  if starts : first.start = second.start then
    if finishes : first.finish = second.finish then .isTrue (by
      cases first
      cases second
      cases starts
      cases finishes
      rfl)
    else .isFalse (fun equal => finishes (congrArg OrientedEdge.finish equal))
  else .isFalse (fun equal => starts (congrArg OrientedEdge.start equal))

/-- Map both endpoints of an oriented edge through a vertex map. -/
@[expose] def map {source target : Nat} (vertex : Fin source → Fin target) (edge : Stokes.OrientedEdge source) :
  Stokes.OrientedEdge target :=
  ⟨vertex edge.start, vertex edge.finish⟩

/-- Mapping endpoints commutes with reversing an edge. -/
theorem map_reverse {source target : Nat} (vertex : Fin source → Fin target) (edge : Stokes.OrientedEdge source) :
    OrientedEdge.map vertex edge.reverse = (OrientedEdge.map vertex edge).reverse := rfl

/-- Consecutive vertex maps act by their composite on an oriented edge. -/
theorem map_comp {first second third : Nat} (left : Fin first → Fin second) (right : Fin second → Fin third)
    (edge : Stokes.OrientedEdge first) : OrientedEdge.map right (OrientedEdge.map left edge) =
      OrientedEdge.map (fun index => right (left index)) edge := rfl

end OrientedEdge

namespace OrientedTriangle

/-- Map the three ordered vertices of an oriented triangle. -/
@[expose] def map {source target : Nat} (vertex : Fin source → Fin target) (triangle : Stokes.OrientedTriangle source) :
  Stokes.OrientedTriangle target :=
  ⟨vertex triangle.first, vertex triangle.second, vertex triangle.third⟩

/-- Mapping a triangle maps its oriented boundary edge list. -/
theorem boundary_map {source target : Nat} (vertex : Fin source → Fin target) (triangle : Stokes.OrientedTriangle
  source) :
    (OrientedTriangle.map vertex triangle).boundary =
      triangle.boundary.map (VertexSewing.OrientedEdge.map vertex) := rfl

end OrientedTriangle

/-- Transport an occurrence-preserving edge reordering through a vertex map. -/
theorem EdgeReordering.map {source target : Nat} (vertex : Fin source → Fin target)
    {left right : List (Stokes.OrientedEdge source)} (ordering : Stokes.EdgeReordering left right) :
    Stokes.EdgeReordering (left.map (VertexSewing.OrientedEdge.map vertex)) (right.map (VertexSewing.OrientedEdge.map
      vertex)) := by
  induction ordering with
  | nil => exact .nil
  | cons edge tail ih => exact .cons (VertexSewing.OrientedEdge.map vertex edge) ih
  | swap first second tail => exact .swap _ _ _
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Mapping vertices preserves the retained forward-and-reverse occurrence pairs. -/
theorem pairedEdgeOccurrences_map {source target : Nat} (vertex : Fin source → Fin target) :
    (edges : List (Stokes.OrientedEdge source)) →
      (Stokes.pairedEdgeOccurrences edges).map (VertexSewing.OrientedEdge.map vertex) = Stokes.pairedEdgeOccurrences
        (edges.map (VertexSewing.OrientedEdge.map vertex))
  | [] => rfl
  | edge :: edges => congrArg (List.cons (VertexSewing.OrientedEdge.map vertex edge))
      (congrArg (List.cons (VertexSewing.OrientedEdge.map vertex edge).reverse)
        (Purelib.Topology.Surface.Sewing.VertexSewing.pairedEdgeOccurrences_map vertex edges))

namespace EndpointGluing

variable {firstCount secondCount : Nat}

/-- Embed the original left vertex bank into the disjoint combined bank. -/
@[expose] def left (index : Fin firstCount) : Fin (firstCount + secondCount) := ⟨index.val, by omega⟩

section
open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing
/-- Embed the right vertex bank while identifying the two displayed seam endpoints oppositely.

Every other right vertex retains its own offset slot in the combined finite bank. -/
@[expose] def right (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount)
    (index : Fin secondCount) : Fin (firstCount + secondCount) :=
  if index = second.start then left first.finish
  else if index = second.finish then left first.start
  else ⟨firstCount + index.val, by omega⟩

/-- The original left vertex embedding is injective. -/
theorem left_injective : Function.Injective (@left firstCount secondCount) := by
  intro first second equal
  have values := congrArg Fin.val equal
  exact Fin.ext values

/-- The right seam start maps to the retained left seam finish. -/
theorem right_start (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount) :
    right first second second.start = left first.finish := by rw [right, if_pos rfl]

/-- A nondegenerate right seam finish maps to the retained left seam start. -/
theorem right_finish (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount)
    (distinct : second.start ≠ second.finish) : right first second second.finish = left first.start := by
  rw [right, if_neg (Ne.symm distinct), if_pos rfl]

/-- The only cross-bank coincidences are the two explicitly sewn endpoints. -/
theorem left_eq_right_iff (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount)
    (distinct : second.start ≠ second.finish) (i : Fin firstCount) (j : Fin secondCount) :
    left i = right first second j ↔ (i = first.finish ∧ j = second.start) ∨ (i = first.start ∧ j = second.finish) := by
  by_cases atStart : j = second.start
  · subst j
    rw [EndpointGluing.right_start]
    constructor
    · intro equal; exact Or.inl ⟨left_injective equal, rfl⟩
    · intro matched
      rcases matched with matched | matched
      · exact congrArg left matched.1
      · exact (distinct matched.2).elim
  · by_cases atFinish : j = second.finish
    · subst j
      rw [EndpointGluing.right_finish first second distinct]
      constructor
      · intro equal; exact Or.inr ⟨left_injective equal, rfl⟩
      · intro matched
        rcases matched with matched | matched
        · exact (distinct matched.2.symm).elim
        · exact congrArg left matched.1
    · simp only [right, if_neg atStart, if_neg atFinish]
      constructor
      · intro equal
        have values := congrArg Fin.val equal
        change i.val = firstCount + j.val at values
        omega
      · intro matched
        rcases matched with matched | matched
        · exact (atStart matched.2).elim
        · exact (atFinish matched.2).elim

/-- The right embedding is injective when both displayed seams have distinct endpoints. -/
theorem right_injective (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount)
    (firstDistinct : first.start ≠ first.finish) (secondDistinct : second.start ≠ second.finish) :
    Function.Injective (right first second) := by
  intro i j equal
  by_cases iStart : i = second.start
  · subst i
    rw [EndpointGluing.right_start] at equal
    rcases (left_eq_right_iff first second secondDistinct _ j).mp equal with matched | matched
    · exact matched.2.symm
    · exact (firstDistinct matched.1.symm).elim
  · by_cases iFinish : i = second.finish
    · subst i
      rw [EndpointGluing.right_finish first second secondDistinct] at equal
      rcases (left_eq_right_iff first second secondDistinct _ j).mp equal with matched | matched
      · exact (firstDistinct matched.1).elim
      · exact matched.2.symm
    · by_cases jStart : j = second.start
      · subst j
        rw [EndpointGluing.right_start] at equal
        rcases (left_eq_right_iff first second secondDistinct _ i).mp equal.symm with matched | matched
        · exact (iStart matched.2).elim
        · exact (iFinish matched.2).elim
      · by_cases jFinish : j = second.finish
        · subst j
          rw [EndpointGluing.right_finish first second secondDistinct] at equal
          rcases (left_eq_right_iff first second secondDistinct _ i).mp equal.symm with matched | matched
          · exact (iStart matched.2).elim
          · exact (iFinish matched.2).elim
        · simp only [right, if_neg iStart, if_neg iFinish, if_neg jStart, if_neg jFinish] at equal
          apply Fin.ext
          have values := congrArg Fin.val equal
          change firstCount + i.val = firstCount + j.val at values
          omega

/-- The two embedded seam edges have opposite orientations. -/
theorem opposite (first : Stokes.OrientedEdge firstCount) (second : Stokes.OrientedEdge secondCount)
    (distinct : second.start ≠ second.finish) :
    VertexSewing.OrientedEdge.map (right first second) second = (VertexSewing.OrientedEdge.map left first).reverse := by
  change OrientedEdge.mk (right first second second.start) (right first second second.finish) = _
  rw [EndpointGluing.right_start, EndpointGluing.right_finish first second distinct]
  rfl

end

/-- Read original surface labels from either part of the combined vertex bank. -/
@[expose] def project {baseCount : Nat} (first : Fin firstCount → Fin baseCount) (second : Fin secondCount → Fin
  baseCount)
    (index : Fin (firstCount + secondCount)) : Fin baseCount :=
  if inside : index.val < firstCount then first ⟨index.val, inside⟩
  else second ⟨index.val - firstCount, by omega⟩

open Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing
/-- Projecting an embedded left vertex recovers its label.

The retained left bound selects the left branch of the combined bank.
The same bounded coordinate is then passed to the supplied projection. -/
theorem project_left {baseCount : Nat} (first : Fin firstCount → Fin baseCount) (second : Fin secondCount → Fin
  baseCount)
    (index : Fin firstCount) : EndpointGluing.project first second (left index) = first index := by
  rw [EndpointGluing.project, left, dif_pos index.isLt]

/-- Oppositely matched seam labels make right embedding preserve projection.

The two displayed seam endpoints use their retained matching equations.
Every other vertex keeps its offset slot and original projected label. -/
theorem project_right {baseCount : Nat} (first : Fin firstCount → Fin baseCount) (second : Fin secondCount → Fin
  baseCount)
    (firstEdge : Stokes.OrientedEdge firstCount) (secondEdge : Stokes.OrientedEdge secondCount)
    (matched : VertexSewing.OrientedEdge.map second secondEdge = (VertexSewing.OrientedEdge.map first
      firstEdge).reverse)
    (index : Fin secondCount) :
    EndpointGluing.project first second (right firstEdge secondEdge index) = second index := by
  by_cases atStart : index = secondEdge.start
  · subst index
    rw [EndpointGluing.right_start, EndpointGluing.project_left]
    exact (congrArg OrientedEdge.start matched).symm
  · by_cases atFinish : index = secondEdge.finish
    · simp only [right, if_neg atStart, if_pos atFinish, EndpointGluing.project_left]
      subst index
      exact (congrArg OrientedEdge.finish matched).symm
    · simp only [right, if_neg atStart, if_neg atFinish, EndpointGluing.project,
        dif_neg (show ¬firstCount + index.val < firstCount by omega)]
      congr 1
      apply Fin.ext
      exact Subtraction.add_sub_cancel_left firstCount index.val

end EndpointGluing

end Purelib.Topology.Surface.Sewing.VertexSewing
