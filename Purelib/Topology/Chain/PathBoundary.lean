module
public import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Topology.BranchedCover.Double.Attachment
import Purelib.Tactic.Ring

open Purelib.Topology.BranchedCover.Double

@[expose] public section

/-!
# Cellular boundary of finite attaching walks

This module turns the explicit face attachments into integral cellular
boundary statements.  Paths are finite inductive objects with exact endpoint
types.  Their vertex boundary telescopes constructively, and every cyclic
hyperelliptic face attachment therefore satisfies `d₁ d₂ = 0` pointwise.
-/

namespace Purelib.Topology.Chain.PathBoundary

/-- A finite edge list with exact initial and final vertices. -/
inductive PathEndpoints {Vertex EdgeLabel : Type}
    (edgeStart edgeFinish : EdgeLabel -> Vertex) :
    List EdgeLabel -> Vertex -> Vertex -> Prop
  /-- The empty edge word starts and finishes at the same vertex. -/ | nil (vertex : Vertex) :
    PathEndpoints edgeStart edgeFinish [] vertex vertex
  /-- Prepend an edge whose finish is the initial vertex of the retained tail. -/ | cons {edge : EdgeLabel} {remaining :
    List EdgeLabel} {finish : Vertex}
      (tail : PathEndpoints edgeStart edgeFinish remaining
        (edgeFinish edge) finish) :
      PathEndpoints edgeStart edgeFinish (edge :: remaining)
        (edgeStart edge) finish

namespace PathEndpoints

open Purelib.Topology.Chain
/-- Transport the initial vertex of an exact path along an equality. -/
theorem castStart {Vertex EdgeLabel : Type}
    {edgeStart edgeFinish : EdgeLabel -> Vertex}
    {edges : List EdgeLabel} {left right finish : Vertex}
    (equal : left = right)
    (path : PathEndpoints edgeStart edgeFinish edges left finish) :
    PathEndpoints edgeStart edgeFinish edges right finish := by
  subst right
  exact path

/-- Transport the final vertex of an exact path along an equality. -/
theorem castFinish {Vertex EdgeLabel : Type}
    {edgeStart edgeFinish : EdgeLabel -> Vertex}
    {edges : List EdgeLabel} {start left right : Vertex}
    (equal : left = right)
    (path : PathEndpoints edgeStart edgeFinish edges start left) :
    PathEndpoints edgeStart edgeFinish edges start right := by
  subst right
  exact path

end PathEndpoints

open Purelib.Topology.Chain in
/-- Materializing a finite sequence with adjacent endpoint equalities gives an exact endpoint path. -/
theorem pathEndpoints_ofFn {Vertex EdgeLabel : Type}
    (edgeStart edgeFinish : EdgeLabel -> Vertex) :
    forall {steps : Nat} (edgeAt : Fin (steps + 1) -> EdgeLabel),
      (forall index : Fin steps,
        edgeFinish (edgeAt index.castSucc) =
          edgeStart (edgeAt index.succ)) ->
      PathEndpoints edgeStart edgeFinish (List.ofFn edgeAt)
        (edgeStart (edgeAt 0)) (edgeFinish (edgeAt (Fin.last steps)))
  | 0, edgeAt, _ => by
      rw [Purelib.Data.List.OfFn.Basic.ofFn_succ, List.ofFn_zero]
      exact .cons (.nil _)
  | steps + 1, edgeAt, adjacent => by
      rw [Purelib.Data.List.OfFn.Basic.ofFn_succ]
      have tailAdjacent : forall index : Fin steps,
          edgeFinish (edgeAt index.castSucc.succ) =
            edgeStart (edgeAt index.succ.succ) := by
        intro index
        exact adjacent index.succ
      have tailPath := pathEndpoints_ofFn edgeStart edgeFinish
        (fun index : Fin (steps + 1) => edgeAt index.succ) tailAdjacent
      have firstAdjacent : edgeFinish (edgeAt 0) = edgeStart (edgeAt 1) :=
        adjacent 0
      apply PathBoundary.PathEndpoints.cons
      have alignedTail := tailPath.castStart firstAdjacent.symm
      have lastEqual : (Fin.last steps).succ = Fin.last (steps + 1) := by
        apply Fin.ext
        rfl
      have finishEqual :
          edgeFinish (edgeAt (Fin.last steps).succ) =
            edgeFinish (edgeAt (Fin.last (steps + 1))) := by
        rw [lastEqual]
      exact alignedTail.castFinish finishEqual

/-- The cyclic successor of a nonterminal index is its ordinary successor. -/
theorem cyclicSucc_castSucc {count : Nat} (positive : 0 < count + 1)
    (index : Fin count) :
    Attachment.cyclicSucc positive index.castSucc = index.succ := by
  apply Fin.ext
  unfold Attachment.cyclicSucc
  split
  · rfl
  · rename_i notBelow
    exact (notBelow (Nat.succ_lt_succ index.isLt)).elim

/-- The cyclic successor of the final index is zero. -/
theorem cyclicSucc_last {count : Nat} (positive : 0 < count + 1) :
    Attachment.cyclicSucc positive (Fin.last count) = 0 := by
  apply Fin.ext
  unfold Attachment.cyclicSucc
  split
  · rename_i below
    have lastValue : (Fin.last count).val = count := rfl
    omega0
  · rfl

open Purelib.Topology.Chain in
/-- Every explicit cyclic attachment is an exact closed finite path. -/
theorem attachment_path {Vertex : Type} {steps : Nat}
    {edgeStart edgeFinish : Attachment.Edge (steps + 1) -> Vertex}
    (attachment : Attachment.CyclicAttachment (steps + 1) Vertex edgeStart edgeFinish) :
    PathEndpoints edgeStart edgeFinish attachment.edges
      (edgeStart (attachment.edgeAt 0))
      (edgeStart (attachment.edgeAt 0)) := by
  have adjacent : forall index : Fin steps,
      edgeFinish (attachment.edgeAt index.castSucc) =
        edgeStart (attachment.edgeAt index.succ) := by
    intro index
    have continuous := attachment.continuous index.castSucc
    rw [cyclicSucc_castSucc] at continuous
    exact continuous
  have openPath := pathEndpoints_ofFn edgeStart edgeFinish
    attachment.edgeAt adjacent
  have closes := attachment.continuous (Fin.last steps)
  rw [cyclicSucc_last] at closes
  exact openPath.castFinish closes

/-- Integer indicator of one displayed vertex. -/
def vertexIndicator {Vertex : Type} [DecidableEq Vertex]
    (selected vertex : Vertex) : Int :=
  if vertex = selected then 1 else 0

open Purelib.Topology.Chain
/-- Boundary coefficient of one oriented edge at one vertex. -/
def edgeBoundaryAt {Vertex EdgeLabel : Type} [DecidableEq Vertex]
    (edgeStart edgeFinish : EdgeLabel -> Vertex)
    (edge : EdgeLabel) (vertex : Vertex) : Int :=
  vertexIndicator (edgeFinish edge) vertex -
    vertexIndicator (edgeStart edge) vertex

/-- Boundary coefficient of a displayed finite edge word. -/
def wordBoundaryAt {Vertex EdgeLabel : Type} [DecidableEq Vertex]
    (edgeStart edgeFinish : EdgeLabel -> Vertex) :
    List EdgeLabel -> Vertex -> Int
  | [], _ => 0
  | edge :: remaining, vertex =>
      edgeBoundaryAt edgeStart edgeFinish edge vertex +
        wordBoundaryAt edgeStart edgeFinish remaining vertex

/-- Finite telescoping: the boundary of a path is final vertex minus initial vertex. -/
theorem wordBoundaryAt_eq_endpoints {Vertex EdgeLabel : Type}
    [DecidableEq Vertex] {edgeStart edgeFinish : EdgeLabel -> Vertex}
    {edges : List EdgeLabel} {start finish : Vertex}
    (path : PathEndpoints edgeStart edgeFinish edges start finish)
    (vertex : Vertex) :
    wordBoundaryAt edgeStart edgeFinish edges vertex =
      vertexIndicator finish vertex - vertexIndicator start vertex := by
  induction path with
  | nil point =>
      unfold wordBoundaryAt
      ring1
  | @cons edge remaining finish tail inductionHypothesis =>
      unfold wordBoundaryAt edgeBoundaryAt
      rw [inductionHypothesis]
      ring1

/-- Pointwise cellular chain condition for every cyclic face attachment. -/
theorem attachment_boundary_zero {Vertex : Type} [DecidableEq Vertex]
    {steps : Nat} {edgeStart edgeFinish : Attachment.Edge (steps + 1) -> Vertex}
    (attachment : Attachment.CyclicAttachment (steps + 1) Vertex edgeStart edgeFinish)
    (vertex : Vertex) :
    wordBoundaryAt edgeStart edgeFinish attachment.edges vertex = 0 := by
  rw [wordBoundaryAt_eq_endpoints (attachment_path attachment)]
  ring1
end Purelib.Topology.Chain.PathBoundary

end
