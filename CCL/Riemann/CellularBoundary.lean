import CCL.Riemann.HyperellipticCells

/-!
# Cellular boundary of finite attaching walks

This module turns the explicit face attachments into integral cellular
boundary statements.  Paths are finite inductive objects with exact endpoint
types.  Their vertex boundary telescopes constructively, and every cyclic
hyperelliptic face attachment therefore satisfies `d₁ d₂ = 0` pointwise.
-/

namespace CCL.Riemann.CellularBoundary

open CCL.Riemann.HyperellipticCells

/-- A finite edge list with exact initial and final vertices. -/
inductive PathEndpoints {Vertex EdgeLabel : Type}
    (edgeStart edgeFinish : EdgeLabel -> Vertex) :
    List EdgeLabel -> Vertex -> Vertex -> Prop
  | nil (vertex : Vertex) : PathEndpoints edgeStart edgeFinish [] vertex vertex
  | cons {edge : EdgeLabel} {remaining : List EdgeLabel} {finish : Vertex}
      (tail : PathEndpoints edgeStart edgeFinish remaining
        (edgeFinish edge) finish) :
      PathEndpoints edgeStart edgeFinish (edge :: remaining)
        (edgeStart edge) finish

namespace PathEndpoints

theorem castStart {Vertex EdgeLabel : Type}
    {edgeStart edgeFinish : EdgeLabel -> Vertex}
    {edges : List EdgeLabel} {left right finish : Vertex}
    (equal : left = right)
    (path : PathEndpoints edgeStart edgeFinish edges left finish) :
    PathEndpoints edgeStart edgeFinish edges right finish := by
  subst right
  exact path

theorem castFinish {Vertex EdgeLabel : Type}
    {edgeStart edgeFinish : EdgeLabel -> Vertex}
    {edges : List EdgeLabel} {start left right : Vertex}
    (equal : left = right)
    (path : PathEndpoints edgeStart edgeFinish edges start left) :
    PathEndpoints edgeStart edgeFinish edges start right := by
  subst right
  exact path

end PathEndpoints

/-- Materializing a finite sequence with adjacent endpoint equalities gives
an exact endpoint path. -/
theorem pathEndpoints_ofFn {Vertex EdgeLabel : Type}
    (edgeStart edgeFinish : EdgeLabel -> Vertex) :
    forall {steps : Nat} (edgeAt : Fin (steps + 1) -> EdgeLabel),
      (forall index : Fin steps,
        edgeFinish (edgeAt index.castSucc) =
          edgeStart (edgeAt index.succ)) ->
      PathEndpoints edgeStart edgeFinish (List.ofFn edgeAt)
        (edgeStart (edgeAt 0)) (edgeFinish (edgeAt (Fin.last steps)))
  | 0, edgeAt, _ => by
      rw [QuotientFreeList.ofFn_succ, List.ofFn_zero]
      exact .cons (.nil _)
  | steps + 1, edgeAt, adjacent => by
      rw [QuotientFreeList.ofFn_succ]
      have tailAdjacent : forall index : Fin steps,
          edgeFinish (edgeAt index.castSucc.succ) =
            edgeStart (edgeAt index.succ.succ) := by
        intro index
        exact adjacent index.succ
      have tailPath := pathEndpoints_ofFn edgeStart edgeFinish
        (fun index : Fin (steps + 1) => edgeAt index.succ) tailAdjacent
      have firstAdjacent : edgeFinish (edgeAt 0) = edgeStart (edgeAt 1) :=
        adjacent 0
      apply PathEndpoints.cons
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
    cyclicSucc positive index.castSucc = index.succ := by
  apply Fin.ext
  unfold cyclicSucc
  split
  · rfl
  · rename_i notBelow
    exact (notBelow (Nat.succ_lt_succ index.isLt)).elim

/-- The cyclic successor of the final index is zero. -/
theorem cyclicSucc_last {count : Nat} (positive : 0 < count + 1) :
    cyclicSucc positive (Fin.last count) = 0 := by
  apply Fin.ext
  unfold cyclicSucc
  split
  · rename_i below
    have lastValue : (Fin.last count).val = count := rfl
    omega0
  · rfl

/-- Every explicit cyclic attachment is an exact closed finite path. -/
theorem attachment_path {Vertex : Type} {steps : Nat}
    {edgeStart edgeFinish : Edge (steps + 1) -> Vertex}
    (attachment : CyclicAttachment (steps + 1) Vertex edgeStart edgeFinish) :
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

/-- Finite telescoping: the boundary of a path is final vertex minus initial
vertex. -/
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
    {steps : Nat} {edgeStart edgeFinish : Edge (steps + 1) -> Vertex}
    (attachment : CyclicAttachment (steps + 1) Vertex edgeStart edgeFinish)
    (vertex : Vertex) :
    wordBoundaryAt edgeStart edgeFinish attachment.edges vertex = 0 := by
  rw [wordBoundaryAt_eq_endpoints (attachment_path attachment)]
  ring1

/-- Every odd-degree hyperelliptic face satisfies `d₁ d₂ = 0`. -/
theorem odd_face_boundary_boundary_zero (genus : Nat) (face : Face)
    (vertex : OddVertex genus) :
    wordBoundaryAt oddEdgeStart oddEdgeFinish
      (oddFaceAttachment genus face).edges vertex = 0 := by
  exact attachment_boundary_zero (oddFaceAttachment genus face) vertex

/-- Every even-degree hyperelliptic face satisfies `d₁ d₂ = 0`, including at
the two separate vertices over infinity. -/
theorem even_face_boundary_boundary_zero (genus : Nat) (face : Face)
    (vertex : EvenVertex genus) :
    wordBoundaryAt evenEdgeStart evenEdgeFinish
      (evenFaceAttachment genus face).edges vertex = 0 := by
  exact attachment_boundary_zero (evenFaceAttachment genus face) vertex

end CCL.Riemann.CellularBoundary
