import mathlib.RFAP.ConstructiveFiniteMatrix

/-!
# Exact finite polygon Stokes algebra

This module isolates the finite algebra at the heart of the first Riemann
bilinear relation.  A point records two Gaussian-rational primitive values.
The oriented edge area is the doubled trapezoidal integral

`F(start) * G(finish) - F(finish) * G(start)`.

It changes sign under reversal.  Hence fan-triangle boundaries telescope to
the outer polygon boundary without limits, integration spaces, or choice.
The boundary of one symplectic commutator polygon is exactly twice
`Aᵢ Bⱼ - Bᵢ Aⱼ`; summing over the finite handle set gives the fraction-free
first-bilinear numerator.

The factor two is intentional.  Keeping all constructions division-free
makes internal-edge cancellation literal.  It is cancelled only after an
apartness proof for the exact rational scalar two.
-/

namespace CCL.Riemann.FinitePolygonStokes

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size

/-- Two displayed primitive values at one vertex of a finite cut polygon. -/
structure PrimitivePoint where
  left : Gaussian
  right : Gaussian

namespace PrimitivePoint

def zero : PrimitivePoint := ⟨0, 0⟩

def add (first second : PrimitivePoint) : PrimitivePoint :=
  ⟨first.left + second.left, first.right + second.right⟩

@[simp] theorem add_left (first second : PrimitivePoint) :
    (first.add second).left = first.left + second.left := rfl

@[simp] theorem add_right (first second : PrimitivePoint) :
    (first.add second).right = first.right + second.right := rfl

end PrimitivePoint

/-- Doubled oriented trapezoidal integral of `F dG` on one displayed edge. -/
def edgeArea (start finish : PrimitivePoint) : Gaussian :=
  start.left * finish.right - finish.left * start.right

/-- Reversing an oriented edge negates its exact contribution. -/
theorem edgeArea_reverse (start finish : PrimitivePoint) :
    edgeArea finish start = -edgeArea start finish := by
  unfold edgeArea
  ring1

/-- A degenerate edge has zero contribution. -/
@[simp] theorem edgeArea_self (point : PrimitivePoint) :
    edgeArea point point = 0 := by
  unfold edgeArea
  ring1

/-- Oriented boundary sum of one displayed triangle. -/
def triangleBoundaryArea (first second third : PrimitivePoint) : Gaussian :=
  edgeArea first second + edgeArea second third + edgeArea third first

/-- Doubled local wedge determinant on one displayed triangle. -/
def triangleWedgeArea (first second third : PrimitivePoint) : Gaussian :=
  (second.left - first.left) * (third.right - first.right) -
    (third.left - first.left) * (second.right - first.right)

/-- Exact finite triangle Stokes identity. -/
theorem triangleBoundaryArea_eq_wedgeArea
    (first second third : PrimitivePoint) :
    triangleBoundaryArea first second third =
      triangleWedgeArea first second third := by
  unfold triangleBoundaryArea triangleWedgeArea edgeArea
  ring1

/-- Boundary contribution of a path from `previous` through the displayed
remaining vertices and finally back to `anchor`. -/
def pathToAnchorArea (anchor previous : PrimitivePoint) :
    List PrimitivePoint -> Gaussian
  | [] => edgeArea previous anchor
  | next :: remaining =>
      edgeArea previous next + pathToAnchorArea anchor next remaining

/-- Doubled integral around the polygon whose cyclic vertex list is
`anchor :: remaining`. -/
def polygonBoundaryArea (anchor : PrimitivePoint) :
    List PrimitivePoint -> Gaussian
  | [] => 0
  | first :: remaining =>
      edgeArea anchor first + pathToAnchorArea anchor first remaining

/-- Sum of local wedge determinants in the fan based at `anchor`. -/
def fanWedgeArea (anchor : PrimitivePoint) :
    List PrimitivePoint -> Gaussian
  | [] => 0
  | [_first] => 0
  | first :: second :: remaining =>
      triangleWedgeArea anchor first second +
        fanWedgeArea anchor (second :: remaining)

/-- Finite polygon Stokes: all fan-internal edges occur once in each
orientation and cancel, leaving exactly the outer polygon boundary. -/
theorem fanWedgeArea_eq_polygonBoundaryArea (anchor : PrimitivePoint) :
    forall remaining : List PrimitivePoint,
      fanWedgeArea anchor remaining = polygonBoundaryArea anchor remaining
  | [] => rfl
  | [first] => by
      simp only [fanWedgeArea, polygonBoundaryArea, pathToAnchorArea]
      rw [edgeArea_reverse]
      ring1
  | first :: second :: remaining => by
      simp only [fanWedgeArea, polygonBoundaryArea, pathToAnchorArea]
      rw [fanWedgeArea_eq_polygonBoundaryArea anchor (second :: remaining)]
      simp only [polygonBoundaryArea]
      rw [← triangleBoundaryArea_eq_wedgeArea]
      unfold triangleBoundaryArea
      rw [edgeArea_reverse second anchor]
      ring1

/-- Boundary vertices of one translated commutator polygon
`a, b, -a, -b`.  The final vertex is again `start` and is implicit in the
cyclic polygon representation. -/
def commutatorVertices (start a b : PrimitivePoint) :
    List PrimitivePoint :=
  [start.add a, (start.add a).add b, start.add b]

/-- Exact doubled boundary integral of one symplectic handle. -/
def commutatorBoundaryArea (start a b : PrimitivePoint) : Gaussian :=
  polygonBoundaryArea start (commutatorVertices start a b)

/-- Translation drops out and one commutator boundary is twice the
determinant of its two primitive increments. -/
theorem commutatorBoundaryArea_eq (start a b : PrimitivePoint) :
    commutatorBoundaryArea start a b =
      2 * (a.left * b.right - b.left * a.right) := by
  simp only [commutatorBoundaryArea, commutatorVertices,
    polygonBoundaryArea, pathToAnchorArea, edgeArea, PrimitivePoint.add]
  ring1

/-- Primitive increment pair supplied by the A-periods of two differentials
around one displayed handle. -/
def aIncrement {size : Nat} (aMatrix : GaussianMatrix size)
    (row column cycle : Fin size) : PrimitivePoint :=
  ⟨aMatrix row cycle, aMatrix column cycle⟩

/-- The corresponding B-period primitive increment pair. -/
def bIncrement {size : Nat} (bMatrix : GaussianMatrix size)
    (row column cycle : Fin size) : PrimitivePoint :=
  ⟨bMatrix row cycle, bMatrix column cycle⟩

/-- Exact finite boundary sum of all handle commutator polygons. -/
def symplecticBoundaryArea {size : Nat}
    (aMatrix bMatrix : GaussianMatrix size) (row column : Fin size) :
    Gaussian :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
    commutatorBoundaryArea PrimitivePoint.zero
      (aIncrement aMatrix row column cycle)
      (bIncrement bMatrix row column cycle)

/-- Exact sample-level first-bilinear pairing in symplectic coordinates. -/
def symplecticPairing {size : Nat}
    (aMatrix bMatrix : GaussianMatrix size) (row column : Fin size) :
    Gaussian :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
    aMatrix row cycle * bMatrix column cycle -
      bMatrix row cycle * aMatrix column cycle

/-- The complete cut-polygon boundary is exactly twice the usual
`A Bᵀ - B Aᵀ` entry. -/
theorem symplecticBoundaryArea_eq_two_mul_pairing {size : Nat}
    (aMatrix bMatrix : GaussianMatrix size) (row column : Fin size) :
    symplecticBoundaryArea aMatrix bMatrix row column =
      2 * symplecticPairing aMatrix bMatrix row column := by
  unfold symplecticBoundaryArea symplecticPairing
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun cycle => 2 *
      (aMatrix row cycle * bMatrix column cycle -
        bMatrix row cycle * aMatrix column cycle))
    (fun cycle => by
      exact commutatorBoundaryArea_eq PrimitivePoint.zero
        (aIncrement aMatrix row column cycle)
        (bIncrement bMatrix row column cycle))]
  exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_left 2 _

/-! ## Arbitrary finite triangulations -/

/-- One oriented edge in a finite vertex bank. -/
structure OrientedEdge (vertexCount : Nat) where
  start : Fin vertexCount
  finish : Fin vertexCount

namespace OrientedEdge

/-- Reverse one displayed edge. -/
def reverse {vertexCount : Nat} (edge : OrientedEdge vertexCount) :
    OrientedEdge vertexCount :=
  ⟨edge.finish, edge.start⟩

@[simp] theorem reverse_start {vertexCount : Nat}
    (edge : OrientedEdge vertexCount) : edge.reverse.start = edge.finish := rfl

@[simp] theorem reverse_finish {vertexCount : Nat}
    (edge : OrientedEdge vertexCount) : edge.reverse.finish = edge.start := rfl

@[simp] theorem reverse_reverse {vertexCount : Nat}
    (edge : OrientedEdge vertexCount) : edge.reverse.reverse = edge := by
  cases edge
  rfl

end OrientedEdge

/-- One oriented triangle in the same finite vertex bank. -/
structure OrientedTriangle (vertexCount : Nat) where
  first : Fin vertexCount
  second : Fin vertexCount
  third : Fin vertexCount

namespace OrientedTriangle

/-- The three oriented boundary edges of a displayed triangle. -/
def boundary {vertexCount : Nat}
    (triangle : OrientedTriangle vertexCount) :
    List (OrientedEdge vertexCount) :=
  [⟨triangle.first, triangle.second⟩,
    ⟨triangle.second, triangle.third⟩,
    ⟨triangle.third, triangle.first⟩]

end OrientedTriangle

/-- A minimal constructive permutation relation for finite edge occurrence
lists.  It is kept here instead of importing generic permutation algebra:
only adjacent swaps, a common head, and transitivity are needed. -/
inductive EdgeReordering {vertexCount : Nat} :
    List (OrientedEdge vertexCount) ->
      List (OrientedEdge vertexCount) -> Prop
  | nil : EdgeReordering [] []
  | cons (edge : OrientedEdge vertexCount) {left right}
      (remaining : EdgeReordering left right) :
      EdgeReordering (edge :: left) (edge :: right)
  | swap (first second : OrientedEdge vertexCount) (remaining) :
      EdgeReordering (first :: second :: remaining)
        (second :: first :: remaining)
  | trans {first second third}
      (left : EdgeReordering first second)
      (right : EdgeReordering second third) :
      EdgeReordering first third

/-- Exact edge-area sum of a finite oriented edge list. -/
def edgeListArea {vertexCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint) :
    List (OrientedEdge vertexCount) -> Gaussian
  | [] => 0
  | edge :: remaining =>
      edgeArea (points edge.start) (points edge.finish) +
        edgeListArea points remaining

/-- Edge-area sums distribute across literal list concatenation. -/
theorem edgeListArea_append {vertexCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint) :
    forall first second : List (OrientedEdge vertexCount),
      edgeListArea points (first ++ second) =
        edgeListArea points first + edgeListArea points second
  | [], second => by
      simp only [List.nil_append, edgeListArea]
      ring1
  | edge :: remaining, second => by
      simp only [List.cons_append, edgeListArea]
      rw [edgeListArea_append points remaining second]
      ring1

/-- Reordering finitely many displayed edge occurrences does not change their
commutative exact area sum. -/
theorem edgeListArea_reordering {vertexCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint) {left right}
    (reordering : EdgeReordering left right) :
    edgeListArea points left = edgeListArea points right := by
  induction reordering with
  | nil => rfl
  | cons edge remaining inductionHypothesis =>
      simp only [edgeListArea]
      rw [inductionHypothesis]
  | swap first second remaining =>
      simp only [edgeListArea]
      ring1
  | trans left right leftHypothesis rightHypothesis =>
      exact leftHypothesis.trans rightHypothesis

/-- Materialize every internal edge immediately followed by its reverse. -/
def pairedEdgeOccurrences {vertexCount : Nat} :
    List (OrientedEdge vertexCount) -> List (OrientedEdge vertexCount)
  | [] => []
  | edge :: remaining =>
      edge :: edge.reverse :: pairedEdgeOccurrences remaining

/-- Every displayed internal edge pair cancels exactly. -/
theorem pairedEdgeOccurrences_area_zero {vertexCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint) :
    forall internalEdges : List (OrientedEdge vertexCount),
      edgeListArea points (pairedEdgeOccurrences internalEdges) = 0
  | [] => rfl
  | edge :: remaining => by
      simp only [pairedEdgeOccurrences, edgeListArea,
        OrientedEdge.reverse_start, OrientedEdge.reverse_finish]
      rw [edgeArea_reverse, pairedEdgeOccurrences_area_zero points remaining]
      ring1

/-- All oriented edge occurrences of a finite triangle bank. -/
def triangleEdgeOccurrences {vertexCount faceCount : Nat}
    (faces : Fin faceCount -> OrientedTriangle vertexCount) :
    List (OrientedEdge vertexCount) :=
  (List.ofFn faces).flatMap OrientedTriangle.boundary

/-- Exact sum of doubled local wedge areas over a finite triangle bank. -/
def triangleWedgeSum {vertexCount faceCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint)
    (faces : Fin faceCount -> OrientedTriangle vertexCount) : Gaussian :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun face =>
    let triangle := faces face
    triangleWedgeArea (points triangle.first) (points triangle.second)
      (points triangle.third)

/-- The sum of the triangle boundary areas is the area of the flattened edge
occurrence list. -/
theorem triangleWedgeSum_eq_edgeListArea {vertexCount faceCount : Nat}
    (points : Fin vertexCount -> PrimitivePoint)
    (faces : Fin faceCount -> OrientedTriangle vertexCount) :
    triangleWedgeSum points faces =
      edgeListArea points (triangleEdgeOccurrences faces) := by
  induction faceCount with
  | zero => rfl
  | succ faceCount inductionHypothesis =>
      rw [triangleWedgeSum, RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      change
        triangleWedgeArea
            (points (faces 0).first) (points (faces 0).second)
              (points (faces 0).third) +
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun face : Fin faceCount =>
                triangleWedgeArea
                  (points (faces face.succ).first)
                  (points (faces face.succ).second)
                  (points (faces face.succ).third)) = _
      rw [show triangleEdgeOccurrences faces =
          OrientedTriangle.boundary (faces 0) ++
            triangleEdgeOccurrences
              (fun face : Fin faceCount => faces face.succ) by
        unfold triangleEdgeOccurrences
        rw [QuotientFreeList.ofFn_succ]
        rfl,
        edgeListArea_append,
        ← triangleBoundaryArea_eq_wedgeArea]
      change
        triangleBoundaryArea
            (points (faces 0).first) (points (faces 0).second)
              (points (faces 0).third) +
            triangleWedgeSum points
              (fun face : Fin faceCount => faces face.succ) =
          edgeListArea points (OrientedTriangle.boundary (faces 0)) +
            edgeListArea points
              (triangleEdgeOccurrences
                (fun face : Fin faceCount => faces face.succ))
      rw [inductionHypothesis
        (fun face : Fin faceCount => faces face.succ)]
      congr 1
      simp only [triangleBoundaryArea, OrientedTriangle.boundary,
        edgeListArea]
      ring1

/-- A finite oriented triangulation is certified solely by incidence: its
complete face-edge list can be reordered into the outer boundary followed by
one edge/reverse-edge pair for every internal edge. -/
structure Triangulation (vertexCount faceCount : Nat) where
  faces : Fin faceCount -> OrientedTriangle vertexCount
  boundary : List (OrientedEdge vertexCount)
  internalEdges : List (OrientedEdge vertexCount)
  incidence : EdgeReordering (triangleEdgeOccurrences faces)
    (boundary ++ pairedEdgeOccurrences internalEdges)

namespace Triangulation

/-- Exact finite Stokes for an arbitrary certified triangulation: local
triangle wedges sum to the oriented outer boundary, while every internal edge
cancels with its displayed reverse occurrence. -/
theorem wedgeSum_eq_boundaryArea {vertexCount faceCount : Nat}
    (triangulation : Triangulation vertexCount faceCount)
    (points : Fin vertexCount -> PrimitivePoint) :
    triangleWedgeSum points triangulation.faces =
      edgeListArea points triangulation.boundary := by
  calc
    triangleWedgeSum points triangulation.faces =
        edgeListArea points
          (triangleEdgeOccurrences triangulation.faces) :=
      triangleWedgeSum_eq_edgeListArea points triangulation.faces
    _ = edgeListArea points
          (triangulation.boundary ++
            pairedEdgeOccurrences triangulation.internalEdges) :=
      edgeListArea_reordering points triangulation.incidence
    _ = edgeListArea points triangulation.boundary +
          edgeListArea points
            (pairedEdgeOccurrences triangulation.internalEdges) :=
      edgeListArea_append points _ _
    _ = edgeListArea points triangulation.boundary := by
      rw [pairedEdgeOccurrences_area_zero]
      ring1

end Triangulation

end CCL.Riemann.FinitePolygonStokes
