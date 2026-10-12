module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Mathlib.Order.Basic

public section

/-!
# Unique oriented occurrences in rectangular two-triangle meshes

The six occurrences have distinct finite direction signatures. Two separated
proper rectangles cannot share an occurrence with the same orientation: their
interiors would lie on the same side of that edge. Opposite orientations on a
shared side remain permitted. Everything depends only on retained coordinates,
so generated vertex banks can use the same geometric proof interface.
-/

section

open Purelib

open Purelib.Data.List

open Purelib.Geometry

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)

section

namespace Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge

/-- The six oriented edge occurrences in a two-triangle rectangle.

The four outer sides and the two directions of the shared diagonal remain separate occurrences. -/
inductive Kind where
  /-- The bottom side directed from left to right. -/ | bottom /-- The right side directed upward. -/ | right /-- The
    diagonal directed from the upper-right corner to the lower-left corner. -/ | downDiagonal /-- The diagonal directed
    from the lower-left corner to the upper-right corner. -/ | upDiagonal /-- The top side directed from right to left.
    -/ | top /-- The left side directed downward. -/ | left
  deriving DecidableEq

/-- List all six edge kinds in triangle-boundary traversal order. -/
@[expose] def kinds : List Kind := [.bottom, .right, .downDiagonal, .upDiagonal, .top, .left]

/-- The ordered endpoints of each rectangle edge kind. -/
@[expose] def coordinates (box : Rational.Box) :
  Kind → Data.Gaussian.Basic.Canonical ×
  Data.Gaussian.Basic.Canonical
  | .bottom => (⟨box.xLower, box.yLower⟩, ⟨box.xUpper, box.yLower⟩)
  | .right => (⟨box.xUpper, box.yLower⟩, ⟨box.xUpper, box.yUpper⟩)
  | .downDiagonal => (⟨box.xUpper, box.yUpper⟩, ⟨box.xLower, box.yLower⟩)
  | .upDiagonal => (⟨box.xLower, box.yLower⟩, ⟨box.xUpper, box.yUpper⟩)
  | .top => (⟨box.xUpper, box.yUpper⟩, ⟨box.xLower, box.yUpper⟩)
  | .left => (⟨box.xLower, box.yUpper⟩, ⟨box.xLower, box.yLower⟩)

/-- Record strict horizontal and vertical directions of an ordered endpoint pair. -/
private def signature (ends : Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical) : Bool × Bool × Bool × Bool
  :=
  (decide (ends.1.re < ends.2.re), decide (ends.2.re < ends.1.re),
    decide (ends.1.im < ends.2.im), decide (ends.2.im < ends.1.im))

/-- The four direction bits prescribed for each rectangle edge kind. -/
private def kindSignature : Kind → Bool × Bool ×
  Bool × Bool
  | .bottom => (true, false, false, false)
  | .right => (false, false, true, false)
  | .downDiagonal => (false, true, false, true)
  | .upDiagonal => (true, false, true, false)
  | .top => (false, true, false, false)
  | .left => (false, false, false, true)

/-- Proper rectangle coordinates have their prescribed direction signature.

Properness supplies both strict coordinate increases and excludes their reverse directions. Direct Boolean decision
certificates identify each original direction bit, including equal-coordinate bits on horizontal and vertical edges. -/
private theorem signature_coordinates {box : Rational.Box} (proper : box.Proper) (kind :
  Kind) :
    signature
      (coordinates box kind) =
      kindSignature kind := by
  have horizontal : decide (box.xLower < box.xUpper) = true := decide_eq_true proper.1
  have horizontalReverse : decide (box.xUpper < box.xLower) = false := decide_eq_false (not_lt_of_ge proper.1.le)
  have vertical : decide (box.yLower < box.yUpper) = true := decide_eq_true proper.2
  have verticalReverse : decide (box.yUpper < box.yLower) = false := decide_eq_false (not_lt_of_ge proper.2.le)
  have horizontalLower : decide (box.xLower < box.xLower) = false := decide_eq_false (lt_irrefl _)
  have horizontalUpper : decide (box.xUpper < box.xUpper) = false := decide_eq_false (lt_irrefl _)
  have verticalLower : decide (box.yLower < box.yLower) = false := decide_eq_false (lt_irrefl _)
  have verticalUpper : decide (box.yUpper < box.yUpper) = false := decide_eq_false (lt_irrefl _)
  cases kind <;> dsimp only [signature, coordinates, kindSignature]
  · rw [horizontal, horizontalReverse, verticalLower]
  · rw [horizontalUpper, vertical, verticalReverse]
  · rw [horizontalReverse, horizontal, verticalReverse, vertical]
  · rw [horizontal, horizontalReverse, vertical, verticalReverse]
  · rw [horizontalReverse, horizontal, verticalUpper]
  · rw [horizontalLower, verticalReverse, vertical]

/-- The six edge kinds have distinct direction signatures. -/
private theorem kindSignature_injective : Function.Injective kindSignature := by
  intro first second equal
  cases first <;> cases second <;> first | rfl | cases equal

/-- Equal directed endpoints in proper rectangles imply equal edge kinds. -/
theorem kind_eq_of_coordinates {first second : Rational.Box}
    (firstProper : first.Proper) (secondProper : second.Proper) {firstKind secondKind :
      Kind}
    (equal : coordinates first firstKind =
      coordinates second secondKind) : firstKind =
      secondKind :=
  kindSignature_injective
    ((signature_coordinates firstProper
    firstKind).symm.trans
    ((congrArg signature equal).trans
      (signature_coordinates secondProper
      secondKind)))

/-- Equal endpoints of the same edge kind force interior overlap in both axes. -/
private theorem overlap_of_coordinates {first second : Rational.Box}
    (firstProper : first.Proper) (secondProper : second.Proper) (kind :
      Kind)
    (equal : coordinates first kind =
      coordinates second kind) :
    first.xLower < second.xUpper ∧ second.xLower < first.xUpper ∧
      first.yLower < second.yUpper ∧ second.yLower < first.yUpper := by
  have sx := congrArg (fun ends : Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical => ends.1.re) equal
  have fx := congrArg (fun ends : Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical => ends.2.re) equal
  have sy := congrArg (fun ends : Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical => ends.1.im) equal
  have fy := congrArg (fun ends : Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical => ends.2.im) equal
  cases kind <;> dsimp only [coordinates,
    Data.Gaussian.Basic.re,
    Data.Gaussian.Basic.im] at sx fx sy fy <;> refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | simpa only [sx, fx, sy, fy] using firstProper.1
    | simpa only [sx, fx, sy, fy] using firstProper.2
    | simpa only [sx, fx, sy, fy] using secondProper.1
    | simpa only [sx, fx, sy, fy] using secondProper.2

/-- Interior-separated proper rectangles cannot share a directed edge occurrence. -/
theorem separated_coordinates_ne {first second : Rational.Box}
    (firstProper : first.Proper) (secondProper : second.Proper)
    (separated : first.InteriorSeparated second) (firstKind secondKind :
      Kind) :
    coordinates first firstKind ≠
      coordinates second secondKind := by
  intro equal
  have same := kind_eq_of_coordinates firstProper
    secondProper equal
  subst secondKind
  have overlap := overlap_of_coordinates
    firstProper secondProper firstKind equal
  rcases separated with before | after | below | above
  · exact (not_lt_of_ge before) overlap.2.1
  · exact (not_lt_of_ge after) overlap.1
  · exact (not_lt_of_ge below) overlap.2.2.2
  · exact (not_lt_of_ge above) overlap.2.2.1

end Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge

end

section

variable {count : Nat}

namespace Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral

/-- Select one of the six directed edges of an indexed quadrilateral. -/
@[expose] def edge (quad :
  IndexedQuadrilaterals.IndexedQuadrilateral count) :
  Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.Kind → Stokes.OrientedEdge count
  | .bottom => ⟨quad.first, quad.second⟩
  | .right => ⟨quad.second, quad.third⟩
  | .downDiagonal => ⟨quad.third, quad.first⟩
  | .upDiagonal => ⟨quad.first, quad.third⟩
  | .top => ⟨quad.third, quad.fourth⟩
  | .left => ⟨quad.fourth, quad.first⟩

end Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral

open Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral (edge)

namespace Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral

/-- The two triangle boundaries enumerate the six selected edge kinds. -/
theorem triangleEdges_eq (quad : IndexedQuadrilaterals.IndexedQuadrilateral count) :
    quad.triangles.flatMap OrientedTriangle.boundary = RectangleEdge.kinds.map
      (Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge quad) := rfl

/-- Exact corner positions, independent of the choice of shared indices. -/
structure RectangleCoordinates (quad : IndexedQuadrilaterals.IndexedQuadrilateral count)
    (coordinate : Fin count → Data.Gaussian.Basic.Canonical) (box : Rational.Box) : Prop where
  /-- The first indexed vertex is the lower-left corner. -/ first : coordinate quad.first = ⟨box.xLower, box.yLower⟩
  /-- The second indexed vertex is the lower-right corner. -/ second : coordinate quad.second = ⟨box.xUpper, box.yLower⟩
  /-- The third indexed vertex is the upper-right corner. -/ third : coordinate quad.third = ⟨box.xUpper, box.yUpper⟩
  /-- The fourth indexed vertex is the upper-left corner. -/ fourth : coordinate quad.fourth = ⟨box.xLower, box.yUpper⟩

end Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral

section

variable {coordinate : Fin count → Purelib.Data.Gaussian.Basic.Canonical} {box :
  Purelib.Geometry.Rational.Box} {quad :
  Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral count}

section
open Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral

namespace Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

/-- Read an indexed edge through the retained rectangle corner coordinates.

The original edge kind selects two retained indexed corners. Their exact coordinate equations identify the same ordered
endpoint pair without changing either shared vertex index. -/
theorem edge_coordinates (geometry :
  RectangleCoordinates quad coordinate box)
  (kind : Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.Kind) :
    (coordinate (Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge quad kind).start, coordinate
      (Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge quad kind).finish) =
      Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.coordinates box kind := by
  cases kind <;> dsimp only [edge, RectangleEdge.coordinates]
  · exact Prod.ext geometry.first geometry.second
  · exact Prod.ext geometry.second geometry.third
  · exact Prod.ext geometry.third geometry.first
  · exact Prod.ext geometry.first geometry.third
  · exact Prod.ext geometry.third geometry.fourth
  · exact Prod.ext geometry.fourth geometry.first

/-- The six indexed edges of a proper rectangle are distinct. -/
theorem edge_injective (geometry :
  RectangleCoordinates quad coordinate box)
  (proper : box.Proper) :
    Function.Injective (Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge quad) := by
  intro first second equal
  exact Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.kind_eq_of_coordinates proper proper
    ((geometry.edge_coordinates first).symm.trans
      ((congrArg (fun edge : Stokes.OrientedEdge count => (coordinate edge.start, coordinate edge.finish)) equal).trans
        (geometry.edge_coordinates second)))

end Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

end

namespace Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

/-- A proper rectangle's two triangle boundaries have no repeated directed occurrence. -/
theorem edges_nodup (geometry :
  RectangleCoordinates quad coordinate box)
  (proper : box.Proper) :
    (quad.triangles.flatMap OrientedTriangle.boundary).Nodup := by
  rw [triangleEdges_eq quad]
  exact Data.List.Nodup.nodup_map_of_injective (geometry.edge_injective proper) (by decide)

open Purelib.Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral
/-- Interior-separated proper rectangles have disjoint directed boundary occurrences. -/
theorem edges_disjoint {other : IndexedQuadrilaterals.IndexedQuadrilateral count} {otherBox :
  Rational.Box}
    (geometry : RectangleCoordinates quad
      coordinate box) (otherGeometry :
      RectangleCoordinates other coordinate
      otherBox)
    (proper : box.Proper) (otherProper : otherBox.Proper) (separated : box.InteriorSeparated otherBox) :
    ∀ left ∈ quad.triangles.flatMap OrientedTriangle.boundary,
      ∀ right ∈ other.triangles.flatMap OrientedTriangle.boundary, left ≠ right := by
  intro left leftMember right rightMember equal
  rw [triangleEdges_eq quad] at leftMember
  rw [triangleEdges_eq other] at rightMember
  obtain ⟨leftKind, _, leftEq⟩ := Map.mem_map.mp leftMember
  obtain ⟨rightKind, _, rightEq⟩ := Map.mem_map.mp rightMember
  exact Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.separated_coordinates_ne proper otherProper
    separated leftKind rightKind
    ((geometry.edge_coordinates leftKind).symm.trans
      ((congrArg (fun edge : Stokes.OrientedEdge count => (coordinate edge.start, coordinate edge.finish))
        (leftEq.trans (equal.trans rightEq.symm))).trans (otherGeometry.edge_coordinates rightKind)))

/-- Above one base rectangle, distinct corresponding corners on two sheets separate every directed occurrence, including
both diagonal directions. -/
theorem sheets_disjoint {other : IndexedQuadrilaterals.IndexedQuadrilateral count}
    (geometry : RectangleCoordinates quad
      coordinate box) (otherGeometry :
      RectangleCoordinates other coordinate
      box)
    (proper : box.Proper) (different : quad.first ≠ other.first ∧ quad.second ≠ other.second ∧
      quad.third ≠ other.third ∧ quad.fourth ≠ other.fourth) :
    ∀ left ∈ quad.triangles.flatMap OrientedTriangle.boundary,
      ∀ right ∈ other.triangles.flatMap OrientedTriangle.boundary, left ≠ right := by
  intro left leftMember right rightMember equal
  rw [triangleEdges_eq quad] at leftMember
  rw [triangleEdges_eq other] at rightMember
  obtain ⟨leftKind, _, leftEq⟩ := Map.mem_map.mp leftMember
  obtain ⟨rightKind, _, rightEq⟩ := Map.mem_map.mp rightMember
  have edgeEq := leftEq.trans (equal.trans rightEq.symm)
  have kindEq := Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge.kind_eq_of_coordinates proper
    proper
    ((geometry.edge_coordinates leftKind).symm.trans
      ((congrArg (fun edge : Stokes.OrientedEdge count => (coordinate edge.start, coordinate edge.finish)) edgeEq).trans
        (otherGeometry.edge_coordinates rightKind)))
  subst rightKind
  have startEq := congrArg OrientedEdge.start edgeEq
  cases leftKind <;> first
    | exact different.1 startEq
    | exact different.2.1 startEq
    | exact different.2.2.1 startEq
    | exact different.2.2.2 startEq

end Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.IndexedQuadrilateral.RectangleCoordinates

end
end

end
