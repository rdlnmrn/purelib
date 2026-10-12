module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Integration.Path.JoinedTrace
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions

public section

/-! The whole matched side keeps every dyadic vertex of every original owner.
Duplicate physical junctions retain the two distinct primitive readings. -/
section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount dyadic dyadic_area)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
    Coordinate}

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

/-- The original horizontal interval index paired with its bounded dyadic vertex index. -/
abbrev Vertex
  (_side : MatchedHorizontalSide left right leftRow rightRow height) (depth : Nat) :=
  Fin left.partition.x.intervals.length × Fin (dyadicCount depth + 1)

open Purelib.Integration.Path in
/-- The exact indexed vertex trace of one retained horizontal piece.

The original piece index is paired with every bounded dyadic vertex index. The resulting word retains that piece and
depth without merging physical junction occurrences. -/
@[expose] def
  pieceVertices
  (side : MatchedHorizontalSide left right leftRow rightRow height) (depth : Nat)
    (column : Fin (left.boundaryColumns + 1)) : JoinedTrace.VertexTrace (side.Vertex depth) :=
  JoinedTrace.VertexTrace.ofIndexed (fun vertex => (Fin.cast left.boundaryColumns_eq column, vertex))

open Purelib.Data in
open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- Cached dyadic segments and their exact joined vertex word for the original matched horizontal side.

Each dependent segment retains its original paired piece, and the concatenation equation preserves the exact interval
order and shared depth. -/
structure Trace
  (side : MatchedHorizontalSide left right leftRow rightRow height) (depth : Nat) where
  /-- The dependent cached dyadic segments of the exact original paired pieces. -/ segments : Vector.DependentVector
    (fun index => RectangularPairedPointBanks.Trace (side.pieces index) (dyadicCount depth))
  /-- Each cached segment equals the original dyadic trace at the retained depth. -/ segments_eq : ∀ index, segments.get
    index = dyadic (side.pieces index) depth
  /-- The cached joined vertex word with original piece and vertex indices. -/ vertices : JoinedTrace.VertexTrace
    (side.Vertex depth)
  /-- The vertex cache equals the exact ordered concatenation of original piece traces. -/ vertices_eq : vertices =
    JoinedTrace.VertexTrace.concatenate (side.pieceVertices depth)

constructive_injectivity Trace

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

section
open Purelib.Algebra
open Purelib.Topology.Polygon

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

/-- Sum the original left-owner primitive joins between consecutive retained horizontal pieces. -/
@[expose] def
  leftJoins
  (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column : Fin left.boundaryColumns =>
    let before := side.pieces (Fin.cast left.boundaryColumns_eq column.castSucc)
    let after := side.pieces (Fin.cast left.boundaryColumns_eq column.succ)
    Stokes.edgeArea (values before.leftColumn before.leftRow before.last)
      (values after.leftColumn after.leftRow after.first))

/-- Sum the original right-owner primitive joins between consecutive retained horizontal pieces.

Each successive endpoint is read through its original right model-cell owner. The finite sum retains the same ordered
horizontal or vertical interval positions. -/
@[expose] def
  rightJoins
  (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  FiniteSum.Fin.sumFin (fun column : Fin left.boundaryColumns =>
    let before := side.pieces (Fin.cast left.boundaryColumns_eq column.castSucc)
    let after := side.pieces (Fin.cast left.boundaryColumns_eq column.succ)
    Stokes.edgeArea (values before.rightColumn before.rightRow before.last)
      (values after.rightColumn after.rightRow after.first))

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

end

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide (Vertex
  pieceVertices leftJoins rightJoins)

section

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

variable {side : MatchedHorizontalSide left right leftRow rightRow height} {depth : Nat}

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

open Purelib.Data in
open Purelib.Integration.Path in
/-- Cache the original matched horizontal side's dyadic segments and exact ordered joined vertex word.

The dependent vector caches every original dyadic segment. Its defining equations retain the original piece indices and
exact concatenated vertex word. -/
@[expose] def
  build
  (side : MatchedHorizontalSide left right leftRow rightRow height) (depth : Nat) : side.Trace depth :=
  ⟨Vector.DependentVector.ofFn (fun index => dyadic (side.pieces index) depth),
    fun index => Vector.DependentVector.ofFn_get _ index, JoinedTrace.VertexTrace.concatenate (side.pieceVertices
      depth), rfl⟩

/-- Read the exact point from the retained piece segment and its original dyadic vertex index. -/
@[expose] def
  point
  (trace : side.Trace depth) (vertex : side.Vertex depth) : Gaussian :=
  (trace.segments.get vertex.1).points vertex.2

open Purelib.Integration.Path in
/-- The retained joined trace starts at the first original column and its zero dyadic vertex.

The exact cached concatenation starts with the retained first piece word. Its original column or row cast and zero
dyadic vertex supply the same initial pair. -/
theorem
  first_index
  (trace : side.Trace depth) :
    trace.vertices.indexed 0 = (Fin.cast left.boundaryColumns_eq 0, 0) := by
  change trace.vertices.first = _
  rw [trace.vertices_eq, JoinedTrace.VertexTrace.concatenate, JoinedTrace.VertexTrace.glue_first]
  rfl

/-- The retained joined trace starts at the first original paired piece's endpoint.

The first retained segment certifies its initial endpoint. Reading the first vertex of the cached concatenation
therefore yields that same piece endpoint. -/
theorem
  first_point
  (trace : side.Trace depth) :
    trace.point (trace.vertices.indexed 0) = (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first := by
  rw [trace.first_index]
  exact (trace.segments.get (Fin.cast left.boundaryColumns_eq 0)).first_point

/-- Retain the original left model-cell owner and containment certificate for the exact trace point.

The selected segment supplies the original left model-cell index and containment certificate. Its point is the same
cached trace reading at the supplied vertex. -/
@[expose] def
  leftOwner
  (trace : side.Trace depth) (vertex : side.Vertex depth) : OwnedVertex leftGeometry :=
  ⟨(side.pieces vertex.1).leftColumn, (side.pieces vertex.1).leftRow, trace.point vertex,
    (trace.segments.get vertex.1).left_contains vertex.2⟩

/-- Retain the original right model-cell owner and containment certificate for the exact trace point.

The selected segment supplies the original right model-cell index and containment certificate. Its point is the same
cached trace reading at the supplied vertex. -/
@[expose] def
  rightOwner
  (trace : side.Trace depth) (vertex : side.Vertex depth) : OwnedVertex rightGeometry :=
  ⟨(side.pieces vertex.1).rightColumn, (side.pieces vertex.1).rightRow, trace.point vertex,
    (trace.segments.get vertex.1).right_contains vertex.2⟩

/-- The retained left owner reads back the exact original trace point. -/
theorem
  leftOwner_point
  (trace : side.Trace depth) (vertex : side.Vertex depth) :
    (trace.leftOwner vertex).point = trace.point vertex := rfl

/-- The retained right owner reads back the exact original trace point. -/
theorem
  rightOwner_point
  (trace : side.Trace depth) (vertex : side.Vertex depth) :
    (trace.rightOwner vertex).point = trace.point vertex := rfl

/-- Read the primitive value through the exact retained left model owner. -/
@[expose] def
  leftValue
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) (vertex : side.Vertex depth) :
      PrimitivePoint :=
  values (side.pieces vertex.1).leftColumn (side.pieces vertex.1).leftRow (trace.point vertex)

/-- Read the primitive value through the exact retained right model owner. -/
@[expose] def
  rightValue
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) (vertex : side.Vertex depth) :
      PrimitivePoint :=
  values (side.pieces vertex.1).rightColumn (side.pieces vertex.1).rightRow (trace.point vertex)

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- One retained horizontal piece's left trace area equals its exact original dyadic boundary area.

The segment cache equation identifies the retained dyadic trace for this original piece. Its left endpoint coordinates
and side orientation determine the same exact boundary area. -/
theorem
  piece_left_area
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (column : Fin (left.boundaryColumns + 1)) :
    (side.pieceVertices depth column).area (trace.leftValue values) =
      PreparedBoxBoundary.horizontalBoundary
        (values (side.pieces (Fin.cast left.boundaryColumns_eq column)).leftColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq column)).leftRow) depth
        (side.pieces (Fin.cast left.boundaryColumns_eq column)).first.re
        (side.pieces (Fin.cast left.boundaryColumns_eq column)).last.re height := by
  rw [ObservationMesh.MatchedHorizontalSide.pieceVertices, JoinedTrace.VertexTrace.ofIndexed_area]
  dsimp only [leftValue, point]
  rw [trace.segments_eq, dyadic_area, side.first_eq, side.last_eq]
  exact (DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea _ _ _ _ _).symm

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

namespace Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- The retained left trace area splits into original piece areas and exact joins of their vertex words.

The concatenated vertex word retains every original piece and intervening chord. Its left owner readings split into the
original side areas and the exact ordered joining contribution. -/
private theorem
  left_area_joining
    (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) :
    CenteredBilinearPath.area (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) =
      side.leftArea values depth + JoinedTrace.VertexTrace.joiningArea (trace.leftValue values) (side.pieceVertices
        depth 0)
        (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) := by
  rw [trace.vertices.indexed_area, trace.vertices_eq, JoinedTrace.VertexTrace.concatenate_area]
  have pieces := FiniteSum.Fin.sumFin_congr (trace.piece_left_area values)
  rw [pieces]
  have cast_sum {first last : Nat} (equal : first = last) (values : Fin last → Gaussian) :
      FiniteSum.Fin.sumFin (fun index : Fin first => values (Fin.cast equal index)) = FiniteSum.Fin.sumFin values := by
    cases equal
    rfl
  have equal := cast_sum left.boundaryColumns_eq (fun index => PreparedBoxBoundary.horizontalBoundary
    (values (side.pieces index).leftColumn (side.pieces index).leftRow) depth
    (side.pieces index).first.re (side.pieces index).last.re height)
  rw [equal]
  rfl

end Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- One retained horizontal piece's right trace area equals its exact original dyadic boundary area.

The segment cache equation identifies the retained dyadic trace for this original piece. Its right endpoint coordinates
and side orientation determine the same exact boundary area. -/
theorem
  piece_right_area
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (column : Fin (left.boundaryColumns + 1)) :
    (side.pieceVertices depth column).area (trace.rightValue values) =
      PreparedBoxBoundary.horizontalBoundary
        (values (side.pieces (Fin.cast left.boundaryColumns_eq column)).rightColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq column)).rightRow) depth
        (side.pieces (Fin.cast left.boundaryColumns_eq column)).first.re
        (side.pieces (Fin.cast left.boundaryColumns_eq column)).last.re height := by
  rw [ObservationMesh.MatchedHorizontalSide.pieceVertices, JoinedTrace.VertexTrace.ofIndexed_area]
  dsimp only [rightValue, point]
  rw [trace.segments_eq, dyadic_area, side.first_eq, side.last_eq]
  exact (DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea _ _ _ _ _).symm

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

namespace Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- The retained right trace area splits into original piece areas and exact joins of their vertex words.

The concatenated vertex word retains every original piece and intervening chord. Its right owner readings split into the
original side areas and the exact ordered joining contribution. -/
private theorem
  right_area_joining
    (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) :
    CenteredBilinearPath.area (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) =
      side.rightArea values depth + JoinedTrace.VertexTrace.joiningArea (trace.rightValue values) (side.pieceVertices
        depth 0)
        (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) := by
  rw [trace.vertices.indexed_area, trace.vertices_eq, JoinedTrace.VertexTrace.concatenate_area]
  have pieces := FiniteSum.Fin.sumFin_congr (trace.piece_right_area values)
  rw [pieces]
  have cast_sum {first last : Nat} (equal : first = last) (values : Fin last → Gaussian) :
      FiniteSum.Fin.sumFin (fun index : Fin first => values (Fin.cast equal index)) = FiniteSum.Fin.sumFin values := by
    cases equal
    rfl
  have equal := cast_sum left.boundaryColumns_eq (fun index => PreparedBoxBoundary.horizontalBoundary
    (values (side.pieces index).rightColumn (side.pieces index).rightRow) depth
    (side.pieces index).first.re (side.pieces index).last.re height)
  rw [equal]
  rfl

end Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

open Purelib.Algebra in
open Purelib.Integration.Path in
/-- The retained trace's left joining area equals the original left-owner endpoint-join sum.

The bounded successor pair identifies each joining chord. The original segment endpoint certificates recover its two
left-owner primitive values without merging their owners. -/
theorem
  left_joining_eq
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) :
    JoinedTrace.VertexTrace.joiningArea (trace.leftValue values) (side.pieceVertices depth 0)
      (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) = side.leftJoins values
        := by
  rw [JoinedTrace.VertexTrace.joiningArea_ofFn]
  unfold Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.leftJoins
  apply FiniteSum.Fin.sumFin_congr
  intro column
  simp only [ObservationMesh.MatchedHorizontalSide.pieceVertices]
  rw [JoinedTrace.VertexTrace.ofIndexed_last]
  dsimp only [JoinedTrace.VertexTrace.ofIndexed, leftValue, point]
  rw [(trace.segments.get (Fin.cast left.boundaryColumns_eq column.castSucc)).last_point,
    (trace.segments.get (Fin.cast left.boundaryColumns_eq column.succ)).first_point]

open Purelib.Riemann.Periods in
/-- The exact left trace area equals the retained matched-side area plus its original endpoint joins.

The exact piece-area and joining-area equations refer to the same retained trace word. Their scalar sum preserves its
original orientation and left-owner readings. -/
theorem
  left_area
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) :
    CenteredBilinearPath.area (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) =
      side.leftArea values depth + side.leftJoins values := by
  rw [Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace.left_area_joining, trace.left_joining_eq]

open Purelib in
open Purelib.Data in
open Purelib.Riemann.Normalization in
/-- Cache point readings from the original left primitive anchors and offsets at the exact joined trace points.

The retained owner vector uses the original left model-cell indices and certifies the same indexed point word. -/
@[expose] def
  leftReadings
  (trace : side.Trace depth) {polynomial numerator : InverseRootPolynomial.Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)) :=
  PointReadings.build anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))
    (Vector.Basic.vectorOfFn (fun vertex => trace.leftOwner (trace.vertices.indexed vertex)))
    (fun vertex => by rw [Vector.Basic.vectorOfFn_apply]; rfl)

open Purelib.Algebra in
open Purelib.Integration.Path in
/-- The retained trace's right joining area equals the original right-owner endpoint-join sum.

The bounded successor pair identifies each joining chord. The original segment endpoint certificates recover its two
right-owner primitive values without merging their owners. -/
theorem
  right_joining_eq
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) :
    JoinedTrace.VertexTrace.joiningArea (trace.rightValue values) (side.pieceVertices depth 0)
      (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) = side.rightJoins values
        := by
  rw [JoinedTrace.VertexTrace.joiningArea_ofFn]
  unfold Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.rightJoins
  apply FiniteSum.Fin.sumFin_congr
  intro column
  simp only [ObservationMesh.MatchedHorizontalSide.pieceVertices]
  rw [JoinedTrace.VertexTrace.ofIndexed_last]
  dsimp only [JoinedTrace.VertexTrace.ofIndexed, rightValue, point]
  rw [(trace.segments.get (Fin.cast left.boundaryColumns_eq column.castSucc)).last_point,
    (trace.segments.get (Fin.cast left.boundaryColumns_eq column.succ)).first_point]

open Purelib.Riemann.Periods in
/-- The exact right trace area equals the retained matched-side area plus its original endpoint joins.

The exact piece-area and joining-area equations refer to the same retained trace word. Their scalar sum preserves its
original orientation and right-owner readings. -/
theorem
  right_area
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) :
    CenteredBilinearPath.area (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) =
      side.rightArea values depth + side.rightJoins values := by
  rw [Purelib.Riemann.Paths.RectangularMatchedSideTrace.Trace.right_area_joining, trace.right_joining_eq]

open Purelib
open Purelib.Data
open Purelib.Riemann.Normalization
/-- Cache point readings from the original right primitive anchors and offsets at the exact joined trace points.

The retained owner vector uses the original right model-cell indices and certifies the same indexed point word. -/
@[expose] def
  rightReadings
  (trace : side.Trace depth) {polynomial numerator : InverseRootPolynomial.Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) :
    PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)) :=
  PointReadings.build anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))
    (Vector.Basic.vectorOfFn (fun vertex => trace.rightOwner (trace.vertices.indexed vertex)))
    (fun vertex => by rw [Vector.Basic.vectorOfFn_apply]; rfl)

/-- Each cached left reading equals the original aligned primitive value at the exact retained trace point.

The point-reading cache specializes at the original finite vertex. Its retained left owner projections are exactly the
matched piece's cell indices and cached point. -/
theorem
  leftReadings_value
  (trace : side.Trace depth) {polynomial numerator : InverseRootPolynomial.Polynomial}
    {models : Bank polynomial leftGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    (trace.leftReadings anchors offsets).values vertex =
      anchors.alignedValue offsets (side.pieces (trace.vertices.indexed vertex).1).leftColumn
        (side.pieces (trace.vertices.indexed vertex).1).leftRow (trace.point (trace.vertices.indexed vertex)) := by
  rewrite [(trace.leftReadings anchors offsets).value_eq]
  dsimp only [leftReadings, PointReadings.build]
  rewrite [Vector.Basic.vectorOfFn_apply]
  exact Eq.refl _

/-- Each cached right reading equals the original aligned primitive value at the exact retained trace point.

The point-reading cache specializes at the original finite vertex. Its retained right owner projections are exactly the
matched piece's cell indices and cached point. -/
theorem
  rightReadings_value
  (trace : side.Trace depth) {polynomial numerator : InverseRootPolynomial.Polynomial}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    (trace.rightReadings anchors offsets).values vertex =
      anchors.alignedValue offsets (side.pieces (trace.vertices.indexed vertex).1).rightColumn
        (side.pieces (trace.vertices.indexed vertex).1).rightRow (trace.point (trace.vertices.indexed vertex)) := by
  rewrite [(trace.rightReadings anchors offsets).value_eq]
  dsimp only [rightReadings, PointReadings.build]
  rewrite [Vector.Basic.vectorOfFn_apply]
  exact Eq.refl _

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

end
end

end
