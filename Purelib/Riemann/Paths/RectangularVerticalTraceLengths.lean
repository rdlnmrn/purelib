module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine

import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
public import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.Vector.Dependent
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The actual vertical trace is ordered, including its zero-length joins. -/
namespace Purelib.Riemann.Paths.RectangularVerticalTraceLengths
open Purelib.Riemann.Paths
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace (point)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide (pieceVertices)

open Purelib.Riemann.Periods.CenteredBilinearPath
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount dyadic_points)
open Purelib.Integration.Path.TraceLengths.VertexTrace (ordered_ofIndexed ordered_concatenate)
open Purelib.Integration.Path.TraceLengths.VertexTrace.Lengths (build)
open Purelib.Integration.Path.TraceLengths.Dyadic (forward_indexed tail_forward)
open Purelib.Data.Gaussian.Basic.Canonical

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : Coordinate}
  {side : MatchedVerticalSide left right leftColumn rightColumn horizontal} {depth : Nat}

/-- The retained vertical trace coordinate is the original interval's affine dyadic reading. -/
theorem point_vertical (trace : side.Trace depth) (column : Fin left.partition.y.intervals.length)
    (vertex : Fin (dyadicCount depth + 1)) :
    (trace.point (column, vertex)).im = left.partition.y.intervals[column].lower +
      (left.partition.y.intervals[column].upper - left.partition.y.intervals[column].lower) *
        DyadicTrace.indexed 0 (DyadicTrace.tail depth 0 1) vertex := by
  rw [point, trace.segments_eq, dyadic_points, side.first_eq, side.last_eq]
  simp only [Affine.line, Basic.add_im, Basic.mul_im, Basic.sub_re, Basic.sub_im,
    Cast.ofCoordinate_re, Cast.ofCoordinate_im]
  ring1

/-- Every point of the exact matched vertical trace has its original retained horizontal coordinate. -/
theorem point_horizontal (trace : side.Trace depth) (vertex : side.Vertex depth) :
    (trace.point vertex).re = horizontal := by
  rcases vertex with ⟨column, vertex⟩
  rw [point, trace.segments_eq, dyadic_points, side.first_eq, side.last_eq]
  simp only [Affine.line, Basic.add_re, Basic.mul_re, Basic.sub_re, Basic.sub_im,
    Cast.ofCoordinate_re, Cast.ofCoordinate_im]
  ring1

open Purelib.Data.Rat in
/-- Each original vertical interval's dyadic trace is ordered by vertical coordinate.

The retained interval endpoints supply a nonnegative affine scale. The same
ordered dyadic parameter edges preserve the original coordinate comparison. -/
private theorem piece_ordered (trace : side.Trace depth) (column : Fin (left.boundaryRows + 1)) :
    TraceLengths.VertexTrace.Ordered (side.pieceVertices depth column)
      (fun vertex => (trace.point vertex).im) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  rw [RectangularVerticalTraceLengths.point_vertical,
    RectangularVerticalTraceLengths.point_vertical]
  have parameters := TraceLengths.Dyadic.forward_indexed id 0
    (DyadicTrace.tail depth 0 1)
    (TraceLengths.Dyadic.tail_forward depth (by decide)) edge
  exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parameters
      (Fraction.Order.Arithmetic.sub_nonneg_direct (left.partition.y.intervals[Fin.cast left.boundaryRows_eq
        column]).ordered.le))

/-- The joined original matched-side trace is ordered by vertical coordinate.

Each exact dyadic piece is monotone, and the original consecutive endpoint identities join neighboring intervals without
changing their retained bounded indices. -/
theorem ordered (trace : side.Trace depth) :
    TraceLengths.VertexTrace.Ordered trace.vertices
      (fun vertex => (trace.point vertex).im) := by
  rw [trace.vertices_eq]
  apply TraceLengths.VertexTrace.ordered_concatenate _ _ (piece_ordered trace)
  intro edge
  rw [pieceVertices, JoinedTrace.VertexTrace.ofIndexed_last]
  change (trace.point (Fin.cast left.boundaryRows_eq edge.castSucc, Fin.last (dyadicCount depth))).im ≤
    (trace.point (Fin.cast left.boundaryRows_eq edge.succ, 0)).im
  change ((trace.segments.get _).points _).im ≤ ((trace.segments.get _).points _).im
  rw [(trace.segments.get _).last_point, (trace.segments.get _).first_point]
  have later : edge.val + 1 < left.partition.y.intervals.length :=
    (Nat.succ_lt_succ edge.isLt).trans_eq left.boundaryRows_eq
  exact le_of_eq (congrArg (fun point : Gaussian => point.im) (side.consecutive edge.val later))

/-- Cache the nonnegative vertical edge lengths of the exact original joined trace. -/
@[expose] def lengths (trace : side.Trace depth) :
    TraceLengths.VertexTrace.Lengths trace.vertices (fun vertex => (trace.point vertex).im) :=
  TraceLengths.VertexTrace.Lengths.build trace.vertices _ (ordered trace)

/-- Each original vertical trace edge's squared Gaussian movement equals its retained coordinate length squared. -/
theorem length_movement (trace : side.Trace depth)
    (lengths : TraceLengths.VertexTrace.Lengths trace.vertices
      (fun vertex => (trace.point vertex).im))
    (edge : Fin trace.vertices.rest.length) :
    normSq (trace.point (trace.vertices.indexed edge.succ) - trace.point (trace.vertices.indexed edge.castSucc)) =
      (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [normSq, Basic.sub_re, Basic.sub_im, RectangularVerticalTraceLengths.point_horizontal]
  ring1

end Purelib.Riemann.Paths.RectangularVerticalTraceLengths

end
