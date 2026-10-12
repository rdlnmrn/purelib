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
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The actual horizontal trace is ordered, including its zero-length joins. -/
namespace Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
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
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace (point)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide (pieceVertices)

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
  {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
    Coordinate}
  {side : MatchedHorizontalSide left right leftRow rightRow height} {depth : Nat}

/-- The retained horizontal trace coordinate is the original interval's affine dyadic reading. -/
theorem point_horizontal (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (vertex : Fin (dyadicCount depth + 1)) :
    (trace.point (column, vertex)).re = left.partition.x.intervals[column].lower +
      (left.partition.x.intervals[column].upper - left.partition.x.intervals[column].lower) *
        DyadicTrace.indexed 0 (DyadicTrace.tail depth 0 1) vertex := by
  rw [point, trace.segments_eq, dyadic_points, side.first_eq, side.last_eq]
  simp only [Affine.line, Basic.add_re, Basic.mul_re, Basic.sub_re, Basic.sub_im,
    Cast.ofCoordinate_re, Cast.ofCoordinate_im]
  ring1

/-- Every point of the exact matched horizontal trace has its original retained height. -/
theorem point_height (trace : side.Trace depth) (vertex : side.Vertex depth) :
    (trace.point vertex).im = height := by
  rcases vertex with ⟨column, vertex⟩
  rw [point, trace.segments_eq, dyadic_points, side.first_eq, side.last_eq]
  simp only [Affine.line, Basic.add_im, Basic.mul_im, Basic.sub_re, Basic.sub_im,
    Cast.ofCoordinate_re, Cast.ofCoordinate_im]
  ring1

open Purelib.Data.Rat in
/-- Each original horizontal interval's dyadic trace is ordered by horizontal coordinate.

The retained interval endpoints supply a nonnegative affine scale. The same
ordered dyadic parameter edges preserve the original coordinate comparison. -/
private theorem piece_ordered (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1)) :
    TraceLengths.VertexTrace.Ordered (side.pieceVertices depth column)
      (fun vertex => (trace.point vertex).re) := by
  apply TraceLengths.VertexTrace.ordered_ofIndexed
  intro edge
  rw [RectangularHorizontalTraceLengths.point_horizontal,
    RectangularHorizontalTraceLengths.point_horizontal]
  have parameters := TraceLengths.Dyadic.forward_indexed id 0 (DyadicTrace.tail depth 0 1)
    (TraceLengths.Dyadic.tail_forward depth (by decide)) edge
  exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parameters
      (Fraction.Order.Arithmetic.sub_nonneg_direct (left.partition.x.intervals[Fin.cast left.boundaryColumns_eq
        column]).ordered.le))

/-- The joined original matched-side trace is ordered by horizontal coordinate.

Each exact dyadic piece is monotone, and the original consecutive endpoint identities join neighboring intervals without
changing their retained bounded indices. -/
theorem ordered (trace : side.Trace depth) :
    TraceLengths.VertexTrace.Ordered trace.vertices
      (fun vertex => (trace.point vertex).re) := by
  rw [trace.vertices_eq]
  apply TraceLengths.VertexTrace.ordered_concatenate _ _ (piece_ordered trace)
  intro edge
  rw [pieceVertices, JoinedTrace.VertexTrace.ofIndexed_last]
  change (trace.point (Fin.cast left.boundaryColumns_eq edge.castSucc, Fin.last (dyadicCount depth))).re ≤
    (trace.point (Fin.cast left.boundaryColumns_eq edge.succ, 0)).re
  change ((trace.segments.get _).points _).re ≤ ((trace.segments.get _).points _).re
  rw [(trace.segments.get _).last_point, (trace.segments.get _).first_point]
  have later : edge.val + 1 < left.partition.x.intervals.length :=
    (Nat.succ_lt_succ edge.isLt).trans_eq left.boundaryColumns_eq
  exact le_of_eq (congrArg (fun point : Gaussian => point.re) (side.consecutive edge.val later))

/-- Cache the nonnegative horizontal edge lengths of the exact original joined trace. -/
@[expose] def lengths (trace : side.Trace depth) :
    TraceLengths.VertexTrace.Lengths trace.vertices (fun vertex => (trace.point vertex).re) :=
  TraceLengths.VertexTrace.Lengths.build trace.vertices _ (ordered trace)

/-- Each original horizontal trace edge's squared Gaussian movement equals its retained coordinate length squared. -/
theorem length_movement (trace : side.Trace depth)
    (lengths : TraceLengths.VertexTrace.Lengths trace.vertices
      (fun vertex => (trace.point vertex).re))
    (edge : Fin trace.vertices.rest.length) :
    normSq (trace.point (trace.vertices.indexed edge.succ) - trace.point (trace.vertices.indexed edge.castSucc)) =
      (lengths.values edge)^2 := by
  rw [lengths.values_eq]
  simp only [normSq, Basic.sub_re, Basic.sub_im, RectangularHorizontalTraceLengths.point_height]
  ring1

end Purelib.Riemann.Paths.RectangularHorizontalTraceLengths

end
