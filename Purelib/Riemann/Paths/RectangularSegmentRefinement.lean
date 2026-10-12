module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.List.Map

import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions

public section

/-! Assign whole fine intervals to retained segment pieces. Location uses
the cached split once; the retained cuts certify both interval endpoints. -/
namespace Purelib.Riemann.Paths.RectangularSegmentRefinement

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}
  {first last : Gaussian}

open Purelib.Geometry in
set_option genInjectivity false in
/-- A fine interval contained in a retained segment piece.

The record retains the exact piece, its original list membership and inequalities certifying both endpoints. -/
structure Subinterval (split : SegmentSplit cuts first last) (interval :
  Rectangle.Partition.PreparedAxisPartitions.Interval) where
  /-- The retained model-owned segment piece containing the interval. -/ piece : SegmentPiece geometry first last
  /-- The piece belongs to the original split's ordered list. -/ member : piece ∈ split.pieces
  /-- The piece begins no later than the fine interval. -/ lower : piece.interval.lower ≤ interval.lower
  /-- The fine interval ends no later than the piece. -/ upper : interval.upper ≤ piece.interval.upper

constructive_injectivity Subinterval

open Purelib.Geometry in
/-- Every parameter in the fine interval lies in the retained containing piece.

The two stored endpoint inequalities transport the supplied parameter bounds to the same retained piece. No interval or
owner is recomputed. -/
theorem Subinterval.contains {split : SegmentSplit cuts first last} {interval :
  Rectangle.Partition.PreparedAxisPartitions.Interval}
    (located : Subinterval split interval) {parameter : Coordinate}
    (inside : interval.lower ≤ parameter ∧ parameter ≤ interval.upper) :
    located.piece.interval.lower ≤ parameter ∧ parameter ≤ located.piece.interval.upper :=
  ⟨located.lower.trans inside.1, inside.2.trans located.upper⟩

open Purelib.Data in
open Purelib.Polynomial in
/-- Both endpoints of a retained piece belong to the split's cached partition coordinates.

The original piece membership transports through the cached interval list. Adjacent interval endpoint membership then
refers to the same retained partition coordinates. -/
theorem endpoints_coordinates (split : SegmentSplit cuts first last)
    {piece : SegmentPiece geometry first last} (member : piece ∈ split.pieces) :
    piece.interval.lower ∈ split.partition.coordinates ∧ piece.interval.upper ∈ split.partition.coordinates := by
  have present := List.Map.mem_map_of_mem (f := SegmentPiece.interval) member
  rw [split.intervals_eq, split.partition.intervals_eq] at present
  exact Geometry.Grid.ClearGrid.Interval.endpoints_mem _ _ present

open Purelib.Data in
open Purelib.Geometry in
/-- Every partition-coordinate point belongs to the split's retained geometric point list.

The partition endpoint certificate selects an original piece and one of its two endpoints. Its exact affine readback
transports the retained endpoint membership to the requested coordinate. -/
theorem coordinate_point_mem (split : SegmentSplit cuts first last) {parameter : Coordinate}
    (member : parameter ∈ split.partition.coordinates) : Rectangle.Partition.PreparedSegmentCuts.point first last
      parameter ∈ split.points := by
  let endpoint := split.partition.endpoint parameter member
  have present := endpoint.member
  rw [← split.intervals_eq] at present
  obtain ⟨piece, inPieces, equal⟩ := List.Map.mem_map.mp present
  have equalPoint := endpoint.endpoint_eq
  rw [← equal] at equalPoint
  cases high : endpoint.high with
  | false =>
    rewrite [high, if_neg (show ¬(false = true) from by decide)] at equalPoint
    have found := (split.points_mem inPieces).1
    rw [piece.first_eq, equalPoint] at found
    exact found
  | true =>
    rewrite [high, if_pos (Eq.refl true)] at equalPoint
    have found := (split.points_mem inPieces).2
    rw [piece.last_eq, equalPoint] at found
    exact found

open Purelib.Geometry in
/-- Locate a fine interval in the original cached segment split.

The interval lies in the unit range and no retained partition boundary crosses its interior; a single midpoint lookup
therefore certifies the whole interval. -/
@[expose] def locateInterval (split : SegmentSplit cuts first last) (interval :
  Rectangle.Partition.PreparedAxisPartitions.Interval)
    (within : 0 ≤ interval.lower ∧ interval.upper ≤ 1)
    (outside : ∀ coordinate ∈ split.partition.coordinates,
      coordinate ≤ interval.lower ∨ interval.upper ≤ coordinate) : Subinterval split interval :=
  let middle := (interval.lower + interval.upper) / 2
  have between := Rectangle.Partition.PreparedSegmentCuts.midpoint_bounds interval
  let located := split.locate middle ⟨within.1.trans between.1.le, between.2.le.trans within.2⟩
  have endpoints := endpoints_coordinates split located.member
  { piece := located.piece
    member := located.member
    lower := by
      rcases outside _ endpoints.1 with lower | above
      · exact lower
      · exact (not_lt_of_ge (above.trans located.inside.1) between.2).elim
    upper := by
      rcases outside _ endpoints.2 with below | upper
      · exact (not_lt_of_ge (located.inside.2.trans below) between.1).elim
      · exact upper }

end Purelib.Riemann.Paths.RectangularSegmentRefinement

end
