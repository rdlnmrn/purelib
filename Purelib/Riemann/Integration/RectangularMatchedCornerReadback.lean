module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints
public import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationEndpoints

public section

/-! Endpoint values of matched traces are the retained exterior-corner
owners. The right trace transports its index through the certified common
interval list, rather than locating a new owner at the physical endpoint. -/

namespace Purelib.Riemann.Integration.RectangularMatchedCornerReadback

open Purelib.Geometry
open Purelib.Data

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularObservationOwners (BoxOwner)
open Purelib.Riemann.Integration.RectangularExteriorCornerOwners (exteriorCornerOwner)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox} {depth : Nat}

/-- Transport through exact interval-list equality preserves the original bounded-index interval. -/
private theorem interval_cast {first last : List Rectangle.Partition.PreparedAxisPartitions.Interval} (equal : first =
  last)
    (index : Fin first.length) :
    last[(Fin.cast (congrArg List.length equal) index).val]'(Fin.cast (congrArg List.length equal) index).isLt =
      first[index.val]'index.isLt := by
  cases equal
  rfl

namespace MatchedHorizontalSide.Trace

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace (leftValue
  rightValue)

/-- The left horizontal trace endpoint reads exactly its retained exterior-corner owner.

The original finite endpoint and side index determine the same cached corner
owner; each Boolean orientation is reduced before coordinate transport. -/
theorem left_corner {rightRow : Fin right.partition.y.intervals.length} {height : Coordinate} {above : Bool}
    {side : MatchedHorizontalSide left right
      (Fin.cast left.boundaryRows_eq (if above then Fin.last left.boundaryRows else 0)) rightRow height}
    (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (equal : height = if above then leftBox.yUpper else leftBox.yLower) (high : Bool) :
    trace.leftValue values (trace.vertices.indexed (if high then Fin.last trace.vertices.rest.length else 0)) =
      let owner := exteriorCornerOwner left high above
      values owner.column owner.row owner.point := by
  cases high <;> cases above
  all_goals
    try rewrite [if_pos (Eq.refl true)] at equal
    try rewrite [if_neg (by decide : false ≠ true)] at equal
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [leftValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext rfl left.y_first.symm)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [leftValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext rfl left.y_last.symm)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [leftValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext rfl left.y_first.symm)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [leftValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext rfl left.y_last.symm)

/-- The right horizontal trace endpoint reads exactly its retained exterior-corner owner.

The certified common interval-list equality transports the original endpoint index, preserving the original owner
instead of locating another one. -/
theorem right_corner {leftRow : Fin left.partition.y.intervals.length} {height : Coordinate} {above : Bool}
    {side : MatchedHorizontalSide left right leftRow
      (Fin.cast right.boundaryRows_eq (if above then Fin.last right.boundaryRows else 0)) height}
    (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (equal : height = if above then rightBox.yUpper else rightBox.yLower) (high : Bool) :
    trace.rightValue values (trace.vertices.indexed (if high then Fin.last trace.vertices.rest.length else 0)) =
      let owner := exteriorCornerOwner right high above
      values owner.column owner.row owner.point := by
  have firstIndex : Fin.cast (congrArg List.length side.intervals_eq) (Fin.cast left.boundaryColumns_eq 0) =
      Fin.cast right.boundaryColumns_eq 0 := Fin.ext rfl
  have lastIndex : Fin.cast (congrArg List.length side.intervals_eq) (Fin.cast left.boundaryColumns_eq (Fin.last
    left.boundaryColumns)) =
      Fin.cast right.boundaryColumns_eq (Fin.last right.boundaryColumns) :=
    Fin.ext (congrArg (fun intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval => intervals.length - 1)
      side.intervals_eq)
  have firstInterval := interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq 0)
  have lastInterval := interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq (Fin.last
    left.boundaryColumns))
  rw [firstIndex] at firstInterval
  rw [lastIndex] at lastInterval
  cases high <;> cases above
  all_goals
    try rewrite [if_pos (Eq.refl true)] at equal
    try rewrite [if_neg (by decide : false ≠ true)] at equal
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [rightValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [firstIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.lower)
        firstInterval).symm
      (equal.trans right.y_first.symm))
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [rightValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [firstIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.lower)
        firstInterval).symm
      (equal.trans right.y_last.symm))
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [rightValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [lastIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.upper)
        lastInterval).symm
      (equal.trans right.y_first.symm))
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [rightValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.horizontalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [lastIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.upper)
        lastInterval).symm
      (equal.trans right.y_last.symm))

end MatchedHorizontalSide.Trace

namespace MatchedVerticalSide.Trace

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace (leftValue
  rightValue)

/-- The left vertical trace endpoint reads exactly its retained exterior-corner owner.

The original finite endpoint and side index determine the same cached corner
owner; each Boolean orientation is reduced before coordinate transport. -/
theorem left_corner {rightColumn : Fin right.partition.x.intervals.length} {horizontal : Coordinate} {rightward : Bool}
    {side : MatchedVerticalSide left right
      (Fin.cast left.boundaryColumns_eq (if rightward then Fin.last left.boundaryColumns else 0)) rightColumn
        horizontal}
    (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (equal : horizontal = if rightward then leftBox.xUpper else leftBox.xLower) (high : Bool) :
    trace.leftValue values (trace.vertices.indexed (if high then Fin.last trace.vertices.rest.length else 0)) =
      let owner := exteriorCornerOwner left rightward high
      values owner.column owner.row owner.point := by
  cases high <;> cases rightward
  all_goals
    try rewrite [if_pos (Eq.refl true)] at equal
    try rewrite [if_neg (by decide : false ≠ true)] at equal
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [leftValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext left.x_first.symm rfl)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [leftValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext left.x_last.symm rfl)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [leftValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext left.x_first.symm rfl)
  · refine (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [leftValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [equal]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext left.x_last.symm rfl)

/-- The right vertical trace endpoint reads exactly its retained exterior-corner owner.

The certified common interval-list equality transports the original endpoint index, preserving the original owner
instead of locating another one. -/
theorem right_corner {leftColumn : Fin left.partition.x.intervals.length} {horizontal : Coordinate} {rightward : Bool}
    {side : MatchedVerticalSide left right leftColumn
      (Fin.cast right.boundaryColumns_eq (if rightward then Fin.last right.boundaryColumns else 0)) horizontal}
    (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (equal : horizontal = if rightward then rightBox.xUpper else rightBox.xLower) (high : Bool) :
    trace.rightValue values (trace.vertices.indexed (if high then Fin.last trace.vertices.rest.length else 0)) =
      let owner := exteriorCornerOwner right rightward high
      values owner.column owner.row owner.point := by
  have firstIndex : Fin.cast (congrArg List.length side.intervals_eq) (Fin.cast left.boundaryRows_eq 0) =
      Fin.cast right.boundaryRows_eq 0 := Fin.ext rfl
  have lastIndex : Fin.cast (congrArg List.length side.intervals_eq) (Fin.cast left.boundaryRows_eq (Fin.last
    left.boundaryRows)) =
      Fin.cast right.boundaryRows_eq (Fin.last right.boundaryRows) :=
    Fin.ext (congrArg (fun intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval => intervals.length - 1)
      side.intervals_eq)
  have firstInterval := interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq 0)
  have lastInterval := interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))
  rw [firstIndex] at firstInterval
  rw [lastIndex] at lastInterval
  cases high <;> cases rightward
  all_goals
    try rewrite [if_pos (Eq.refl true)] at equal
    try rewrite [if_neg (by decide : false ≠ true)] at equal
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [rightValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [firstIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext (equal.trans right.x_first.symm)
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.lower)
        firstInterval).symm)
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).trans ?_
    rw [rightValue, trace.first_point, trace.first_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [firstIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext (equal.trans right.x_last.symm)
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.lower)
        firstInterval).symm)
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [rightValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [lastIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext (equal.trans right.x_first.symm)
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.upper)
        lastInterval).symm)
  · refine (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).trans ?_
    rw [rightValue, trace.last_point, trace.last_index, side.pieces_eq]
    dsimp only [BoxOwner.verticalPiece, Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    rw [lastIndex]
    dsimp only [exteriorCornerOwner, Rectangle.Partition.PreparedRectangleCuts.corner,
      Rectangle.Partition.PreparedRectangleCuts.intervalBox]
    exact congrArg (values _ _) (Gaussian.Basic.ext (equal.trans right.x_last.symm)
      (congrArg (fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval => interval.upper)
        lastInterval).symm)

end MatchedVerticalSide.Trace
end Purelib.Riemann.Integration.RectangularMatchedCornerReadback

end
