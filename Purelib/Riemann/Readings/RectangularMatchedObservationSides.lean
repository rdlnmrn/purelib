module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Integration.RectangularClippedSeamGeometry
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-! Whole common-cut sides retain both original face owners on every interval.
The side readback consumes the same recursive boundaries as the exterior. -/
namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)

open Purelib.Geometry.Rectangle.Partition in
/-- The exact interval at an index is preserved by transport along equality of the original interval lists. -/
public theorem interval_cast {first last : List PreparedAxisPartitions.Interval} (equal : first = last)
    (index : Fin first.length) : last[Fin.cast (congrArg List.length equal) index] = first[index] := by
  cases equal
  rfl

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}

namespace ObservationMesh

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
set_option genInjectivity false in
/-- Cached paired horizontal pieces shared by two original observation meshes at a fixed height.

The exact horizontal partition equality transports right-hand indices, while separate containment certificates retain
both original row owners. -/
structure MatchedHorizontalSide (left : ObservationMesh leftCuts leftBox) (right : ObservationMesh rightCuts rightBox)
    (leftRow : Fin left.partition.y.intervals.length) (rightRow : Fin right.partition.y.intervals.length) (height :
      Coordinate) where
  /-- The two original observation meshes retain exactly the same varying-axis interval list. -/ intervals_eq :
    left.partition.x.intervals = right.partition.x.intervals
  /-- The fixed coordinate lies in the original left-hand owner interval. -/ left_inside :
    left.partition.y.intervals[leftRow].lower ≤ height ∧ height ≤ left.partition.y.intervals[leftRow].upper
  /-- The fixed coordinate lies in the original right-hand owner interval. -/ right_inside :
    right.partition.y.intervals[rightRow].lower ≤ height ∧ height ≤ right.partition.y.intervals[rightRow].upper
  /-- The cached paired pieces at the exact original interval indices. -/ pieces : Data.Vector
    (PairedSegmentPiece leftGeometry rightGeometry) left.partition.x.intervals.length
  /-- Each cached piece equals the construction from both original model owners and the retained partition equality. -/
    pieces_eq : ∀ index, pieces index =
    (left.ownerAt index leftRow).horizontalPiece
      (right.ownerAt (Fin.cast (congrArg List.length intervals_eq) index) rightRow)
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast intervals_eq
        index)).symm
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast intervals_eq
        index)).symm
      height left_inside right_inside

constructive_injectivity MatchedHorizontalSide

namespace MatchedHorizontalSide

variable {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
    Coordinate}

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
/-- Cache the paired interval pieces from the two original observation owners and exact partition equality.

Each piece retains both model-cell indices and its separate endpoint-containment certificates; the vector readback
equation identifies that exact construction. -/
def build (left : ObservationMesh leftCuts leftBox) (right : ObservationMesh rightCuts rightBox)
    (leftRow : Fin left.partition.y.intervals.length) (rightRow : Fin right.partition.y.intervals.length) (height :
      Coordinate)
    (intervalsEq : left.partition.x.intervals = right.partition.x.intervals)
    (leftInside : left.partition.y.intervals[leftRow].lower ≤ height ∧ height ≤
      left.partition.y.intervals[leftRow].upper)
    (rightInside : right.partition.y.intervals[rightRow].lower ≤ height ∧ height ≤
      right.partition.y.intervals[rightRow].upper) :
    MatchedHorizontalSide left right leftRow rightRow height :=
  ⟨intervalsEq, leftInside, rightInside,
    Vector.Basic.vectorOfFn (fun index => (left.ownerAt index leftRow).horizontalPiece
      (right.ownerAt (Fin.cast (congrArg List.length intervalsEq) index) rightRow)
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast intervalsEq
        index)).symm
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast intervalsEq
        index)).symm height leftInside rightInside),
    fun index => Vector.Basic.vectorOfFn_apply _ index⟩

/-- The retained paired piece starts at the original interval's lower endpoint. -/
theorem first_eq (side : MatchedHorizontalSide left right leftRow rightRow height)
    (index : Fin left.partition.x.intervals.length) :
    (side.pieces index).first = ⟨left.partition.x.intervals[index].lower, height⟩ := by
  rw [side.pieces_eq]
  rfl

/-- The retained paired piece finishes at the original interval's upper endpoint. -/
theorem last_eq (side : MatchedHorizontalSide left right leftRow rightRow height)
    (index : Fin left.partition.x.intervals.length) :
    (side.pieces index).last = ⟨left.partition.x.intervals[index].upper, height⟩ := by
  rw [side.pieces_eq]
  rfl

open Purelib.Data.Gaussian in
/-- Consecutive retained paired pieces meet at the same original interval endpoint. -/
theorem consecutive (side : MatchedHorizontalSide left right leftRow rightRow height)
    (index : Nat) (later : index + 1 < left.partition.x.intervals.length) :
    (side.pieces ⟨index, Nat.lt_trans (Nat.lt_succ_self _) later⟩).last =
      (side.pieces ⟨index + 1, later⟩).first := by
  rw [side.last_eq, side.first_eq]
  apply Basic.ext
  · exact left.partition.x.consecutive index later
  · rfl

section
open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
/-- Sum the matched side's primitive boundary areas using the original left-hand owners. -/
def leftArea (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index => PreparedBoxBoundary.horizontalBoundary
    (values (side.pieces index).leftColumn (side.pieces index).leftRow) depth
    (side.pieces index).first.re (side.pieces index).last.re height)

/-- Sum the matched side's primitive boundary areas using the original right-hand owners. -/
def rightArea (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index => PreparedBoxBoundary.horizontalBoundary
    (values (side.pieces index).rightColumn (side.pieces index).rightRow) depth
    (side.pieces index).first.re (side.pieces index).last.re height)

/-- The matched side's left area reads back the original left mesh's indexed interval boundaries. -/
theorem leftArea_eq (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    side.leftArea values depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.x.intervals.length =>
      PreparedBoxBoundary.horizontalBoundary (values (left.ownerAt index leftRow).column (left.ownerAt index
        leftRow).row)
        depth left.partition.x.intervals[index].lower left.partition.x.intervals[index].upper height) := by
  unfold leftArea
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [side.pieces_eq]
  rfl

/-- The matched side's right area reads back the original right mesh's indexed interval boundaries.

The exact partition equality transports bounded indices while preserving the original right-hand model owners and
endpoint coordinates. -/
theorem rightArea_eq (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    side.rightArea values depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.x.intervals.length =>
      PreparedBoxBoundary.horizontalBoundary (values (right.ownerAt index rightRow).column (right.ownerAt index
        rightRow).row)
        depth right.partition.x.intervals[index].lower right.partition.x.intervals[index].upper height) := by
  have readback : side.rightArea values depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.x.intervals.length
    =>
      PreparedBoxBoundary.horizontalBoundary
        (values (right.ownerAt (Fin.cast (congrArg List.length side.intervals_eq) index) rightRow).column
          (right.ownerAt (Fin.cast (congrArg List.length side.intervals_eq) index) rightRow).row)
        depth right.partition.x.intervals[Fin.cast (congrArg List.length side.intervals_eq) index].lower
          right.partition.x.intervals[Fin.cast (congrArg List.length side.intervals_eq) index].upper height) := by
    unfold rightArea
    apply FiniteSum.Fin.sumFin_congr
    intro index
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast
      side.intervals_eq index)
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast
      side.intervals_eq index)
    rw [lower, upper, side.pieces_eq]
    rfl
  rw [readback]
  have cast_sum {first last : Nat} (equal : first = last) (values : Fin last → Gaussian) :
      FiniteSum.Fin.sumFin (fun index : Fin first => values (Fin.cast equal index)) = FiniteSum.Fin.sumFin values := by
    cases equal
    rfl
  exact cast_sum (congrArg List.length side.intervals_eq)
    (fun index : Fin right.partition.x.intervals.length => PreparedBoxBoundary.horizontalBoundary
      (values (right.ownerAt index rightRow).column (right.ownerAt index rightRow).row) depth
      right.partition.x.intervals[index].lower right.partition.x.intervals[index].upper height)

end

open Purelib.Algebra
/-- At the left mesh's lower height, the matched area equals its original bottom-side sum. -/
theorem leftArea_eq_bottom (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (equal : height = left.partition.y.intervals[leftRow].lower) :
    side.leftArea values left.depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.x.intervals.length =>
      (left.cellSides values index leftRow).bottom) := by
  rw [side.leftArea_eq, equal]
  rfl

/-- At the left mesh's upper height, the matched area equals its original top-side sum. -/
theorem leftArea_eq_top (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (equal : height = left.partition.y.intervals[leftRow].upper) :
    side.leftArea values left.depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.x.intervals.length =>
      (left.cellSides values index leftRow).top) := by
  rw [side.leftArea_eq, equal]
  rfl

/-- At the right mesh's lower height, the matched area equals its original bottom-side sum. -/
theorem rightArea_eq_bottom (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (equal : height = right.partition.y.intervals[rightRow].lower) :
    side.rightArea values right.depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.x.intervals.length =>
      (right.cellSides values index rightRow).bottom) := by
  rw [side.rightArea_eq, equal]
  rfl

/-- At the right mesh's upper height, the matched area equals its original top-side sum. -/
theorem rightArea_eq_top (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (equal : height = right.partition.y.intervals[rightRow].upper) :
    side.rightArea values right.depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.x.intervals.length =>
      (right.cellSides values index rightRow).top) := by
  rw [side.rightArea_eq, equal]
  rfl

end MatchedHorizontalSide
open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
set_option genInjectivity false in
/-- Cached paired vertical pieces shared by two original observation meshes at a fixed horizontal coordinate.

The exact vertical partition equality transports right-hand indices, while separate containment certificates retain both
original column owners. -/
structure MatchedVerticalSide (left : ObservationMesh leftCuts leftBox) (right : ObservationMesh rightCuts rightBox)
    (leftColumn : Fin left.partition.x.intervals.length) (rightColumn : Fin right.partition.x.intervals.length)
      (horizontal : Coordinate) where
  /-- The two original observation meshes retain exactly the same varying-axis interval list. -/ intervals_eq :
    left.partition.y.intervals = right.partition.y.intervals
  /-- The fixed coordinate lies in the original left-hand owner interval. -/ left_inside :
    left.partition.x.intervals[leftColumn].lower ≤ horizontal ∧ horizontal ≤
    left.partition.x.intervals[leftColumn].upper
  /-- The fixed coordinate lies in the original right-hand owner interval. -/ right_inside :
    right.partition.x.intervals[rightColumn].lower ≤ horizontal ∧ horizontal ≤
    right.partition.x.intervals[rightColumn].upper
  /-- The cached paired pieces at the exact original interval indices. -/ pieces : Data.Vector
    (PairedSegmentPiece leftGeometry rightGeometry) left.partition.y.intervals.length
  /-- Each cached piece equals the construction from both original model owners and the retained partition equality. -/
    pieces_eq : ∀ index, pieces index =
    (left.ownerAt leftColumn index).verticalPiece
      (right.ownerAt rightColumn (Fin.cast (congrArg List.length intervals_eq) index))
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast intervals_eq
        index)).symm
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast intervals_eq
        index)).symm
      horizontal left_inside right_inside

constructive_injectivity MatchedVerticalSide

namespace MatchedVerticalSide

variable {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : Coordinate}

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
/-- Cache the paired interval pieces from the two original observation owners and exact partition equality.

Each piece retains both model-cell indices and its separate endpoint-containment certificates; the vector readback
equation identifies that exact construction. -/
def build (left : ObservationMesh leftCuts leftBox) (right : ObservationMesh rightCuts rightBox)
    (leftColumn : Fin left.partition.x.intervals.length) (rightColumn : Fin right.partition.x.intervals.length)
      (horizontal : Coordinate)
    (intervalsEq : left.partition.y.intervals = right.partition.y.intervals)
    (leftInside : left.partition.x.intervals[leftColumn].lower ≤ horizontal ∧ horizontal ≤
      left.partition.x.intervals[leftColumn].upper)
    (rightInside : right.partition.x.intervals[rightColumn].lower ≤ horizontal ∧ horizontal ≤
      right.partition.x.intervals[rightColumn].upper) :
    MatchedVerticalSide left right leftColumn rightColumn horizontal :=
  ⟨intervalsEq, leftInside, rightInside,
    Vector.Basic.vectorOfFn (fun index => (left.ownerAt leftColumn index).verticalPiece
      (right.ownerAt rightColumn (Fin.cast (congrArg List.length intervalsEq) index))
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast intervalsEq
        index)).symm
      (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast intervalsEq
        index)).symm horizontal leftInside rightInside),
    fun index => Vector.Basic.vectorOfFn_apply _ index⟩

/-- The retained paired piece starts at the original interval's lower endpoint. -/
theorem first_eq (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (index : Fin left.partition.y.intervals.length) :
    (side.pieces index).first = ⟨horizontal, left.partition.y.intervals[index].lower⟩ := by
  rw [side.pieces_eq]
  rfl

/-- The retained paired piece finishes at the original interval's upper endpoint. -/
theorem last_eq (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (index : Fin left.partition.y.intervals.length) :
    (side.pieces index).last = ⟨horizontal, left.partition.y.intervals[index].upper⟩ := by
  rw [side.pieces_eq]
  rfl

open Purelib.Data.Gaussian in
/-- Consecutive retained paired pieces meet at the same original interval endpoint. -/
theorem consecutive (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (index : Nat) (later : index + 1 < left.partition.y.intervals.length) :
    (side.pieces ⟨index, Nat.lt_trans (Nat.lt_succ_self _) later⟩).last =
      (side.pieces ⟨index + 1, later⟩).first := by
  rw [side.last_eq, side.first_eq]
  apply Basic.ext
  · rfl
  · exact left.partition.y.consecutive index later

section
open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
/-- Sum the matched side's primitive boundary areas using the original left-hand owners. -/
def leftArea (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index => PreparedBoxBoundary.verticalBoundary
    (values (side.pieces index).leftColumn (side.pieces index).leftRow) depth
    (side.pieces index).first.im (side.pieces index).last.im horizontal)

/-- Sum the matched side's primitive boundary areas using the original right-hand owners. -/
def rightArea (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index => PreparedBoxBoundary.verticalBoundary
    (values (side.pieces index).rightColumn (side.pieces index).rightRow) depth
    (side.pieces index).first.im (side.pieces index).last.im horizontal)

/-- The matched side's left area reads back the original left mesh's indexed interval boundaries. -/
theorem leftArea_eq (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    side.leftArea values depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.y.intervals.length =>
      PreparedBoxBoundary.verticalBoundary (values (left.ownerAt leftColumn index).column (left.ownerAt leftColumn
        index).row)
        depth left.partition.y.intervals[index].lower left.partition.y.intervals[index].upper horizontal) := by
  unfold leftArea
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [side.pieces_eq]
  rfl

/-- The matched side's right area reads back the original right mesh's indexed interval boundaries.

The exact partition equality transports bounded indices while preserving the original right-hand model owners and
endpoint coordinates. -/
theorem rightArea_eq (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    side.rightArea values depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.y.intervals.length =>
      PreparedBoxBoundary.verticalBoundary (values (right.ownerAt rightColumn index).column (right.ownerAt rightColumn
        index).row)
        depth right.partition.y.intervals[index].lower right.partition.y.intervals[index].upper horizontal) := by
  have readback : side.rightArea values depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.y.intervals.length
    =>
      PreparedBoxBoundary.verticalBoundary
        (values (right.ownerAt rightColumn (Fin.cast (congrArg List.length side.intervals_eq) index)).column
          (right.ownerAt rightColumn (Fin.cast (congrArg List.length side.intervals_eq) index)).row)
        depth right.partition.y.intervals[Fin.cast (congrArg List.length side.intervals_eq) index].lower
          right.partition.y.intervals[Fin.cast (congrArg List.length side.intervals_eq) index].upper horizontal) := by
    unfold rightArea
    apply FiniteSum.Fin.sumFin_congr
    intro index
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower) (interval_cast
      side.intervals_eq index)
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper) (interval_cast
      side.intervals_eq index)
    rw [lower, upper, side.pieces_eq]
    rfl
  rw [readback]
  have cast_sum {first last : Nat} (equal : first = last) (values : Fin last → Gaussian) :
      FiniteSum.Fin.sumFin (fun index : Fin first => values (Fin.cast equal index)) = FiniteSum.Fin.sumFin values := by
    cases equal
    rfl
  exact cast_sum (congrArg List.length side.intervals_eq)
    (fun index : Fin right.partition.y.intervals.length => PreparedBoxBoundary.verticalBoundary
      (values (right.ownerAt rightColumn index).column (right.ownerAt rightColumn index).row) depth
      right.partition.y.intervals[index].lower right.partition.y.intervals[index].upper horizontal)

end

open Purelib.Algebra
/-- At the left mesh's lower horizontal coordinate, the matched area equals its original left-side sum. -/
theorem leftArea_eq_left (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (equal : horizontal = left.partition.x.intervals[leftColumn].lower) :
    side.leftArea values left.depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.y.intervals.length =>
      (left.cellSides values leftColumn index).left) := by
  rw [side.leftArea_eq, equal]
  rfl

/-- At the left mesh's upper horizontal coordinate, the matched area equals its original right-side sum. -/
theorem leftArea_eq_right (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (equal : horizontal = left.partition.x.intervals[leftColumn].upper) :
    side.leftArea values left.depth = FiniteSum.Fin.sumFin (fun index : Fin left.partition.y.intervals.length =>
      (left.cellSides values leftColumn index).right) := by
  rw [side.leftArea_eq, equal]
  rfl

/-- At the right mesh's lower horizontal coordinate, the matched area equals its original left-side sum. -/
theorem rightArea_eq_left (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (equal : horizontal = right.partition.x.intervals[rightColumn].lower) :
    side.rightArea values right.depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.y.intervals.length =>
      (right.cellSides values rightColumn index).left) := by
  rw [side.rightArea_eq, equal]
  rfl

/-- At the right mesh's upper horizontal coordinate, the matched area equals its original right-side sum. -/
theorem rightArea_eq_right (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (equal : horizontal = right.partition.x.intervals[rightColumn].upper) :
    side.rightArea values right.depth = FiniteSum.Fin.sumFin (fun index : Fin right.partition.y.intervals.length =>
      (right.cellSides values rightColumn index).right) := by
  rw [side.rightArea_eq, equal]
  rfl

end MatchedVerticalSide
end ObservationMesh
end Purelib.Riemann.Readings.RectangularMatchedObservationSides
