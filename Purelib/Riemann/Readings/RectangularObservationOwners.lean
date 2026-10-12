module
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed owner lookup retains the dependent finite-index eliminator.
public import Purelib.Data.Fin
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
public import Purelib.Riemann.Paths.RectangularPairedSegments
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Riemann

public section

/-! Indexed access to the actual retained box owners, with boundary readback.
Matching clipped sides produce common trace pieces without locating new owners. -/
section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces ObservationMesh)
open Purelib.Data
open Purelib.Riemann.Integration
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (rectangles intervalBox)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (rectangleBoundary)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

namespace Purelib.Riemann.Readings.RectangularObservationOwners

set_option genInjectivity false in
/-- A rectangular model-cell owner with the exact refinement certificate for the original box.

The bounded column and row identify the retained model cell. Its refinement
certificate concerns that same supplied observation box. -/
structure BoxOwner {columns rows : Nat} (geometry : Geometry columns rows) (box : Box) where
  /-- The bounded original model-cell column. -/ column : Fin (columns + 1)
  /-- The bounded original model-cell row. -/ row : Fin (rows + 1)
  /-- The original box refines this exact retained model cell. -/ refines : box.Refines (geometry.box column row)

constructive_injectivity BoxOwner

end Purelib.Riemann.Readings.RectangularObservationOwners

section

variable {columns rows : Nat} {geometry : Geometry columns rows}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

/-- Read the original observation box's retained model-cell owner at its exact bounded list index.

Dependent coordinate elimination retains the indexed box, original column and
row, and refinement certificate. Successor coordinates read the same original
owner from the retained tail. -/
@[expose] def owner : {boxes : List Box} →
  ObservationPieces geometry boxes →
    (index : Fin boxes.length) → Readings.RectangularObservationOwners.BoxOwner geometry boxes[index]
  | _, .nil, index => Fin.elim0 index
  | box :: boxes, .cons column row refines tail, index =>
      Fin.casesDependent (motive :=
        fun index => Readings.RectangularObservationOwners.BoxOwner geometry ((box :: boxes)[index]))
        ⟨column, row, refines⟩ (fun index => tail.owner index) index

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
/-- The recursive original observation boundary equals its finite sum with exact indexed box owners. -/
theorem localBoundary_eq_indexed {boxes :
  List Box} (pieces : ObservationPieces geometry boxes)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    pieces.localBoundary values depth = FiniteSum.Fin.sumFin (fun index : Fin boxes.length =>
      PreparedBoxBoundary.rectangleBoundary (values (pieces.owner index).column (pieces.owner index).row) depth
        boxes[index]) := by
  induction pieces with
  | nil => rfl
  | cons column row refines tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change PreparedBoxBoundary.rectangleBoundary (values column row) depth _ + tail.localBoundary values depth = _
      rw [ih]
      rfl

open Purelib.Geometry.Rectangle.Partition in
/-- Recover the retained observation owner at an exact horizontal and vertical interval pair.

The original rectangle enumeration equation transports the refinement certificate to that same interval box without
changing the cell owner. -/
@[expose] def ownerAtRectangle (horizontal
  vertical : List PreparedAxisPartitions.Interval)
    (pieces : ObservationPieces geometry (PreparedRectangleCuts.rectangles horizontal vertical))
    (column : Fin horizontal.length) (row : Fin vertical.length) :
    Readings.RectangularObservationOwners.BoxOwner geometry
      (PreparedRectangleCuts.intervalBox horizontal[column] vertical[row]) :=
  let retained := pieces.owner (PreparedRectangleIndices.rectangleIndex horizontal vertical column row)
  ⟨retained.column, retained.row, by
    rw [← PreparedRectangleIndices.rectangle_at horizontal vertical column row]
    exact retained.refines⟩

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

end

section

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftBox rightBox : Box}

namespace Purelib.Riemann.Readings.RectangularObservationOwners.BoxOwner

/-- Construct a paired horizontal segment using the two original box owners and their common horizontal span.

The supplied height belongs to both boxes; their retained refinement certificates establish endpoint containment in both
original model cells. -/
@[expose] def horizontalPiece (left : BoxOwner leftGeometry leftBox) (right : BoxOwner rightGeometry rightBox)
    (lowerEq : leftBox.xLower = rightBox.xLower) (upperEq : leftBox.xUpper = rightBox.xUpper)
    (height : Coordinate) (leftInside : leftBox.yLower ≤ height ∧ height ≤ leftBox.yUpper)
    (rightInside : rightBox.yLower ≤ height ∧ height ≤ rightBox.yUpper) : PairedSegmentPiece leftGeometry rightGeometry
      :=
  ⟨left.column, left.row, right.column, right.row, ⟨leftBox.xLower, height⟩, ⟨leftBox.xUpper, height⟩,
    left.refines.contains ⟨le_rfl, leftBox.x_valid, leftInside⟩,
    left.refines.contains ⟨leftBox.x_valid, le_rfl, leftInside⟩,
    right.refines.contains (by
      change rightBox.xLower ≤ leftBox.xLower ∧ leftBox.xLower ≤ rightBox.xUpper ∧ rightBox.yLower ≤ height ∧ height ≤
        rightBox.yUpper
      rw [lowerEq]; exact ⟨le_rfl, rightBox.x_valid, rightInside⟩),
    right.refines.contains (by
      change rightBox.xLower ≤ leftBox.xUpper ∧ leftBox.xUpper ≤ rightBox.xUpper ∧ rightBox.yLower ≤ height ∧ height ≤
        rightBox.yUpper
      rw [upperEq]; exact ⟨rightBox.x_valid, le_rfl, rightInside⟩)⟩

/-- Construct a paired vertical segment using the two original box owners and their common vertical span.

The supplied horizontal coordinate belongs to both boxes; their retained refinement certificates establish endpoint
containment in both original model cells. -/
@[expose] def verticalPiece (left : BoxOwner leftGeometry leftBox) (right : BoxOwner rightGeometry rightBox)
    (lowerEq : leftBox.yLower = rightBox.yLower) (upperEq : leftBox.yUpper = rightBox.yUpper)
    (horizontal : Coordinate) (leftInside : leftBox.xLower ≤ horizontal ∧ horizontal ≤ leftBox.xUpper)
    (rightInside : rightBox.xLower ≤ horizontal ∧ horizontal ≤ rightBox.xUpper) : PairedSegmentPiece leftGeometry
      rightGeometry :=
  ⟨left.column, left.row, right.column, right.row, ⟨horizontal, leftBox.yLower⟩, ⟨horizontal, leftBox.yUpper⟩,
    left.refines.contains ⟨leftInside.1, leftInside.2, le_rfl, leftBox.y_valid⟩,
    left.refines.contains ⟨leftInside.1, leftInside.2, leftBox.y_valid, le_rfl⟩,
    right.refines.contains (by
      change rightBox.xLower ≤ horizontal ∧ horizontal ≤ rightBox.xUpper ∧ rightBox.yLower ≤ leftBox.yLower ∧
        leftBox.yLower ≤ rightBox.yUpper
      rw [lowerEq]; exact ⟨rightInside.1, rightInside.2, le_rfl, rightBox.y_valid⟩),
    right.refines.contains (by
      change rightBox.xLower ≤ horizontal ∧ horizontal ≤ rightBox.xUpper ∧ rightBox.yLower ≤ leftBox.yUpper ∧
        leftBox.yUpper ≤ rightBox.yUpper
      rw [upperEq]; exact ⟨rightInside.1, rightInside.2, rightBox.y_valid, le_rfl⟩)⟩

end Purelib.Riemann.Readings.RectangularObservationOwners.BoxOwner

end

section

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box : Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Geometry.Rectangle.Partition in
/-- Read the exact model-cell owner for the retained observation mesh's indexed interval box. -/
@[expose] def ownerAt (mesh : ObservationMesh
  cuts box)
    (column : Fin mesh.partition.x.intervals.length) (row : Fin mesh.partition.y.intervals.length) :
    Readings.RectangularObservationOwners.BoxOwner geometry
      (PreparedRectangleCuts.intervalBox mesh.partition.x.intervals[column]
      mesh.partition.y.intervals[row]) := by
  let pieces : ObservationPieces geometry
      (PreparedRectangleCuts.rectangles mesh.partition.x.intervals mesh.partition.y.intervals) :=
    mesh.partition.boxes_eq ▸ mesh.pieces
  exact pieces.ownerAtRectangle mesh.partition.x.intervals mesh.partition.y.intervals column row

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end

end

end
