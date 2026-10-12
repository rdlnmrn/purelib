module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-! Read whole matched traces back into the cached face perimeter. -/
section

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}

namespace Purelib.Riemann.Integration.RectangularMatchedPerimeter

open Purelib.Algebra in
/-- Transporting bounded indices along count equality preserves the original finite sum. -/
private theorem
  sum_cast
    {n m : Nat} (equal : n = m) (f : Fin m → Gaussian) :
    FiniteSum.Fin.sumFin f = FiniteSum.Fin.sumFin (fun i => f (Fin.cast equal i)) := by
  cases equal
  rfl

open Purelib.Geometry.Rectangle.Partition in
/-- Transporting a bounded index along interval-list equality preserves its original interval. -/
private theorem
  interval_cast
    {first last : List PreparedAxisPartitions.Interval} (equal : first = last)
    (index : Fin first.length) : last[Fin.cast (congrArg List.length equal) index] = first[index] := by
  cases equal
  rfl

end Purelib.Riemann.Integration.RectangularMatchedPerimeter

section

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide (leftJoins
  rightJoins)

variable {rightRow : Fin right.partition.y.intervals.length} {height : Coordinate}

section
open Purelib.Algebra

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

/-- The matched left area and its original joins equal the retained bottom perimeter at the lower boundary. -/
theorem
  left_boundary_eq_bottom
    (side : MatchedHorizontalSide left right
      (Fin.cast left.boundaryRows_eq (0)) rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : height = left.partition.y.intervals[Fin.cast left.boundaryRows_eq (0)].lower) :
    side.leftArea values left.depth + side.leftJoins values = perimeter.bottom := by
  rw [perimeter.bottom_eq, side.leftArea_eq_bottom values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast left.boundaryColumns_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [assembly.sides_eq]
    rfl
  · unfold leftJoins
    apply FiniteSum.Fin.sumFin_congr
    intro column
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨_, height⟩)
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨_, height⟩) = _
    rw [equal]
    rfl

/-- The matched left area and its original joins equal the retained top perimeter at the upper boundary. -/
theorem
  left_boundary_eq_top
    (side : MatchedHorizontalSide left right
      (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)) rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : height = left.partition.y.intervals[Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)].upper) :
    side.leftArea values left.depth + side.leftJoins values = perimeter.top := by
  rw [perimeter.top_eq, side.leftArea_eq_top values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast left.boundaryColumns_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro column
    rw [assembly.sides_eq]
    rfl
  · unfold leftJoins
    apply FiniteSum.Fin.sumFin_congr
    intro column
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨_, height⟩)
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨_, height⟩) = _
    rw [equal]
    rfl

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

end

section
open Purelib.Riemann.Periods

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

/-- The original matched trace's left area equals the retained bottom perimeter at its own mesh depth. -/
theorem
  left_area_eq_bottom
    {side : MatchedHorizontalSide left right
      (Fin.cast left.boundaryRows_eq (0)) rightRow height}
    (trace : side.Trace left.depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : height = left.partition.y.intervals[Fin.cast left.boundaryRows_eq (0)].lower) :
    CenteredBilinearPath.area
      (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) = perimeter.bottom := by
  rw [trace.left_area]
  exact side.left_boundary_eq_bottom values assembly perimeter equal

/-- The original matched trace's left area equals the retained top perimeter at its own mesh depth. -/
theorem
  left_area_eq_top
    {side : MatchedHorizontalSide left right
      (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)) rightRow height}
    (trace : side.Trace left.depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : height = left.partition.y.intervals[Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)].upper) :
    CenteredBilinearPath.area
      (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) = perimeter.top := by
  rw [trace.left_area]
  exact side.left_boundary_eq_top values assembly perimeter equal

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

end

variable {leftRow : Fin left.partition.y.intervals.length}

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Geometry.Rectangle.Partition

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

/-- The matched right area and its original joins equal the retained bottom perimeter at the lower boundary. -/
theorem
  right_boundary_eq_bottom
    (side : MatchedHorizontalSide left right leftRow
      (Fin.cast right.boundaryRows_eq (0)) height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : height = right.partition.y.intervals[Fin.cast right.boundaryRows_eq (0)].lower) :
    side.rightArea values right.depth + side.rightJoins values = perimeter.bottom := by
  rw [perimeter.bottom_eq, side.rightArea_eq_bottom values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast right.boundaryColumns_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [assembly.sides_eq]
    rfl
  · have countEq : left.boundaryColumns = right.boundaryColumns :=
      congrArg (fun intervals : List PreparedAxisPartitions.Interval => intervals.length - 1) side.intervals_eq
    unfold rightJoins
    rw [RectangularMatchedPerimeter.sum_cast countEq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨_, height⟩)
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨_, height⟩) = _
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq index.castSucc))
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq index.succ))
    apply congrArg₂ edgeArea
    · apply congrArg (values _ _)
      exact Basic.ext upper.symm equal
    · apply congrArg (values _ _)
      exact Basic.ext lower.symm equal

/-- The matched right area and its original joins equal the retained top perimeter at the upper boundary. -/
theorem
  right_boundary_eq_top
    (side : MatchedHorizontalSide left right leftRow
      (Fin.cast right.boundaryRows_eq (Fin.last right.boundaryRows)) height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : height = right.partition.y.intervals[Fin.cast right.boundaryRows_eq (Fin.last right.boundaryRows)].upper) :
    side.rightArea values right.depth + side.rightJoins values = perimeter.top := by
  rw [perimeter.top_eq, side.rightArea_eq_top values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast right.boundaryColumns_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [assembly.sides_eq]
    rfl
  · have countEq : left.boundaryColumns = right.boundaryColumns :=
      congrArg (fun intervals : List PreparedAxisPartitions.Interval => intervals.length - 1) side.intervals_eq
    unfold rightJoins
    rw [RectangularMatchedPerimeter.sum_cast countEq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨_, height⟩)
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨_, height⟩) = _
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq index.castSucc))
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryColumns_eq index.succ))
    apply congrArg₂ edgeArea
    · apply congrArg (values _ _)
      exact Basic.ext upper.symm equal
    · apply congrArg (values _ _)
      exact Basic.ext lower.symm equal

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

end

open Purelib.Riemann.Periods

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

/-- The original matched trace's right area equals the retained bottom perimeter at its own mesh depth. -/
theorem
  right_area_eq_bottom
    {side : MatchedHorizontalSide left right leftRow
      (Fin.cast right.boundaryRows_eq (0)) height}
    (trace : side.Trace right.depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : height = right.partition.y.intervals[Fin.cast right.boundaryRows_eq (0)].lower) :
    CenteredBilinearPath.area
      (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) = perimeter.bottom := by
  rw [trace.right_area]
  exact side.right_boundary_eq_bottom values assembly perimeter equal

/-- The original matched trace's right area equals the retained top perimeter at its own mesh depth. -/
theorem
  right_area_eq_top
    {side : MatchedHorizontalSide left right leftRow
      (Fin.cast right.boundaryRows_eq (Fin.last right.boundaryRows)) height}
    (trace : side.Trace right.depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : height = right.partition.y.intervals[Fin.cast right.boundaryRows_eq (Fin.last right.boundaryRows)].upper) :
    CenteredBilinearPath.area
      (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) = perimeter.top := by
  rw [trace.right_area]
  exact side.right_boundary_eq_top values assembly perimeter equal

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace

end
section

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide (leftJoins
  rightJoins)

variable {rightColumn : Fin right.partition.x.intervals.length} {horizontal : Coordinate}

section
open Purelib.Algebra

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

/-- The matched left-owner area and original joins equal the retained left perimeter at the lower boundary coordinate.
-/
theorem
  left_boundary_eq_left
    (side : MatchedVerticalSide left right
      (Fin.cast left.boundaryColumns_eq (0)) rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : horizontal = left.partition.x.intervals[Fin.cast left.boundaryColumns_eq (0)].lower) :
    side.leftArea values left.depth + side.leftJoins values = perimeter.left := by
  rw [perimeter.left_eq, side.leftArea_eq_left values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast left.boundaryRows_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    rw [assembly.sides_eq]
    rfl
  · unfold leftJoins
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨horizontal, _⟩)
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨horizontal, _⟩) = _
    rw [equal]
    rfl

/-- The matched left-owner area and original joins equal the retained right perimeter at the upper boundary coordinate.
-/
theorem
  left_boundary_eq_right
    (side : MatchedVerticalSide left right
      (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)) rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : horizontal = left.partition.x.intervals[Fin.cast left.boundaryColumns_eq (Fin.last
      left.boundaryColumns)].upper) :
    side.leftArea values left.depth + side.leftJoins values = perimeter.right := by
  rw [perimeter.right_eq, side.leftArea_eq_right values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast left.boundaryRows_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    rw [assembly.sides_eq]
    rfl
  · unfold leftJoins
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨horizontal, _⟩)
      (values (left.ownerAt _ _).column (left.ownerAt _ _).row ⟨horizontal, _⟩) = _
    rw [equal]
    rfl

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

end

section
open Purelib.Riemann.Periods

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace

/-- The original matched trace's left-owner area equals the retained left perimeter at its own mesh depth. -/
theorem
  left_area_eq_left
    {side : MatchedVerticalSide left right
      (Fin.cast left.boundaryColumns_eq (0)) rightColumn horizontal}
    (trace : side.Trace left.depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : horizontal = left.partition.x.intervals[Fin.cast left.boundaryColumns_eq (0)].lower) :
    CenteredBilinearPath.area
      (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) = perimeter.left := by
  rw [trace.left_area]
  exact side.left_boundary_eq_left values assembly perimeter equal

/-- The original matched trace's left-owner area equals the retained right perimeter at its own mesh depth. -/
theorem
  left_area_eq_right
    {side : MatchedVerticalSide left right
      (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)) rightColumn horizontal}
    (trace : side.Trace left.depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : horizontal = left.partition.x.intervals[Fin.cast left.boundaryColumns_eq (Fin.last
      left.boundaryColumns)].upper) :
    CenteredBilinearPath.area
      (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)) = perimeter.right := by
  rw [trace.left_area]
  exact side.left_boundary_eq_right values assembly perimeter equal

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace

end

variable {leftColumn : Fin left.partition.x.intervals.length}

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Geometry.Rectangle.Partition

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

/-- The matched right-owner area and original joins equal the retained left perimeter at the lower boundary coordinate.
-/
theorem
  right_boundary_eq_left
    (side : MatchedVerticalSide left right leftColumn
      (Fin.cast right.boundaryColumns_eq (0)) horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : horizontal = right.partition.x.intervals[Fin.cast right.boundaryColumns_eq (0)].lower) :
    side.rightArea values right.depth + side.rightJoins values = perimeter.left := by
  rw [perimeter.left_eq, side.rightArea_eq_left values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast right.boundaryRows_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [assembly.sides_eq]
    rfl
  · have countEq : left.boundaryRows = right.boundaryRows :=
      congrArg (fun intervals : List PreparedAxisPartitions.Interval => intervals.length - 1) side.intervals_eq
    unfold rightJoins
    rw [RectangularMatchedPerimeter.sum_cast countEq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨horizontal, _⟩)
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨horizontal, _⟩) = _
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq index.castSucc))
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq index.succ))
    apply congrArg₂ edgeArea
    · apply congrArg (values _ _)
      exact Basic.ext equal upper.symm
    · apply congrArg (values _ _)
      exact Basic.ext equal lower.symm

/-- The matched right-owner area and original joins equal the retained right perimeter at the upper boundary coordinate.
-/
theorem
  right_boundary_eq_right
    (side : MatchedVerticalSide left right leftColumn
      (Fin.cast right.boundaryColumns_eq (Fin.last right.boundaryColumns)) horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : horizontal = right.partition.x.intervals[Fin.cast right.boundaryColumns_eq (Fin.last
      right.boundaryColumns)].upper) :
    side.rightArea values right.depth + side.rightJoins values = perimeter.right := by
  rw [perimeter.right_eq, side.rightArea_eq_right values equal]
  apply congrArg₂ (· + ·)
  · rw [RectangularMatchedPerimeter.sum_cast right.boundaryRows_eq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [assembly.sides_eq]
    rfl
  · have countEq : left.boundaryRows = right.boundaryRows :=
      congrArg (fun intervals : List PreparedAxisPartitions.Interval => intervals.length - 1) side.intervals_eq
    unfold rightJoins
    rw [RectangularMatchedPerimeter.sum_cast countEq]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    dsimp only
    rw [side.pieces_eq, side.pieces_eq, assembly.corners_eq, assembly.corners_eq]
    change edgeArea
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨horizontal, _⟩)
      (values (right.ownerAt _ _).column (right.ownerAt _ _).row ⟨horizontal, _⟩) = _
    have upper := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq index.castSucc))
    have lower := congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
      (RectangularMatchedPerimeter.interval_cast side.intervals_eq (Fin.cast left.boundaryRows_eq index.succ))
    apply congrArg₂ edgeArea
    · apply congrArg (values _ _)
      exact Basic.ext equal upper.symm
    · apply congrArg (values _ _)
      exact Basic.ext equal lower.symm

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

end

open Purelib.Riemann.Periods

namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace

/-- The original matched trace's right-owner area equals the retained left perimeter at its own mesh depth. -/
theorem
  right_area_eq_left
    {side : MatchedVerticalSide left right leftColumn
      (Fin.cast right.boundaryColumns_eq (0)) horizontal}
    (trace : side.Trace right.depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : horizontal = right.partition.x.intervals[Fin.cast right.boundaryColumns_eq (0)].lower) :
    CenteredBilinearPath.area
      (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) = perimeter.left := by
  rw [trace.right_area]
  exact side.right_boundary_eq_left values assembly perimeter equal

/-- The original matched trace's right-owner area equals the retained right perimeter at its own mesh depth. -/
theorem
  right_area_eq_right
    {side : MatchedVerticalSide left right leftColumn
      (Fin.cast right.boundaryColumns_eq (Fin.last right.boundaryColumns)) horizontal}
    (trace : side.Trace right.depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : horizontal = right.partition.x.intervals[Fin.cast right.boundaryColumns_eq (Fin.last
      right.boundaryColumns)].upper) :
    CenteredBilinearPath.area
      (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)) = perimeter.right := by
  rw [trace.right_area]
  exact side.right_boundary_eq_right values assembly perimeter equal

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace

end
end
