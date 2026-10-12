module

public import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Integration.Path.JoinedTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularMatchedPerimeter
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Purelib.Riemann.Integration.RectangularMatchedCornerReadback

public section

/-! Matched contact traces and retained perimeter traces have identical
centered areas, including their owner joins and corner corrections. -/
namespace Purelib.Riemann.Integration.RectangularMatchedCenteredPerimeters

open Purelib.Integration.Path
open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces (topOwned bottomOwned rightOwned leftOwned topOwned_area
  bottomOwned_area rightOwned_area leftOwned_area topOwned_first bottomOwned_first rightOwned_first leftOwned_first
  topOwned_last bottomOwned_last rightOwned_last leftOwned_last)
open Purelib.Integration.Path.JoinedCenteredArea (sample_area sample_endpoint)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}

namespace MatchedHorizontalSide.Trace

/-- The original left matched trace has the same centered area as its retained top perimeter trace.

The shared coordinate must be the left box's upper ordinate and the trace depth must equal the original mesh depth;
exact corner and endpoint readbacks identify the two samples. -/
theorem left_centered_top
    {otherIndex : Fin right.partition.y.intervals.length} {coordinate : Coordinate}
    {side : MatchedHorizontalSide left right (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows)) otherIndex
      coordinate}
    {depth : Nat} (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)))
    (traces : PerimeterTraces left)
    (owned : Sample (fun vertex => let owner := (topOwned traces).indexed vertex
      values owner.column owner.row owner.point))
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : coordinate = leftBox.yUpper) (depthEq : depth = left.depth) :
    sample.centeredArea = owned.centeredArea := by
  have areaEq : sample.originalArea = owned.originalArea := by
    rw [sample.originalArea_eq, JoinedCenteredArea.sample_area (topOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned, topOwned_area traces values assembly perimeter]
    rw [trace.left_area, depthEq]
    exact side.left_boundary_eq_top values assembly perimeter (equal.trans left.y_last.symm)
  have endpointEq : sample.endpoint = owned.endpoint := by
    rw [sample.endpoint_eq, JoinedCenteredArea.sample_endpoint (topOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned]
    have first := RectangularMatchedCornerReadback.MatchedHorizontalSide.Trace.left_corner trace (above := true) values
      equal false
    have last := RectangularMatchedCornerReadback.MatchedHorizontalSide.Trace.left_corner trace (above := true) values
      equal true
    have firstRead := (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).symm.trans first
    have lastRead := (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).symm.trans last
    erw [firstRead, lastRead, topOwned_first traces values, topOwned_last traces values]
    dsimp only [edgeArea, PrimitivePoint.sub]
    ring1
  have decomposed := sample.decomposition.symm.trans (areaEq.trans owned.decomposition)
  rw [endpointEq] at decomposed
  exact add_right_cancel decomposed

/-- The original right matched trace has the same centered area as its retained bottom perimeter trace.

The shared coordinate and depth must equal the right box's lower ordinate and original mesh depth, preserving both
original sample endpoints. -/
theorem right_centered_bottom
    {otherIndex : Fin left.partition.y.intervals.length} {coordinate : Coordinate}
    {side : MatchedHorizontalSide left right otherIndex (Fin.cast right.boundaryRows_eq 0) coordinate}
    {depth : Nat} (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (sample : Sample (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)))
    (traces : PerimeterTraces right)
    (owned : Sample (fun vertex => let owner := (bottomOwned traces).indexed vertex
      values owner.column owner.row owner.point))
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : coordinate = rightBox.yLower) (depthEq : depth = right.depth) :
    sample.centeredArea = owned.centeredArea := by
  have areaEq : sample.originalArea = owned.originalArea := by
    rw [sample.originalArea_eq, JoinedCenteredArea.sample_area (bottomOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned, bottomOwned_area traces values assembly perimeter]
    rw [trace.right_area, depthEq]
    exact side.right_boundary_eq_bottom values assembly perimeter (equal.trans right.y_first.symm)
  have endpointEq : sample.endpoint = owned.endpoint := by
    rw [sample.endpoint_eq, JoinedCenteredArea.sample_endpoint (bottomOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned]
    have first := RectangularMatchedCornerReadback.MatchedHorizontalSide.Trace.right_corner trace (above := false)
      values equal false
    have last := RectangularMatchedCornerReadback.MatchedHorizontalSide.Trace.right_corner trace (above := false) values
      equal true
    have firstRead := (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).symm.trans first
    have lastRead := (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).symm.trans last
    erw [firstRead, lastRead, bottomOwned_first traces values, bottomOwned_last traces values]
    dsimp only [edgeArea, PrimitivePoint.sub]
    ring1
  have decomposed := sample.decomposition.symm.trans (areaEq.trans owned.decomposition)
  rw [endpointEq] at decomposed
  exact add_right_cancel decomposed

end MatchedHorizontalSide.Trace

namespace MatchedVerticalSide.Trace

/-- The original left matched trace has the same centered area as its retained right perimeter trace.

The shared coordinate is the left box's upper abscissa and the depth is the original mesh depth; exact area and endpoint
readbacks retain the original orientation. -/
theorem left_centered_right
    {otherIndex : Fin right.partition.x.intervals.length} {coordinate : Coordinate}
    {side : MatchedVerticalSide left right (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns)) otherIndex
      coordinate}
    {depth : Nat} (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex)))
    (traces : PerimeterTraces left)
    (owned : Sample (fun vertex => let owner := (rightOwned traces).indexed vertex
      values owner.column owner.row owner.point))
    (assembly : ClippedAssembly left values) (perimeter : assembly.Perimeter)
    (equal : coordinate = leftBox.xUpper) (depthEq : depth = left.depth) :
    sample.centeredArea = owned.centeredArea := by
  have areaEq : sample.originalArea = owned.originalArea := by
    rw [sample.originalArea_eq, JoinedCenteredArea.sample_area (rightOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned, rightOwned_area traces values assembly perimeter]
    rw [trace.left_area, depthEq]
    exact side.left_boundary_eq_right values assembly perimeter (equal.trans left.x_last.symm)
  have endpointEq : sample.endpoint = owned.endpoint := by
    rw [sample.endpoint_eq, JoinedCenteredArea.sample_endpoint (rightOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned]
    have first := RectangularMatchedCornerReadback.MatchedVerticalSide.Trace.left_corner trace (rightward := true)
      values equal false
    have last := RectangularMatchedCornerReadback.MatchedVerticalSide.Trace.left_corner trace (rightward := true) values
      equal true
    have firstRead := (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).symm.trans first
    have lastRead := (congrArg (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).symm.trans last
    erw [firstRead, lastRead, rightOwned_first traces values, rightOwned_last traces values]
    dsimp only [edgeArea, PrimitivePoint.sub]
    ring1
  have decomposed := sample.decomposition.symm.trans (areaEq.trans owned.decomposition)
  rw [endpointEq] at decomposed
  exact add_right_cancel decomposed

/-- The original right matched trace has the same centered area as its retained left perimeter trace.

The shared coordinate is the right box's lower abscissa and the depth is the original mesh depth, with both original
endpoint samples retained. -/
theorem right_centered_left
    {otherIndex : Fin left.partition.x.intervals.length} {coordinate : Coordinate}
    {side : MatchedVerticalSide left right otherIndex (Fin.cast right.boundaryColumns_eq 0) coordinate}
    {depth : Nat} (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    (sample : Sample (fun vertex => trace.rightValue values (trace.vertices.indexed vertex)))
    (traces : PerimeterTraces right)
    (owned : Sample (fun vertex => let owner := (leftOwned traces).indexed vertex
      values owner.column owner.row owner.point))
    (assembly : ClippedAssembly right values) (perimeter : assembly.Perimeter)
    (equal : coordinate = rightBox.xLower) (depthEq : depth = right.depth) :
    sample.centeredArea = owned.centeredArea := by
  have areaEq : sample.originalArea = owned.originalArea := by
    rw [sample.originalArea_eq, JoinedCenteredArea.sample_area (leftOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned, leftOwned_area traces values assembly perimeter]
    rw [trace.right_area, depthEq]
    exact side.right_boundary_eq_left values assembly perimeter (equal.trans right.x_first.symm)
  have endpointEq : sample.endpoint = owned.endpoint := by
    rw [sample.endpoint_eq, JoinedCenteredArea.sample_endpoint (leftOwned traces) (fun owner => values owner.column
      owner.row owner.point) owned]
    have first := RectangularMatchedCornerReadback.MatchedVerticalSide.Trace.right_corner trace (rightward := false)
      values equal false
    have last := RectangularMatchedCornerReadback.MatchedVerticalSide.Trace.right_corner trace (rightward := false)
      values equal true
    have firstRead := (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_neg (by decide : false ≠ true))).symm.trans first
    have lastRead := (congrArg (fun vertex => trace.rightValue values (trace.vertices.indexed vertex))
      (if_pos (Eq.refl true))).symm.trans last
    erw [firstRead, lastRead, leftOwned_first traces values, leftOwned_last traces values]
    dsimp only [edgeArea, PrimitivePoint.sub]
    ring1
  have decomposed := sample.decomposition.symm.trans (areaEq.trans owned.decomposition)
  rw [endpointEq] at decomposed
  exact add_right_cancel decomposed

end MatchedVerticalSide.Trace

end Purelib.Riemann.Integration.RectangularMatchedCenteredPerimeters

end
