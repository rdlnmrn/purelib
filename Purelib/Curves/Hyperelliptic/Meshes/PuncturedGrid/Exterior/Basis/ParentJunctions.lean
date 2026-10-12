module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.Paths.RectangularPairedSegments
public import Purelib.Riemann.Paths.RectangularTraceParameterReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularTraceParameterReadings

public section

/-! Endpoint and junction readbacks on the original common-basis parent cache. -/
section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (point)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis signedInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (parent_parameter_eq
  parent_signed_bounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
variable {vertical forward : Bool} {physical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

/-- The retained parent interval endpoint corresponding to the first physical side endpoint. -/
@[expose] def firstParameter (block : ParentBlocks.ParentBlock occurrence vertical forward physical) : Coordinate :=
  if forward then block.parameters.range.lower else block.parameters.range.upper

/-- The retained parent interval endpoint corresponding to the last physical side endpoint. -/
@[expose] def lastParameter (block : ParentBlocks.ParentBlock occurrence vertical forward physical) : Coordinate :=
  if forward then block.parameters.range.upper else block.parameters.range.lower

/-- The first retained parent parameter reads the original physical interval's lower coordinate. -/
theorem first_axis (block : ParentBlocks.ParentBlock occurrence vertical forward physical) :
    SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point
      block.firstParameter) = physical.lower := by
  rw [PreparedParentSplitting.prepared_point_eq, SourceIntervals.axis_affine]
  cases forward with
  | true => exact block.parameters.first_eq
  | false =>
    have equal := congrArg Neg.neg block.parameters.last_eq
    change -(-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0) +
      block.parameters.range.upper * (-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 1) -
        -SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0))) =
          -(-physical.lower) at equal
    rw [neg_neg] at equal
    exact (show _ = -(-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
      block.index).edge.point 0) +
      block.parameters.range.upper * (-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 1) -
        -SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0))) by
      simp only [firstParameter,
        if_neg (show (false : Bool) ≠ true from Bool.noConfusion), -eq_self, -iff_self]; ring1).trans equal

/-- The last retained parent parameter reads the original physical interval's upper coordinate. -/
theorem last_axis (block : ParentBlocks.ParentBlock occurrence vertical forward physical) :
    SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point
      block.lastParameter) = physical.upper := by
  rw [PreparedParentSplitting.prepared_point_eq, SourceIntervals.axis_affine]
  cases forward with
  | true => exact block.parameters.last_eq
  | false =>
    have equal := congrArg Neg.neg block.parameters.first_eq
    change -(-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0) +
      block.parameters.range.lower * (-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 1) -
        -SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0))) =
          -(-physical.upper) at equal
    rw [neg_neg] at equal
    exact (show _ = -(-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
      block.index).edge.point 0) +
      block.parameters.range.lower * (-SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence
        block.index).edge.point 1) -
        -SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point 0))) by
      simp only [lastParameter, if_neg
        (show (false : Bool) ≠ true from Bool.noConfusion), -eq_self, -iff_self]; ring1).trans equal

/-- Every selected parent retains the fixed coordinate of its occurrence. -/
theorem fixed_axis (block : ParentBlocks.ParentBlock occurrence vertical forward physical)
    (coordinate : InverseRootPolynomial.Coordinate)
    (firstEq : SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
    (lastEq : SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate) (parameter :
      InverseRootPolynomial.Coordinate) :
    SourceIntervals.axisCoordinate (!vertical) ((ParentBlocks.cacheParent occurrence block.index).edge.point parameter)
      = coordinate := by
  have endpoints := PreparedSegmentBoundaryGeometry.segment_parent_endpoints occurrence.compared.entered.cache
    block.member
  have atSegment (fraction : InverseRootPolynomial.Coordinate) :
      SourceIntervals.axisCoordinate (!vertical) (occurrence.segment.pointAt fraction) = coordinate := by
    change SourceIntervals.axisCoordinate (!vertical) (PreparedSegmentCuts.point occurrence.start occurrence.finish
      fraction) = coordinate
    rw [SourceIntervals.axis_affine, firstEq, lastEq]
    ring1
  rw [PreparedParentSplitting.prepared_point_eq, SourceIntervals.axis_affine, endpoints.1, endpoints.2,
    atSegment, atSegment]
  ring1

/-- Transport a retained physical trace to its selected original parent. Both coordinates are certified, including the
fixed coordinate of the side. -/
@[expose] def traceParameters (block : ParentBlocks.ParentBlock occurrence vertical forward physical)
    (coordinate : InverseRootPolynomial.Coordinate)
    (sourceFirst : SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
    (sourceLast : SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate)
    {lc lr rc rr count : Nat}
    {lg : RectangularInverseModels.Geometry lc lr} {rg : RectangularInverseModels.Geometry rc rr}
    {piece : RectangularPairedSegments.PairedSegmentPiece lg rg} (trace : RectangularPairedPointBanks.Trace piece count)
    (firstAlong : SourceIntervals.axisCoordinate vertical piece.first = physical.lower)
    (lastAlong : SourceIntervals.axisCoordinate vertical piece.last = physical.upper)
    (firstAcross : SourceIntervals.axisCoordinate (!vertical) piece.first = coordinate)
    (lastAcross : SourceIntervals.axisCoordinate (!vertical) piece.last = coordinate) :
    RectangularTraceParameterReadings.ParentParameters trace (ParentBlocks.cacheParent occurrence block.index)
      block.firstParameter block.lastParameter :=
  ParentParameters.build trace _ _ _
    (SourceIntervals.point_from_axes vertical (firstAlong.trans block.first_axis.symm)
      (firstAcross.trans (block.fixed_axis coordinate sourceFirst sourceLast _).symm))
    (SourceIntervals.point_from_axes vertical (lastAlong.trans block.last_axis.symm)
      (lastAcross.trans (block.fixed_axis coordinate sourceFirst sourceLast _).symm))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

variable {beforeForward afterForward : Bool}
  {beforePhysical afterPhysical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

/-- Consecutive physical pieces retaining the identical parent position have equal adjoining parent parameters. -/
theorem same_parent_parameters
    (before : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence vertical afterForward afterPhysical)
    (same : after.index = before.index) (consecutive : afterPhysical.lower = beforePhysical.upper) :
    after.firstParameter = before.lastParameter := by
  have equal := after.first_axis.trans (consecutive.trans before.last_axis.symm)
  rw [same] at equal
  exact BoundaryTraceParameters.parent_parameter_eq before.ordered equal

/-- Matching the physical start to its parent endpoint determines the full run's initial parameter, including reversed
physical sides. -/
theorem first_parameter_of_parent_endpoint
    (block : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    (aligned : beforePhysical.lower = SourceIntervals.axisCoordinate vertical
      ((ParentBlocks.cacheParent occurrence block.index).edge.point (if beforeForward then 0 else 1))) :
    block.firstParameter = if beforeForward then 0 else 1 :=
  BoundaryTraceParameters.parent_parameter_eq block.ordered (block.first_axis.trans aligned)

/-- Alignment with the original parent's final physical endpoint determines the retained last parameter. -/
theorem last_parameter_of_parent_endpoint
    (block : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    (aligned : beforePhysical.upper = SourceIntervals.axisCoordinate vertical
      ((ParentBlocks.cacheParent occurrence block.index).edge.point (if beforeForward then 1 else 0))) :
    block.lastParameter = if beforeForward then 1 else 0 :=
  BoundaryTraceParameters.parent_parameter_eq block.ordered (block.last_axis.trans aligned)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions.ParentBlock

/-- Every original unit parent parameter lies between the direction-selected physical endpoint coordinates. -/
private theorem parameter_physical_bounds
    (block : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point (if
      beforeForward then 0 else 1)) ≤
      SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point parameter) ∧
    SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point parameter) ≤
      SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point (if
        beforeForward then 1 else 0)) := by
  have bounds := BoundaryTraceParameters.parent_signed_bounds block.ordered inside
  cases beforeForward with
  | true => exact bounds
  | false =>
    have lower := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2
    have upper := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1
    simpa only [SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), neg_neg,
      -eq_self, -iff_self] using And.intro lower upper

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions.ParentBlock

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

/-- The retained physical interval lies inside the selected original parent's physical span. -/
theorem physical_inside (block : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical) :
    SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point (if
      beforeForward then 0 else 1)) ≤
      beforePhysical.lower ∧ beforePhysical.upper ≤
      SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence block.index).edge.point (if
        beforeForward then 1 else 0)) := by
  have lowUnit : 0 ≤ block.parameters.range.lower ∧ block.parameters.range.lower ≤ 1 :=
    ⟨block.parameters.within.1, block.parameters.range.ordered.le.trans block.parameters.within.2⟩
  have highUnit : 0 ≤ block.parameters.range.upper ∧ block.parameters.range.upper ≤ 1 :=
    ⟨block.parameters.within.1.trans block.parameters.range.ordered.le, block.parameters.within.2⟩
  have firstUnit : 0 ≤ block.firstParameter ∧ block.firstParameter ≤ 1 := by
    cases beforeForward with
    | true => exact lowUnit
    | false => exact highUnit
  have lastUnit : 0 ≤ block.lastParameter ∧ block.lastParameter ≤ 1 := by
    cases beforeForward with
    | true => exact highUnit
    | false => exact lowUnit
  exact ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions.ParentBlock.parameter_physical_bounds
    block firstUnit).1.trans_eq block.first_axis,
    block.last_axis.symm.trans_le
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions.ParentBlock.parameter_physical_bounds
      block lastUnit).2⟩

/-- A shared physical endpoint that is the end of both selected parent intervals retains both parameter certificates; no
primitive jump is cancelled. -/
theorem parent_handoff_parameters
    (before : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence vertical afterForward afterPhysical)
    (consecutive : afterPhysical.lower = beforePhysical.upper)
    (beforeEnd : beforePhysical.upper = SourceIntervals.axisCoordinate vertical
      ((ParentBlocks.cacheParent occurrence before.index).edge.point (if beforeForward then 1 else 0)))
    (parentJoin : SourceIntervals.axisCoordinate vertical
      ((ParentBlocks.cacheParent occurrence before.index).edge.point (if beforeForward then 1 else 0)) =
      SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence after.index).edge.point (if
        afterForward then 0 else 1))) :
    before.lastParameter = (if beforeForward then 1 else 0) ∧
      after.firstParameter = (if afterForward then 0 else 1) :=
  ⟨before.last_parameter_of_parent_endpoint beforeEnd,
    after.first_parameter_of_parent_endpoint (consecutive.trans (beforeEnd.trans parentJoin))⟩

/-- Adjacent physical pieces selected from separated parent spans must meet at both parent endpoints. This supplies the
run boundaries geometrically. -/
theorem handoff_of_separated
    (before : ParentBlocks.ParentBlock occurrence vertical beforeForward beforePhysical)
    (after : ParentBlocks.ParentBlock occurrence vertical afterForward afterPhysical)
    (consecutive : afterPhysical.lower = beforePhysical.upper)
    (separated : SourceIntervals.axisCoordinate vertical
      ((ParentBlocks.cacheParent occurrence before.index).edge.point (if beforeForward then 1 else 0)) ≤
      SourceIntervals.axisCoordinate vertical ((ParentBlocks.cacheParent occurrence after.index).edge.point (if
        afterForward then 0 else 1))) :
    before.lastParameter = (if beforeForward then 1 else 0) ∧
      after.firstParameter = (if afterForward then 0 else 1) := by
  have left := before.physical_inside.2
  have right := after.physical_inside.1.trans_eq consecutive
  have beforeEnd := _root_.le_antisymm left (separated.trans right)
  have parentJoin := _root_.le_antisymm separated (right.trans left)
  exact before.parent_handoff_parameters after consecutive beforeEnd parentJoin

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

end
