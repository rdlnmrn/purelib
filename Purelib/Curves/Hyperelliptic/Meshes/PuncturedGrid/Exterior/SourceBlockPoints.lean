module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

section

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-! Full point readback for assigned exterior blocks. The fixed coordinate
is inherited from the original segment, not inferred from an axis match. -/
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints

/-- Axis projection commutes with the original scalar affine interpolation. -/
private theorem axis_affine (vertical : Bool) (first last : Normalization.InverseRootPolynomial.Gaussian) (parameter :
  Normalization.InverseRootPolynomial.Coordinate) :
    Rectangle.SourceIntervals.axisCoordinate vertical (Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts.point
      first last parameter) =
      Rectangle.SourceIntervals.axisCoordinate vertical first + parameter * (Rectangle.SourceIntervals.axisCoordinate
        vertical last - Rectangle.SourceIntervals.axisCoordinate vertical first) := by
  cases vertical <;> rfl

/-- An affine segment whose endpoints share an axis coordinate keeps that coordinate at every parameter. -/
private theorem axis_constant (vertical : Bool) (first last : Normalization.InverseRootPolynomial.Gaussian) (parameter
  coordinate : Normalization.InverseRootPolynomial.Coordinate)
    (firstEq : Rectangle.SourceIntervals.axisCoordinate vertical first = coordinate) (lastEq :
      Rectangle.SourceIntervals.axisCoordinate vertical last = coordinate) :
    Rectangle.SourceIntervals.axisCoordinate vertical (Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts.point
      first last parameter) = coordinate := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.axis_affine, firstEq, lastEq]
  ring1

/-- Every indexed original parent keeps the containing segment's fixed axis coordinate.

The retained parent membership supplies both original endpoints on that same segment. -/
theorem indexed_parent_axis_constant (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (index : Fin evaluated.retained.length) (vertical : Bool) (coordinate :
      Normalization.InverseRootPolynomial.Coordinate)
    (firstEq : Rectangle.SourceIntervals.axisCoordinate vertical occurrence.start = coordinate)
    (lastEq : Rectangle.SourceIntervals.axisCoordinate vertical occurrence.finish = coordinate) (parameter :
      Normalization.InverseRootPolynomial.Coordinate) :
    Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent.edge.point parameter) = coordinate := by
  have member : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
    index).plan.parent ∈ occurrence.compared.entered.cache.parents := by
    have mapped : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent ∈ evaluated.retained.map (fun entry => entry.plan.parent) :=
      Data.List.Map.mem_map.mpr ⟨_, Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member
        evaluated index, rfl⟩
    exact Eq.mp (congrArg (fun parents => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry
      evaluated index).plan.parent ∈ parents)
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated)) mapped
  have endpoints := Paths.PreparedSegmentBoundaryGeometry.segment_parent_endpoints occurrence.compared.entered.cache
    member
  have atSegment (fraction : Normalization.InverseRootPolynomial.Coordinate) : Rectangle.SourceIntervals.axisCoordinate
    vertical (occurrence.segment.pointAt fraction) = coordinate := by
    change Rectangle.SourceIntervals.axisCoordinate vertical (Rectangle.Partition.PreparedSegmentCuts.point
      occurrence.start occurrence.finish fraction) = coordinate
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.axis_constant vertical _ _ fraction coordinate
      firstEq lastEq
  rw [Integration.PreparedParentSplitting.prepared_point_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.axis_affine, endpoints.1, endpoints.2,
    atSegment, atSegment]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
variable {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine} {vertical forward : Bool}
  {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}

/-- Select the original parent parameter at the physical interval's lower endpoint according to traversal orientation.
-/
@[expose] def firstParameter (block :
  SourceBlockParameters evaluated vertical forward
  physical) : Coordinate :=
  if forward then block.parameters.range.lower else block.parameters.range.upper

/-- Select the original parent parameter at the physical interval's upper endpoint according to traversal orientation.
-/
@[expose] def lastParameter (block :
  SourceBlockParameters evaluated vertical forward
  physical) : Coordinate :=
  if forward then block.parameters.range.upper else block.parameters.range.lower

/-- The selected first parent parameter reads back the physical interval's lower axis endpoint. -/
theorem first_axis (block : SourceBlockParameters
  evaluated vertical forward physical) :
    Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point
      (firstParameter block)) =
      physical.lower := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.axis_affine]
  cases forward with
  | true => exact block.parameters.first_eq
  | false =>
    have equal := congrArg Neg.neg block.parameters.last_eq
    change -(-Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0) +
      block.parameters.range.upper * (-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) -
        -Rectangle.SourceIntervals.axisCoordinate vertical
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
          block.index).plan.parent.edge.point 0))) = -(-physical.lower) at equal
    rw [neg_neg] at equal
    exact (show _ = -(-Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0) +
      block.parameters.range.upper * (-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) -
        -Rectangle.SourceIntervals.axisCoordinate vertical
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
          block.index).plan.parent.edge.point 0))) by
      dsimp only
        [firstParameter]; rw
        [if_neg (show false ≠ true by intro same; cases same)]; ring1).trans equal

/-- The selected last parent parameter reads back the physical interval's upper axis endpoint. -/
theorem last_axis (block : SourceBlockParameters
  evaluated vertical forward physical) :
    Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point
      (lastParameter block)) =
      physical.upper := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.axis_affine]
  cases forward with
  | true => exact block.parameters.last_eq
  | false =>
    have equal := congrArg Neg.neg block.parameters.first_eq
    change -(-Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0) +
      block.parameters.range.lower * (-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) -
        -Rectangle.SourceIntervals.axisCoordinate vertical
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
          block.index).plan.parent.edge.point 0))) = -(-physical.upper) at equal
    rw [neg_neg] at equal
    exact (show _ = -(-Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0) +
      block.parameters.range.lower * (-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) -
        -Rectangle.SourceIntervals.axisCoordinate vertical
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
          block.index).plan.parent.edge.point 0))) by
      dsimp only
        [lastParameter]; rw
        [if_neg (show false ≠ true by intro same; cases same)]; ring1).trans equal

/-- Compute the trace's parameter vector from the actual segment's fixed
coordinate and the physical block endpoints. Reversed source orientation
produces descending parameters, without reversing or resampling readings. -/
@[expose] def traceParameters (block :
  SourceBlockParameters evaluated vertical forward
  physical)
    (coordinate : Normalization.InverseRootPolynomial.Coordinate)
    (sourceFirst : Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
    (sourceLast : Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate)
    {lc lr rc rr count : Nat}
    {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg : Normalization.RectangularInverseModels.Geometry
      rc rr}
    {piece : Paths.RectangularPairedSegments.PairedSegmentPiece lg rg} (trace :
      Integration.RectangularPairedPointBanks.Trace piece count)
    (firstAlong : Rectangle.SourceIntervals.axisCoordinate vertical piece.first = physical.lower)
    (lastAlong : Rectangle.SourceIntervals.axisCoordinate vertical piece.last = physical.upper)
    (firstAcross : Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.first = coordinate)
    (lastAcross : Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.last = coordinate) :
    Paths.RectangularTraceParameterReadings.ParentParameters trace
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index).plan.parent
      (firstParameter block)
      (lastParameter block) :=
  Paths.RectangularTraceParameterReadings.ParentParameters.build trace _ _ _
    (Rectangle.SourceIntervals.point_from_axes vertical (firstAlong.trans
      (first_axis block).symm)
      (firstAcross.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.indexed_parent_axis_constant
        evaluated block.index (!vertical) coordinate sourceFirst sourceLast _).symm))
    (Rectangle.SourceIntervals.point_from_axes vertical (lastAlong.trans
      (last_axis block).symm)
      (lastAcross.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints.indexed_parent_axis_constant
        evaluated block.index (!vertical) coordinate sourceFirst sourceLast _).symm))

/-- A physical block in either orientation consumes its indexed source location
and scalar side geometry directly. Full point transport, inside bounds and
the owner-aware area comparison are discharged by the retained data. -/
@[expose] def ownedFragment (block :
  SourceBlockParameters evaluated vertical forward
  physical)
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
        block.parameters.range)
    (coordinate : Normalization.InverseRootPolynomial.Coordinate)
    (sourceFirst : Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.start = coordinate)
    (sourceLast : Rectangle.SourceIntervals.axisCoordinate (!vertical) occurrence.finish = coordinate)
    {lc lr rc rr count index : Nat}
    {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg : Normalization.RectangularInverseModels.Geometry
      rc rr}
    {piece : Paths.RectangularPairedSegments.PairedSegmentPiece lg rg} (trace :
      Integration.RectangularPairedPointBanks.Trace piece count)
    (firstAlong : Rectangle.SourceIntervals.axisCoordinate vertical piece.first = physical.lower)
    (lastAlong : Rectangle.SourceIntervals.axisCoordinate vertical piece.last = physical.upper)
    (firstAcross : Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.first = coordinate)
    (lastAcross : Rectangle.SourceIntervals.axisCoordinate (!vertical) piece.last = coordinate)
    (increasing : ∀ edge : Fin count, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.points
      vertex))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.points vertex))
    (owned : Periods.CenteredBilinearPath.Sample
      (fun vertex => (⟨first.values vertex, second.values vertex⟩ : Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
      ((traceParameters block
        coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross lastAcross).parameters vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.ofTrace
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member evaluated block.index) located
    forward
    (traceParameters block
      coordinate sourceFirst sourceLast trace firstAlong lastAlong firstAcross lastAcross)
    increasing budget owners later first second owned source

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

end
