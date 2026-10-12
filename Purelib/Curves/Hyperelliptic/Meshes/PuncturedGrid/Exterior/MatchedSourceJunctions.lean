module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Readings.RectangularSideReadingReadback
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Owner junctions use the preceding piece's retained source location.
Both numerical readings remain present at their common physical point. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions

open Purelib.Riemann.Normalization

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
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}
  {evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
    sample otherSample fine}
  {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}

/-- Construct a one-step owner junction at one retained source parameter.

Both original numerical readings remain present at their common physical point, while the source sample repeats the same
original primitive value. -/
public def locatedJunction (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) (parameter :
      Normalization.InverseRootPolynomial.Coordinate)
    (inside : piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper)
    {points : Fin 2 → Normalization.InverseRootPolynomial.Gaussian} (pointEq : ∀ vertex, points vertex =
      entry.plan.parent.edge.point parameter)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (originalFirst : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (originalSecond : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets points) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  let first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data (fun _ : Fin 2
    => parameter) :=
    ⟨originalFirst.owners, fun vertex => (originalFirst.point_eq vertex).trans (pointEq vertex),
      originalFirst.values, originalFirst.value_eq⟩
  let second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData (fun _ :
    Fin 2 => parameter) :=
    ⟨originalSecond.owners, fun vertex => (originalSecond.point_eq vertex).trans (pointEq vertex),
      originalSecond.values, originalSecond.value_eq⟩
  let sourceValue := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry parameter
  { entry := entry, member := member, piece := piece, count := 1, parameters := fun _ => parameter
    inside := fun _ => inside, forward := true, ordered := fun _ => le_rfl
    allowance := allowance, budget := budget, owners := owners, later := later
    first := first, second := second, owned := Periods.CenteredBilinearPath.Sample.build
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second)
    source := Periods.CenteredBilinearPath.Sample.build (fun _ => sourceValue) }

namespace SourceBlockParameters
variable {lc lr rc rr : Nat} {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts : Paths.RectangularSegmentSplitting.GridCuts rg}
    {leftBox rightBox : Rational.Box}
  {left : Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {depth : Nat} {forward : Bool}

/-- The orientation-selected last parameter lies in the original block's retained parameter interval. -/
public theorem last_inside {vertical : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated vertical
      forward physical) :
    block.parameters.range.lower ≤
      (SourceBlockParameters.lastParameter block) ∧
      (SourceBlockParameters.lastParameter block) ≤
      block.parameters.range.upper := by
  cases forward with
  | true => exact ⟨block.parameters.range.ordered.le, le_rfl⟩
  | false => exact ⟨le_rfl, block.parameters.range.ordered.le⟩

/-- Build a horizontal owner junction at the preceding piece's original retained source endpoint.

The original matched-side junction readings and both point identities retain the two numerical owners at that same
physical point. -/
def horizontalJunction
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : Normalization.InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
      height}
    (trace : side.Trace depth) (column : Fin left.boundaryColumns)
    (block : SourceBlockParameters evaluated false
      forward
      (left.partition.x.intervals[(Fin.cast
        left.boundaryColumns_eq column.castSucc).val]'(Fin.cast left.boundaryColumns_eq column.castSucc).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.locatedJunction
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member evaluated block.index)
    located.piece (SourceBlockParameters.lastParameter
      block) (located.contains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.last_inside
      block))
    (fun vertex => (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.junction_point trace column
      vertex).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalParameters
        trace (Fin.cast left.boundaryColumns_eq column.castSucc) block sourceFirst sourceLast).last_point)
    budget owners later (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.junctionReadings trace column
      first) (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.junctionReadings trace column second)

/-- Build a vertical owner junction at the preceding piece's original retained source endpoint.

The original matched-side junction readings and both point identities retain the two numerical owners at that same
physical point. -/
def verticalJunction
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
      horizontal}
    (trace : side.Trace depth) (row : Fin left.boundaryRows)
    (block : SourceBlockParameters evaluated true
      forward
      (left.partition.y.intervals[(Fin.cast
        left.boundaryRows_eq row.castSucc).val]'(Fin.cast left.boundaryRows_eq row.castSucc).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.locatedJunction
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member evaluated block.index)
    located.piece (SourceBlockParameters.lastParameter
      block) (located.contains
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.last_inside
      block))
    (fun vertex => (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.junction_point trace row
      vertex).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalParameters trace
        (Fin.cast left.boundaryRows_eq row.castSucc) block sourceFirst sourceLast).last_point)
    budget owners later (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.junctionReadings trace row
      first) (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.junctionReadings trace row second)

/-- The horizontal junction preserves both original matched-side readings at the adjacent piece endpoints. -/
theorem horizontalJunction_values
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : Normalization.InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
      height}
    (trace : side.Trace depth) (column : Fin left.boundaryColumns)
    (block : SourceBlockParameters evaluated false
      forward
      (left.partition.x.intervals[(Fin.cast
        left.boundaryColumns_eq column.castSucc).val]'(Fin.cast left.boundaryColumns_eq column.castSucc).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → Normalization.InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    let fragment :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.horizontalJunction trace
      column block located sourceFirst sourceLast budget owners later first second
    ∀ vertex : Fin 2, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues fragment.first
      fragment.second vertex =
      let point := if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last else (side.pieceVertices depth
        column.succ).first
      (⟨leftValues point, rightValues point⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  intro fragment vertex
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.junctionReadings_spec trace
    column first leftValues leftEq vertex)
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.junctionReadings_spec trace
      column second rightValues rightEq vertex)

/-- The vertical junction preserves both original matched-side readings at the adjacent piece endpoints. -/
theorem verticalJunction_values
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
      horizontal}
    (trace : side.Trace depth) (row : Fin left.boundaryRows)
    (block : SourceBlockParameters evaluated true
      forward
      (left.partition.y.intervals[(Fin.cast
        left.boundaryRows_eq row.castSucc).val]'(Fin.cast left.boundaryRows_eq row.castSucc).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → Normalization.InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    let fragment :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.verticalJunction trace
      row block located sourceFirst sourceLast budget owners later first second
    ∀ vertex : Fin 2, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues fragment.first
      fragment.second vertex =
      let point := if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last else (side.pieceVertices depth
        row.succ).first
      (⟨leftValues point, rightValues point⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  intro fragment vertex
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.junctionReadings_spec trace
    row first leftValues leftEq vertex)
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.junctionReadings_spec trace
      row second rightValues rightEq vertex)

end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions
