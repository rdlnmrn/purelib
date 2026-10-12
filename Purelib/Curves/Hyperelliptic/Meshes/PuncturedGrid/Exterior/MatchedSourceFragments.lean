module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
public import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Readings.RectangularSideReadingReadback
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
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.SourceIntervals
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

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Actual matched side pieces discharge their own endpoint geometry and
dyadic ordering when entering the source-fragment comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments

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
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}
  {evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
    sample otherSample fine}
  {lc lr rc rr : Nat} {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts : Paths.RectangularSegmentSplitting.GridCuts rg}
    {leftBox rightBox : Rational.Box}
  {left : Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {depth : Nat} {forward : Bool}

/-- Consecutive parameters in the original paired dyadic trace are nondecreasing. -/
private theorem dyadic_ordered (piece : Paths.RectangularPairedSegments.PairedSegmentPiece lg rg) (depth : Nat)
    (edge : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth)) :
    (Paths.RectangularDyadicPairedTrace.dyadic piece depth).parameters edge.castSucc ≤
      (Paths.RectangularDyadicPairedTrace.dyadic piece depth).parameters edge.succ := by
  dsimp only [Paths.RectangularDyadicPairedTrace.dyadic, Integration.RectangularPairedPointBanks.Trace.build]
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact Path.TraceLengths.Dyadic.forward_indexed id 0
    (Path.Dyadic.DyadicTrace.tail depth 0 1)
    (Path.TraceLengths.Dyadic.tail_forward depth (by decide)) edge

namespace SourceBlockParameters
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
    height}

/-- Transport a matched horizontal trace piece to the original source parent parameters.

The actual side endpoints and the original fixed imaginary coordinate discharge both endpoint identities. -/
def horizontalParameters (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (block : SourceBlockParameters evaluated false
      forward (left.partition.x.intervals[column.val]'column.isLt))
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height) :
    Paths.RectangularTraceParameterReadings.ParentParameters (trace.segments.get column)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index).plan.parent
      (SourceBlockParameters.firstParameter block)
        (SourceBlockParameters.lastParameter block) :=
  SourceBlockParameters.traceParameters block height
    sourceFirst sourceLast (trace.segments.get column)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments in
/-- Build the horizontal owned fragment from the original matched-side point readings.

The indexed parent, retained subinterval, budgets and actual dyadic trace determine both cached owned and source
samples. -/
def horizontalFragment (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (block : SourceBlockParameters evaluated false
      forward (left.partition.x.intervals[column.val]'column.isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {index : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index}
      {otherData : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
      (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (originalFirst : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex)))
    (originalSecond : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  let first := Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceReadings trace (Fin.cast
    left.boundaryColumns_eq.symm column) originalFirst
  let second := Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceReadings trace (Fin.cast
    left.boundaryColumns_eq.symm column) originalSecond
  let transport :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalParameters trace
    column block sourceFirst sourceLast
  let owned := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨first.values vertex, second.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint))
  let source := Periods.CenteredBilinearPath.Sample.build (fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (transport.parameters vertex))
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.ofTrace
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member evaluated block.index) located
    forward
    transport
    (by intro edge; rw [trace.segments_eq]; exact dyadic_ordered _ depth edge)
    budget owners later first second owned source

/-- The horizontal fragment reads back the supplied original left and right matched-side values at every indexed vertex.
-/
theorem horizontalFragment_values (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length)
    (block : SourceBlockParameters evaluated false
      forward (left.partition.x.intervals[column.val]'column.isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {index : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index}
      {otherData : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
      (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
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
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalFragment trace
      column block located sourceFirst sourceLast budget owners later first second
    ∀ vertex : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth + 1),
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues fragment.first fragment.second vertex
      =
      (⟨leftValues (column, vertex), rightValues (column, vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  intro fragment vertex
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.pieceReadings_spec trace
      (Fin.cast left.boundaryColumns_eq.symm column) first leftValues leftEq vertex)
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.pieceReadings_spec trace
      (Fin.cast left.boundaryColumns_eq.symm column) second rightValues rightEq vertex)

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
    horizontal}

/-- Transport a matched vertical trace piece to the original source parent parameters.

The actual side endpoints and the original fixed real coordinate discharge both endpoint identities. -/
def verticalParameters (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length)
    (block : SourceBlockParameters evaluated true
      forward (left.partition.y.intervals[row.val]'row.isLt))
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal) :
    Paths.RectangularTraceParameterReadings.ParentParameters (trace.segments.get row)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index).plan.parent
      (SourceBlockParameters.firstParameter block)
        (SourceBlockParameters.lastParameter block) :=
  SourceBlockParameters.traceParameters block
    horizontal sourceFirst sourceLast (trace.segments.get row)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments in
/-- Build the vertical owned fragment from the original matched-side point readings.

The indexed parent, retained subinterval, budgets and actual dyadic trace determine both cached owned and source
samples. -/
def verticalFragment (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length)
    (block : SourceBlockParameters evaluated true
      forward (left.partition.y.intervals[row.val]'row.isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {index : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index}
      {otherData : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
      (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (originalFirst : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex)))
    (originalSecond : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.point (trace.vertices.indexed vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  let first := Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceReadings trace (Fin.cast
    left.boundaryRows_eq.symm row) originalFirst
  let second := Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceReadings trace (Fin.cast
    left.boundaryRows_eq.symm row) originalSecond
  let transport :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalParameters trace
    row block sourceFirst sourceLast
  let owned := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨first.values vertex, second.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint))
  let source := Periods.CenteredBilinearPath.Sample.build (fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (transport.parameters vertex))
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.ofTrace
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated block.index)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry_member evaluated block.index) located
    forward
    transport
    (by intro edge; rw [trace.segments_eq]; exact dyadic_ordered _ depth edge)
    budget owners later first second owned source

/-- The vertical fragment reads back the supplied original left and right matched-side values at every indexed vertex.
-/
theorem verticalFragment_values (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length)
    (block : SourceBlockParameters evaluated true
      forward (left.partition.y.intervals[row.val]'row.isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {index : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index}
      {otherData : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
      (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
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
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalFragment trace
      row block located sourceFirst sourceLast budget owners later first second
    ∀ vertex : Fin (Paths.RectangularDyadicPairedTrace.dyadicCount depth + 1),
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues fragment.first fragment.second vertex
      =
      (⟨leftValues (row, vertex), rightValues (row, vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint) := by
  intro fragment vertex
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.pieceReadings_spec trace
      (Fin.cast left.boundaryRows_eq.symm row) first leftValues leftEq vertex)
    (Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.pieceReadings_spec trace
      (Fin.cast left.boundaryRows_eq.symm row) second rightValues rightEq vertex)

end Vertical
end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
