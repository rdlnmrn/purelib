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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
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
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
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

public section

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Matched side constructors produce the value-certified cached samples
consumed by the joined comparison. Certification never rebuilds a sample. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments

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
  {lc lr rc rr depth : Nat} {lg : Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts : Paths.RectangularSegmentSplitting.GridCuts rg}
    {leftBox rightBox : Rational.Box}
  {left : Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox} {forward : Bool}

namespace SourceBlockParameters
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
    height}

/-- Certify the original horizontal piece sample against its supplied matched-side vertex values.

The retained source location, owner readings and cached sample pass through exact indexed readback. -/
@[expose] def certifiedHorizontalPiece (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1))
    (block : SourceBlockParameters evaluated false
      forward
      (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column).val]'(Fin.cast left.boundaryColumns_eq
        column).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData)
      (fun vertex => (⟨leftValues ((side.pieceVertices depth column).indexed vertex),
        rightValues ((side.pieceVertices depth column).indexed vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint)) :=
  let fragment :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.horizontalFragment trace
    (Fin.cast left.boundaryColumns_eq column) block located sourceFirst sourceLast budget owners later first second
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofIndexed (fun vertex =>
    (Fin.cast left.boundaryColumns_eq column, vertex))
    (fun vertex => (⟨leftValues vertex, rightValues vertex⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofReadback fragment rfl _

        (MatchedSourceFragments.SourceBlockParameters.horizontalFragment_values
        trace (Fin.cast left.boundaryColumns_eq column) block located sourceFirst sourceLast budget owners later
        first second leftValues rightValues leftEq rightEq))

/-- Certify both original horizontal junction readings against the adjacent piece endpoint values.

The original cached junction sample is retained through exact readback. -/
@[expose] def certifiedHorizontalJunction (trace : side.Trace depth) (column : Fin left.boundaryColumns)
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData)
      (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues (fun vertex => (⟨leftValues vertex, rightValues vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint))
        (side.pieceVertices depth column.castSucc) (side.pieceVertices depth column.succ)) :=
  let fragment :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.horizontalJunction trace
    column block located sourceFirst sourceLast budget owners later first second
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofReadback fragment rfl _ (by
    intro vertex
    have equal :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.horizontalJunction_values
      trace column block located sourceFirst sourceLast budget owners later
      first second leftValues rightValues leftEq rightEq vertex
    refine equal.trans ?_
    by_cases zero : vertex.val = 0
    · dsimp only [Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues]
      rewrite [if_pos zero, if_pos zero]
      rfl
    · dsimp only [Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues]
      rewrite [if_neg zero, if_neg zero]
      rfl)

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Normalization.InverseRootPolynomial.Coordinate} {side :
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
    horizontal}

/-- Certify the original vertical piece sample against its supplied matched-side vertex values.

The retained source location, owner readings and cached sample pass through exact indexed readback. -/
@[expose] def certifiedVerticalPiece (trace : side.Trace depth) (row : Fin (left.boundaryRows + 1))
    (block : SourceBlockParameters evaluated true
      forward
      (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row).val]'(Fin.cast left.boundaryRows_eq row).isLt))
    (located : Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData)
      (fun vertex => (⟨leftValues ((side.pieceVertices depth row).indexed vertex),
        rightValues ((side.pieceVertices depth row).indexed vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint)) :=
  let fragment :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalFragment trace
    (Fin.cast left.boundaryRows_eq row) block located sourceFirst sourceLast budget owners later first second
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofIndexed (fun vertex =>
    (Fin.cast left.boundaryRows_eq row, vertex))
    (fun vertex => (⟨leftValues vertex, rightValues vertex⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofReadback fragment rfl _
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceFragments.SourceBlockParameters.verticalFragment_values
        trace (Fin.cast left.boundaryRows_eq row) block located sourceFirst sourceLast budget owners later
        first second leftValues rightValues leftEq rightEq))

/-- Certify both original vertical junction readings against the adjacent piece endpoint values.

The original cached junction sample is retained through exact readback. -/
@[expose] def certifiedVerticalJunction (trace : side.Trace depth) (row : Fin left.boundaryRows)
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData)
      (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues (fun vertex => (⟨leftValues vertex, rightValues vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint))
        (side.pieceVertices depth row.castSucc) (side.pieceVertices depth row.succ)) :=
  let fragment :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.verticalJunction trace row
    block located sourceFirst sourceLast budget owners later first second
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment.ofReadback fragment rfl _ (by
    intro vertex
    have equal :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions.SourceBlockParameters.verticalJunction_values
      trace row block located sourceFirst sourceLast budget owners later
      first second leftValues rightValues leftEq rightEq vertex
    refine equal.trans ?_
    by_cases zero : vertex.val = 0
    · dsimp only [Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues]
      rewrite [if_pos zero, if_pos zero]
      rfl
    · dsimp only [Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues]
      rewrite [if_neg zero, if_neg zero]
      rfl)

end Vertical
end SourceBlockParameters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments
