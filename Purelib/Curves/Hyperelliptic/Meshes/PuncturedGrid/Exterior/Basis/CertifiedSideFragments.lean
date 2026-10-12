module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MatchedJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Batteries.Logic
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MatchedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
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
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CertifiedSideFragments

public section

/-! Certified cached piece and junction samples at their physical trace positions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Rectangle
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Paths
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
variable {lc lr rc rr depth : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
namespace ParentBlock
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}

/-- Attach the retained piece sample to its exact whole-side vertex positions. -/
@[expose] def certifiedHorizontalPiece (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1)) {forward :
  Bool}
    (block : ParentBlocks.ParentBlock occurrence false forward
      (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column).val]'(Fin.cast left.boundaryColumns_eq
        column).isLt))
    {covers : SourceLocations.BasisSourceCovers (ParentBlocks.cacheParent occurrence block.index)}
    {sourceIndex faceIndex : Nat}
    {originals : BasisSourceLocations.PrimitiveBank covers sourceIndex}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data : FragmentQueries.RowData occurrence
      faceIndex}
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
      (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    JoinedFragments.SampledFragment (originals := originals) (coefficients := coefficients) (data := data)
      (fun vertex => ((fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow => coefficients
        basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ :
          Stokes.PrimitivePoint))) ((side.pieceVertices depth column).indexed vertex)) := by
  let fragment := block.horizontalFragment (originals := originals) (coefficients := coefficients)
    trace (Fin.cast left.boundaryColumns_eq column) sourceFirst sourceLast budget owners later original
  apply SampledFragment.ofIndexed (fun vertex => (Fin.cast left.boundaryColumns_eq column, vertex)) (fun vertex =>
    ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow => coefficients basisRow * values basisRow
    vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
  apply SampledFragment.ofReadback fragment rfl
  intro vertex
  have equal := block.horizontalFragment_values (originals := originals) (coefficients := coefficients)
    trace (Fin.cast left.boundaryColumns_eq column) sourceFirst sourceLast budget owners later original values readback
      vertex
  exact congrArg ConjugateIncrementComparison.conjugateFirst (congrArg₂ PrimitivePoint.mk equal equal)

/-- Attach the retained junction sample to its exact whole-side vertex positions. -/
@[expose] def certifiedHorizontalJunction (trace : side.Trace depth) (column : Fin left.boundaryColumns) {forward :
  Bool}
    (block : ParentBlocks.ParentBlock occurrence false forward
      (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column.castSucc).val]'(Fin.cast
        left.boundaryColumns_eq column.castSucc).isLt))
    {covers : SourceLocations.BasisSourceCovers (ParentBlocks.cacheParent occurrence block.index)}
    {sourceIndex faceIndex : Nat}
    {originals : BasisSourceLocations.PrimitiveBank covers sourceIndex}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data : FragmentQueries.RowData occurrence
      faceIndex}
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget (1) allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    JoinedFragments.SampledFragment (originals := originals) (coefficients := coefficients) (data := data)
      (JoinedSampleBlocks.JunctionValues (fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun
        basisRow => coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
      (side.pieceVertices depth column.castSucc) (side.pieceVertices depth column.succ)) := by
  let fragment := block.horizontalJunction (originals := originals) (coefficients := coefficients)
    trace column sourceFirst sourceLast budget owners later original
  apply SampledFragment.ofReadback fragment rfl
  intro vertex
  have equal := block.horizontalJunction_values (originals := originals) (coefficients := coefficients)
    trace column sourceFirst sourceLast budget owners later original values readback vertex
  have point := congrArg ConjugateIncrementComparison.conjugateFirst (congrArg₂ PrimitivePoint.mk equal equal)
  refine point.trans ?_
  by_cases zero : vertex.val = 0
  · simp only [JoinedSampleBlocks.JunctionValues, if_pos zero, -eq_self, -iff_self]
    rfl
  · simp only [JoinedSampleBlocks.JunctionValues, if_neg zero, -eq_self, -iff_self]
    rfl

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}

/-- Attach the retained piece sample to its exact whole-side vertex positions. -/
@[expose] def certifiedVerticalPiece (trace : side.Trace depth) (row : Fin (left.boundaryRows + 1)) {forward : Bool}
    (block : ParentBlocks.ParentBlock occurrence true forward
      (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row).val]'(Fin.cast left.boundaryRows_eq row).isLt))
    {covers : SourceLocations.BasisSourceCovers (ParentBlocks.cacheParent occurrence block.index)}
    {sourceIndex faceIndex : Nat}
    {originals : BasisSourceLocations.PrimitiveBank covers sourceIndex}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data : FragmentQueries.RowData occurrence
      faceIndex}
    (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
      (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    JoinedFragments.SampledFragment (originals := originals) (coefficients := coefficients) (data := data)
      (fun vertex => ((fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow => coefficients
        basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ :
          Stokes.PrimitivePoint))) ((side.pieceVertices depth row).indexed vertex)) := by
  let fragment := block.verticalFragment (originals := originals) (coefficients := coefficients)
    trace (Fin.cast left.boundaryRows_eq row) sourceFirst sourceLast budget owners later original
  apply SampledFragment.ofIndexed (fun vertex => (Fin.cast left.boundaryRows_eq row, vertex)) (fun vertex =>
    ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun basisRow => coefficients basisRow * values basisRow
    vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
  apply SampledFragment.ofReadback fragment rfl
  intro vertex
  have equal := block.verticalFragment_values (originals := originals) (coefficients := coefficients)
    trace (Fin.cast left.boundaryRows_eq row) sourceFirst sourceLast budget owners later original values readback vertex
  exact congrArg ConjugateIncrementComparison.conjugateFirst (congrArg₂ PrimitivePoint.mk equal equal)

/-- Attach the retained junction sample to its exact whole-side vertex positions. -/
@[expose] def certifiedVerticalJunction (trace : side.Trace depth) (row : Fin left.boundaryRows) {forward : Bool}
    (block : ParentBlocks.ParentBlock occurrence true forward
      (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row.castSucc).val]'(Fin.cast left.boundaryRows_eq
        row.castSucc).isLt))
    {covers : SourceLocations.BasisSourceCovers (ParentBlocks.cacheParent occurrence block.index)}
    {sourceIndex faceIndex : Nat}
    {originals : BasisSourceLocations.PrimitiveBank covers sourceIndex}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data : FragmentQueries.RowData occurrence
      faceIndex}
    (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget (1) allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
      :
    JoinedFragments.SampledFragment (originals := originals) (coefficients := coefficients) (data := data)
      (JoinedSampleBlocks.JunctionValues (fun vertex => ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun
        basisRow => coefficients basisRow * values basisRow vertex),
        FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow vertex)⟩ : Stokes.PrimitivePoint))
      (side.pieceVertices depth row.castSucc) (side.pieceVertices depth row.succ)) := by
  let fragment := block.verticalJunction (originals := originals) (coefficients := coefficients)
    trace row sourceFirst sourceLast budget owners later original
  apply SampledFragment.ofReadback fragment rfl
  intro vertex
  have equal := block.verticalJunction_values (originals := originals) (coefficients := coefficients)
    trace row sourceFirst sourceLast budget owners later original values readback vertex
  have point := congrArg ConjugateIncrementComparison.conjugateFirst (congrArg₂ PrimitivePoint.mk equal equal)
  refine point.trans ?_
  by_cases zero : vertex.val = 0
  · simp only [JoinedSampleBlocks.JunctionValues, if_pos zero, -eq_self, -iff_self]
    rfl
  · simp only [JoinedSampleBlocks.JunctionValues, if_neg zero, -eq_self, -iff_self]
    rfl

end Vertical
end ParentBlock
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
