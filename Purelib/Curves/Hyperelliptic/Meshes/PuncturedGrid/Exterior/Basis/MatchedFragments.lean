module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentFragments
public import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Readings.RectangularSideReadingReadback
import Init.Data.Fin.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
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
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.TraceLengths

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide

open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Build common-basis fragments from retained matched-side pieces and readings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

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

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
variable {lc lr rc rr depth : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}

/-- Every original dyadic trace step is nondecreasing in its retained parameter. -/
private theorem dyadic_ordered (piece : RectangularPairedSegments.PairedSegmentPiece lg rg) (depth : Nat)
    (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    (RectangularDyadicPairedTrace.dyadic piece depth).parameters edge.castSucc ≤
      (RectangularDyadicPairedTrace.dyadic piece depth).parameters edge.succ := by
  dsimp only [RectangularDyadicPairedTrace.dyadic, RectangularPairedPointBanks.Trace.build]
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact Dyadic.forward_indexed id 0
    (DyadicTrace.tail depth 0 1)
    (Dyadic.tail_forward depth (by decide)) edge

namespace ParentBlock
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth) (column : Fin left.partition.x.intervals.length) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence false
    forward (left.partition.x.intervals[column.val]'column.isLt))

/-- Transport the original cached horizontal piece trace to its selected retained source parent and endpoint parameters.
-/
def horizontalParameters (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height) :
    RectangularTraceParameterReadings.ParentParameters (trace.segments.get column) (ParentBlocks.cacheParent occurrence
      block.index)
      block.firstParameter block.lastParameter :=
  block.traceParameters height sourceFirst sourceLast (trace.segments.get column)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
    (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks in
/-- Extract the cached rows for this physical piece and retain its selected parent. -/
def horizontalFragment : OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  let readings := fun basisRow => Trace.pieceReadings trace (Fin.cast left.boundaryColumns_eq.symm column) (original
    basisRow)
  let transport := block.horizontalParameters trace column sourceFirst sourceLast
  let owned := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
      Purelib.Topology.Polygon.Stokes.PrimitivePoint))
  let source := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (⟨PrimitiveBank.value originals coefficients (transport.parameters vertex), PrimitiveBank.value originals
      coefficients (transport.parameters vertex)⟩ : Purelib.Topology.Polygon.Stokes.PrimitivePoint))
  OwnedFragment.ofTrace block.member block.located forward transport
    (by intro edge; rw [trace.segments_eq]; exact dyadic_ordered _ depth edge)
    budget owners later readings owned source

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- The retained horizontal fragment's coefficient reading is the exact combination of the original physical piece
values. -/
theorem horizontalFragment_values (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1)) :
    ownedValue (block.horizontalFragment (originals := originals) (coefficients := coefficients) trace column
      sourceFirst sourceLast budget owners later original).readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow (column, vertex)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro basisRow
  exact congrArg (fun value => coefficients basisRow * value)
    (Trace.pieceReadings_spec trace (Fin.cast left.boundaryColumns_eq.symm column) (original basisRow)
      (values basisRow) (readback basisRow) vertex)

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth) (row : Fin left.partition.y.intervals.length) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence true
    forward (left.partition.y.intervals[row.val]'row.isLt))

/-- Transport the original cached vertical piece trace to its selected retained source parent and endpoint parameters.
-/
def verticalParameters (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width) :
    RectangularTraceParameterReadings.ParentParameters (trace.segments.get row) (ParentBlocks.cacheParent occurrence
      block.index)
      block.firstParameter block.lastParameter :=
  block.traceParameters width sourceFirst sourceLast (trace.segments.get row)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)
    (by rw [side.first_eq]; rfl) (by rw [side.last_eq]; rfl)

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
    (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks in
/-- Extract the cached rows for this physical piece and retain its selected parent. -/
def verticalFragment : OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  let readings := fun basisRow => Trace.pieceReadings trace (Fin.cast left.boundaryRows_eq.symm row) (original basisRow)
  let transport := block.verticalParameters trace row sourceFirst sourceLast
  let owned := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
      Purelib.Topology.Polygon.Stokes.PrimitivePoint))
  let source := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    (⟨PrimitiveBank.value originals coefficients (transport.parameters vertex), PrimitiveBank.value originals
      coefficients (transport.parameters vertex)⟩ : Purelib.Topology.Polygon.Stokes.PrimitivePoint))
  OwnedFragment.ofTrace block.member block.located forward transport
    (by intro edge; rw [trace.segments_eq]; exact dyadic_ordered _ depth edge)
    budget owners later readings owned source

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- The retained vertical fragment's coefficient reading is the exact combination of the original physical piece values.
-/
theorem verticalFragment_values (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1)) :
    ownedValue (block.verticalFragment (originals := originals) (coefficients := coefficients) trace row
      sourceFirst sourceLast budget owners later original).readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow (row, vertex)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro basisRow
  exact congrArg (fun value => coefficients basisRow * value)
    (Trace.pieceReadings_spec trace (Fin.cast left.boundaryRows_eq.symm row) (original basisRow)
      (values basisRow) (readback basisRow) vertex)

end Vertical
end ParentBlock
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
