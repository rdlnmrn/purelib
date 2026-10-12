module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularSideReadingReadback
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MatchedFragments
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
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
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide

open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Preserve owner junctions in the common-basis matched-side fragment bank. -/
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
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
variable {lc lr rc rr depth : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}

namespace ParentBlock

/-- The retained block's last source parameter lies inside its original source range. -/
public theorem last_inside {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence vertical forward physical) :
    block.parameters.range.lower ≤ block.lastParameter ∧ block.lastParameter ≤ block.parameters.range.upper := by
  cases forward with
  | true => exact ⟨block.parameters.range.ordered.le, le_rfl⟩
  | false => exact ⟨le_rfl, block.parameters.range.ordered.le⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- Retain both original owner readings at one source endpoint and pair them with a constant original source sample. -/
public def ownedJunction {vertical forward : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence vertical forward physical)
    {covers : SourceLocations.BasisSourceCovers (ParentBlocks.cacheParent occurrence block.index)}
    {sourceIndex faceIndex : Nat}
    {originals : BasisSourceLocations.PrimitiveBank covers sourceIndex}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data : FragmentQueries.RowData occurrence
      faceIndex}
    {points : Fin 2 → InverseRootPolynomial.Gaussian}
    (pointEq : ∀ vertex, points vertex = (ParentBlocks.cacheParent occurrence block.index).edge.point
      block.lastParameter)
    {allowance : InverseRootPolynomial.Coordinate} (budget : NoisyPathArea.LengthErrorBudget 1 allowance)
    (owners : OwnerRequest occurrence budget.tolerance) (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data points) :
    OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  let readings : OwnerRequest.OwnedReadings data (fun _ : Fin 2 => (ParentBlocks.cacheParent occurrence
    block.index).edge.point block.lastParameter) :=
    fun row => ⟨(original row).owners, fun vertex => ((original row).point_eq vertex).trans (pointEq vertex),
      (original row).values, (original row).value_eq⟩
  let value := PrimitiveBank.value originals coefficients block.lastParameter
  { member := block.member, piece := block.located.piece, vertices := 1, parameters := fun _ => block.lastParameter
    inside := fun _ => block.located.contains block.last_inside, forward := true, ordered := fun _ => le_rfl
    allowance := allowance, budget := budget, owners := owners, later := later, readings := readings
    owned := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Purelib.Topology.Polygon.Stokes.PrimitivePoint))
    source := CenteredBilinearPath.Sample.build (fun _ => ConjugateIncrementComparison.conjugateFirst (⟨value, value⟩ :
      Purelib.Topology.Polygon.Stokes.PrimitivePoint)) }

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth) (column : Fin left.boundaryColumns) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence false
    forward (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column.castSucc).val]'(Fin.cast
    left.boundaryColumns_eq column.castSucc).isLt))
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

/-- Keep the two cached owner readings at the same physical endpoint. -/
def horizontalJunction : OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock.ownedJunction block
    (fun vertex => (Trace.junction_point trace column vertex).trans
      (block.horizontalParameters trace (Fin.cast left.boundaryColumns_eq column.castSucc) sourceFirst
        sourceLast).last_point)
    budget owners later (fun basisRow => Trace.junctionReadings trace column (original basisRow))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- The retained horizontal owner junction reads the exact coefficient combination of the original adjoining piece
values. -/
theorem horizontalJunction_values (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (vertex : Fin 2) :
    ownedValue (block.horizontalJunction (originals := originals) (coefficients := coefficients) trace column
      sourceFirst sourceLast budget owners later original).readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow
        (if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last else (side.pieceVertices depth
          column.succ).first)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro basisRow
  exact congrArg (fun value => coefficients basisRow * value)
    (Trace.junctionReadings_spec trace column (original basisRow) (values basisRow) (readback basisRow) vertex)

/-- Both original horizontal junction vertices retain the same terminal source parameter. -/
theorem horizontalJunction_parameter (vertex : Fin 2) :
    (block.horizontalJunction (originals := originals) (coefficients := coefficients) trace column
      sourceFirst sourceLast budget owners later original).parameters vertex = block.lastParameter := rfl

/-- The retained horizontal owner junction has zero source-parameter width. -/
theorem horizontalJunction_sourceWidth :
    (block.horizontalJunction (originals := originals) (coefficients := coefficients) trace column
      sourceFirst sourceLast budget owners later original).sourceWidth ≤ 0 := by
  apply SourceSampleResampling.meshWidth_le _ true le_rfl
  intro edge
  exact (sub_self block.lastParameter).le

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth) (row : Fin left.boundaryRows) {forward : Bool}
  (block : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock occurrence true
    forward (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row.castSucc).val]'(Fin.cast left.boundaryRows_eq
    row.castSucc).isLt))
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent occurrence block.index)}
  {sourceIndex faceIndex : Nat}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers sourceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {data :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex}
  (sourceFirst : occurrence.start.re = width) (sourceLast : occurrence.finish.re = width)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 allowance)
  (owners : OwnerRequest occurrence
    budget.tolerance) (later : owners.index ≤ faceIndex)
  (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
    vertex => trace.point (trace.vertices.indexed vertex)))

/-- Keep the two cached owner readings at the same physical endpoint. -/
def verticalJunction : OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock.ownedJunction block
    (fun vertex => (Trace.junction_point trace row vertex).trans
      (block.verticalParameters trace (Fin.cast left.boundaryRows_eq row.castSucc) sourceFirst sourceLast).last_point)
    budget owners later (fun basisRow => Trace.junctionReadings trace row (original basisRow))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- The retained vertical owner junction reads the exact coefficient combination of the original adjoining piece values.
-/
theorem verticalJunction_values (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (vertex : Fin 2) :
    ownedValue (block.verticalJunction (originals := originals) (coefficients := coefficients) trace row
      sourceFirst sourceLast budget owners later original).readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow * values basisRow
        (if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last else (side.pieceVertices depth
          row.succ).first)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro basisRow
  exact congrArg (fun value => coefficients basisRow * value)
    (Trace.junctionReadings_spec trace row (original basisRow) (values basisRow) (readback basisRow) vertex)

/-- Both original vertical junction vertices retain the same terminal source parameter. -/
theorem verticalJunction_parameter (vertex : Fin 2) :
    (block.verticalJunction (originals := originals) (coefficients := coefficients) trace row
      sourceFirst sourceLast budget owners later original).parameters vertex = block.lastParameter := rfl

/-- The retained vertical owner junction has zero source-parameter width. -/
theorem verticalJunction_sourceWidth :
    (block.verticalJunction (originals := originals) (coefficients := coefficients) trace row
      sourceFirst sourceLast budget owners later original).sourceWidth ≤ 0 := by
  apply SourceSampleResampling.meshWidth_le _ true le_rfl
  intro edge
  exact (sub_self block.lastParameter).le

end Vertical
end ParentBlock
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
