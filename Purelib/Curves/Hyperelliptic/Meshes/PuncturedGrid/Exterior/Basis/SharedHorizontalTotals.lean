module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps

@[expose] public section

/-! Exact physical side words and endpoint totals on the acquired Newton readings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Normalization.RectangularInverseModels

variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth)
  (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left false true)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains.horizontalItems retained
  (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank in
open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping retains every physical increment, including owner junctions. -/
theorem horizontal_grouped_increments
    (sample : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex)),
        FiniteSum.Fin.sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex))⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) :
    ((((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs.map (fun
      run => run.fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair)).flatten).map
      Prod.fst).flatten =
      Path.CenteredPathIncrements.Sample.increments sample := by
  rw [(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).pairs_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains.horizontalItems
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments_pairs]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback.pairedSideBlocks_flatten
    (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row * values row
      vertex),
      FiniteSum.Fin.sumFin (fun row => coefficients row * values row vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (fun position => left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq position).val]'
      (Fin.cast left.boundaryColumns_eq position).isLt)
    (fun position => blocks.get (Fin.cast left.boundaryColumns_eq position))
    (side.pieceVertices depth)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained inputs
      outer trace blocks sourceFirst sourceLast
      budget owners later original values readback).get position)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalJunctions retained
      inputs outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback).get position)
    sample trace.vertices_eq

end Horizontal
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Normalization.RectangularInverseModels

variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth)
  (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left false false)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains.horizontalReverseItems
  retained (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank in
open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping retains every physical increment, including owner junctions. -/
theorem horizontal_reverse_grouped_increments
    (sample : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex)),
        FiniteSum.Fin.sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex))⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) :
    ((((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs.map (fun
      run => run.fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair)).flatten).map
      Prod.fst).flatten =
      Path.CenteredPathIncrements.Sample.increments sample := by
  rw [(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).pairs_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains.horizontalReverseItems
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments_pairs]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback.pairedSideBlocks_flatten
    (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row * values row
      vertex),
      FiniteSum.Fin.sumFin (fun row => coefficients row * values row vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (fun position => left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq position).val]'
      (Fin.cast left.boundaryColumns_eq position).isLt)
    (fun position => blocks.get (Fin.cast left.boundaryColumns_eq position))
    (side.pieceVertices depth)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained inputs
      outer trace blocks sourceFirst sourceLast
      budget owners later original values readback).get position)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalJunctions retained
      inputs outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback).get position)
    sample trace.vertices_eq

end Horizontal
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Normalization.RectangularInverseModels

namespace SharedHorizontalRuns
variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstRow secondRow : Fin mesh.partition.y.intervals.length} {height :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide mesh mesh
    firstRow secondRow height}
  (trace : side.Trace depth) (cache :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.Data
    (occurrence := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer) trace cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
    (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

section Forward
variable (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer) mesh false true)

variable (axis : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).sourceVertical = false)
  (orientation : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward = true)
  (boxEq : meshBox =
    (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

open Purelib.Algebra
open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann
/-- The acquired source-ordered bank retains the complete oriented side word. -/
theorem forward_increments : (List.ofFn
  (SharedHorizontalRuns.forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical).flatten =
    Path.CenteredPathIncrements.Sample.increments
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients) := by
  have path := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build
    (SharedHorizontalRuns.forward retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    |> fun grouped =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths.IndexedGrouping.source_order_physical grouped
    (SharedHorizontalRuns.forward_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2
  apply path.trans
  have readback :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals.horizontal_grouped_increments retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients)
  have grouped := congrArg (fun pairs : List (List Topology.Polygon.Stokes.PrimitivePoint × List
    Topology.Polygon.Stokes.PrimitivePoint) =>
    (pairs.map Prod.fst).flatten)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build
      (SharedHorizontalRuns.forward retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks)).pairs_eq
  exact grouped.symm.trans readback

/-- The complete acquired side telescopes on its retained Newton endpoint readings. -/
theorem forward_total : Path.PairedIncrementArea.total (List.ofFn
  (SharedHorizontalRuns.forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical).flatten =
    (Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
      (trace.vertices.indexed (Fin.last trace.vertices.rest.length))),
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
        (trace.vertices.indexed (Fin.last trace.vertices.rest.length)))⟩ : Topology.Polygon.Stokes.PrimitivePoint)).sub
      (Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
        (trace.vertices.indexed 0)),
        FiniteSum.Fin.sumFin (fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
          (trace.vertices.indexed 0))⟩ : Topology.Polygon.Stokes.PrimitivePoint)) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals.SharedHorizontalRuns.forward_increments
    retained inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq]
  exact Path.CenteredPathIncrements.Sample.increments_total
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
    coefficients)

end Forward

section Reverse
variable (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer) mesh false false)

variable (axis : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).sourceVertical = false)
  (orientation : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward = false)
  (boxEq : meshBox =
    (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
        outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

open Purelib.Algebra
open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann
/-- The acquired source-ordered bank retains the complete oriented side word. -/
theorem reverse_increments : (List.ofFn (fun position => Path.PairedAreaReversal.reverseIncrements
  ((SharedHorizontalRuns.reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical
      position))).flatten =
    Path.PairedAreaReversal.reverseIncrements (Path.CenteredPathIncrements.Sample.increments
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients)) := by
  have path := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build
    (SharedHorizontalRuns.reverse retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    |> fun grouped =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths.IndexedGrouping.reverse_source_order_physical
      grouped
    (SharedHorizontalRuns.reverse_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2
  apply path.trans
  have readback :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals.horizontal_reverse_grouped_increments
    retained (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients)
  have grouped := congrArg (fun pairs : List (List Topology.Polygon.Stokes.PrimitivePoint × List
    Topology.Polygon.Stokes.PrimitivePoint) =>
    (pairs.map Prod.fst).flatten)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build
      (SharedHorizontalRuns.reverse retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks)).pairs_eq
  exact congrArg Path.PairedAreaReversal.reverseIncrements (grouped.symm.trans readback)

/-- The complete acquired side telescopes on its retained Newton endpoint readings. -/
theorem reverse_total : Path.PairedIncrementArea.total (List.ofFn (fun position =>
  Path.PairedAreaReversal.reverseIncrements
  ((SharedHorizontalRuns.reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical
      position))).flatten =
    Topology.Polygon.Stokes.PrimitivePoint.zero.sub ((Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row
      => coefficients row *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
      (trace.vertices.indexed (Fin.last trace.vertices.rest.length))),
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
        (trace.vertices.indexed (Fin.last trace.vertices.rest.length)))⟩ : Topology.Polygon.Stokes.PrimitivePoint)).sub
      (Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
        (trace.vertices.indexed 0)),
        FiniteSum.Fin.sumFin (fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.values trace cache row
          (trace.vertices.indexed 0))⟩ : Topology.Polygon.Stokes.PrimitivePoint))) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals.SharedHorizontalRuns.reverse_increments
    retained inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq]
  rw [Path.PairedAreaReversal.total_reverseIncrements]
  exact congrArg (Topology.Polygon.Stokes.PrimitivePoint.zero.sub) (Path.CenteredPathIncrements.Sample.increments_total
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
    coefficients))

end Reverse

end SharedHorizontalRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalTotals
