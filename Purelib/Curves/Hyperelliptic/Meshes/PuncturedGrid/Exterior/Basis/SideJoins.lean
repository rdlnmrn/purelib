module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
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
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
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
import Purelib.Topology.Polygon.Stokes

public section

/-! Certified handoffs from physical pieces to their retained owner junctions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (blockIndex blockIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.BlockInputs (blockInput)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank (ParentBlockBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis (OwnerRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (horizontalPieces verticalPieces
  horizontalJunctions verticalJunctions)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (SampledFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments (IndexedFragment)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

variable (retained : CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : Geometry lc lr} {rg :
    Geometry rc rr}
  {leftCuts : GridCuts lg} {rightCuts :
    GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : ObservationMesh leftCuts leftBox} {right :
    ObservationMesh rightCuts rightBox}
  {data : RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  Coordinate}
  {side : MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth) {forward : Bool}
  (blocks : ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left false forward)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : Coordinate} (budget :
  LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (column : Fin left.boundaryColumns)

variable {junctionAllowance : Coordinate} (junctionBudget :
  LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "piece" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryColumns_eq column.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) column.castSucc)

local notation "junction" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryColumns_eq column.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalJunctions retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback) column)

/-- The junction reuses the preceding physical piece's parent and terminal parameter, while retaining its separate
physical point-owner readings. -/
theorem horizontalPieces_join_junction : (piece).Joined (junction) := by
  constructor
  · intro _
    exact (PhysicalParameterReadback.horizontalPieces_last retained inputs outer trace blocks sourceFirst sourceLast
      budget owners later original values readback column.castSucc).trans
      (JunctionParameterReadback.horizontalJunctions_first retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback column).symm
  · intro different
    exact (different rfl).elim

/-- Every stationary owner junction is increasing, in either side orientation. -/
theorem horizontalJunctions_increasing : (junction).Increasing := by
  intro edge
  have ordered := (junction).fragment.ordered edge
  have forwardEq := JunctionParameterReadback.horizontalJunctions_forward retained (coefficients := coefficients) inputs
    outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback column
  change (junction).fragment.forward = true at forwardEq
  rw [forwardEq] at ordered
  exact ordered

variable (position : Fin (left.boundaryColumns + 1))
local notation "current" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryColumns_eq position))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) position)

/-- Forward side pieces inherit their stored pointwise parameter order. -/
theorem horizontalPieces_increasing (orientation : forward = true) : (current).Increasing := by
  intro edge
  have ordered := (current).fragment.ordered edge
  have forwardEq := PhysicalParameterReadback.horizontalPieces_forward retained (coefficients := coefficients) inputs
    outer trace blocks
    sourceFirst sourceLast budget owners later original values readback position
  change (current).fragment.forward = forward at forwardEq
  have actual := forwardEq.trans orientation
  rw [actual] at ordered
  exact ordered

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Coordinate}
  {side : MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth) {forward : Bool}
  (blocks : ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left true forward)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

variable {allowance : Coordinate} (budget :
  LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))
    (row : Fin left.boundaryRows)

variable {junctionAllowance : Coordinate} (junctionBudget :
  LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "piece" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryRows_eq row.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) row.castSucc)

local notation "junction" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryRows_eq row.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalJunctions retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback) row)

/-- The junction reuses the preceding physical piece's parent and terminal parameter, while retaining its separate
physical point-owner readings. -/
theorem verticalPieces_join_junction : (piece).Joined (junction) := by
  constructor
  · intro _
    exact (PhysicalParameterReadback.verticalPieces_last retained inputs outer trace blocks sourceFirst sourceLast
      budget owners later original values readback row.castSucc).trans
      (JunctionParameterReadback.verticalJunctions_first retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback row).symm
  · intro different
    exact (different rfl).elim

/-- Every stationary owner junction is increasing, in either side orientation. -/
theorem verticalJunctions_increasing : (junction).Increasing := by
  intro edge
  have ordered := (junction).fragment.ordered edge
  have forwardEq := JunctionParameterReadback.verticalJunctions_forward retained (coefficients := coefficients) inputs
    outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback row
  change (junction).fragment.forward = true at forwardEq
  rw [forwardEq] at ordered
  exact ordered

variable (position : Fin (left.boundaryRows + 1))
local notation "current" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryRows_eq position))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) position)

/-- Forward side pieces inherit their stored pointwise parameter order. -/
theorem verticalPieces_increasing (orientation : forward = true) : (current).Increasing := by
  intro edge
  have ordered := (current).fragment.ordered edge
  have forwardEq := PhysicalParameterReadback.verticalPieces_forward retained (coefficients := coefficients) inputs
    outer trace blocks
    sourceFirst sourceLast budget owners later original values readback position
  change (current).fragment.forward = forward at forwardEq
  have actual := forwardEq.trans orientation
  rw [actual] at ordered
  exact ordered

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins
