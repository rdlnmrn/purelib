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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
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
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
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
import Purelib.Topology.Polygon.Stokes

public section

/-! Join cached owner junctions to the next canonical physical piece. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.NextPieceJoins

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

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
    (column : Fin left.boundaryColumns)

variable {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "nextPiece" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryColumns_eq column.succ))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) column.succ)

local notation "junction" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryColumns_eq column.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.horizontalJunctions retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback) column)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Actual interval adjacency supplies both the parent-index step and the
source-parameter handoff, including transitions between different parents. -/
theorem horizontalJunctions_handoff
    (axis : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceVertical = false)
    (orientation : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward = true) :
    ((nextPiece).parent.val = (junction).parent.val ∨
      (nextPiece).parent.val = (junction).parent.val + 1) ∧ (junction).Joined (nextPiece) := by
  let before := blocks.get (Fin.cast left.boundaryColumns_eq column.castSucc)
  let after := blocks.get (Fin.cast left.boundaryColumns_eq column.succ)
  have consecutive :
      (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column.succ).val]'(Fin.cast left.boundaryColumns_eq
        column.succ).isLt).lower =
      (left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq column.castSucc).val]'(Fin.cast
        left.boundaryColumns_eq column.castSucc).isLt).upper :=
    (left.partition.x.consecutive column.val (Fin.cast left.boundaryColumns_eq column.succ).isLt).symm
  have transition :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs.ParentBlock.consecutive_parent_handoff before after
    (fun parent member => by
    have ordered := Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) member
    simpa only [axis, orientation, Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis, if_pos
      (rfl : true = true), if_neg Bool.false_ne_true, -eq_self, -iff_self] using ordered) consecutive
  have lastRead : (junction).lastParameter = before.lastParameter :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback.horizontalJunctions_last retained inputs
      outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback column
  have firstRead : (nextPiece).firstParameter = after.firstParameter :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback.horizontalPieces_first retained inputs
      outer trace blocks sourceFirst sourceLast
      budget owners later original values readback column.succ
  constructor
  · rcases transition with same | next
    · exact Or.inl (congrArg Fin.val same.1)
    · exact Or.inr next.1
  constructor
  · intro same
    have joined := before.same_parent_parameters after same.symm consecutive
    exact lastRead.trans (joined.symm.trans firstRead.symm)
  · intro different
    rcases transition with same | next
    · exact (different same.1.symm).elim
    · exact ⟨lastRead.trans next.2.1, firstRead.trans next.2.2⟩

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth)
  (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left true true)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

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
    (row : Fin left.boundaryRows)

variable {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "nextPiece" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryRows_eq row.succ))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later original values readback) row.succ)

local notation "junction" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
  (Purelib.Data.Vector.DependentVector.get blocks (Fin.cast left.boundaryRows_eq row.castSucc))
  (Purelib.Data.Vector.DependentVector.get
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalJunctions retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast junctionBudget junctionOwners junctionLater original values readback) row)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Actual interval adjacency supplies both the parent-index step and the
source-parameter handoff, including transitions between different parents. -/
theorem verticalJunctions_handoff
    (axis : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceVertical = true)
    (orientation : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceForward = true) :
    ((nextPiece).parent.val = (junction).parent.val ∨
      (nextPiece).parent.val = (junction).parent.val + 1) ∧ (junction).Joined (nextPiece) := by
  let before := blocks.get (Fin.cast left.boundaryRows_eq row.castSucc)
  let after := blocks.get (Fin.cast left.boundaryRows_eq row.succ)
  have consecutive :
      (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row.succ).val]'(Fin.cast left.boundaryRows_eq
        row.succ).isLt).lower =
      (left.partition.y.intervals[(Fin.cast left.boundaryRows_eq row.castSucc).val]'(Fin.cast left.boundaryRows_eq
        row.castSucc).isLt).upper :=
    (left.partition.y.consecutive row.val (Fin.cast left.boundaryRows_eq row.succ).isLt).symm
  have transition :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentHandoffs.ParentBlock.consecutive_parent_handoff before after
    (fun parent member => by
    have ordered := Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.source_parent_ordered
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) member
    simpa only [axis, orientation, Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis, if_pos
      (rfl : true = true), if_neg Bool.false_ne_true, -eq_self, -iff_self] using ordered) consecutive
  have lastRead : (junction).lastParameter = before.lastParameter :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback.verticalJunctions_last retained inputs
      outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback row
  have firstRead : (nextPiece).firstParameter = after.firstParameter :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback.verticalPieces_first retained inputs
      outer trace blocks sourceFirst sourceLast
      budget owners later original values readback row.succ
  constructor
  · rcases transition with same | next
    · exact Or.inl (congrArg Fin.val same.1)
    · exact Or.inr next.1
  constructor
  · intro same
    have joined := before.same_parent_parameters after same.symm consecutive
    exact lastRead.trans (joined.symm.trans firstRead.symm)
  · intro different
    rcases transition with same | next
    · exact (different same.1.symm).elim
    · exact ⟨lastRead.trans next.2.1, firstRead.trans next.2.2⟩

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.NextPieceJoins
