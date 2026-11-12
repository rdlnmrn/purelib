module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseVerticalChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBudgetReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
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
import Purelib.Data.Rat.Fraction.Order.Basic
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
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Integration.Path

public section

/-! The actual side groups inherit the selected piece and junction budgets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideBudgets

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

variable (retained : Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : RectangularInverseModels.Geometry lc lr} {rg :
    RectangularInverseModels.Geometry rc rr}
  {leftCuts : Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Geometry.Rational.Box}
  {left : Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {data : FragmentQueries.RowData
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  InverseRootPolynomial.Coordinate}
  {side : Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth)
  (blocks : ParentBank.ParentBlockBank
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) left false true)
  (sourceFirst : (ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : InverseRootPolynomial.Coordinate} (budget :
  NoisyPathArea.LengthErrorBudget
  (Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
  NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains.horizontalItems retained
  (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance

/-- Every piece and stationary junction in the forward horizontal word retains the supplied allowance and tolerance
bounds. -/
theorem horizontal_items_budget : ∀ item ∈ items,
    item.fragment.allowance ≤ allowanceBound ∧ item.fragment.budget.tolerance ≤ toleranceBound := by
  apply GroupedBudgets.indexedSideFragments_budget
  · intro position
    exact ⟨(PhysicalBudgetReadback.horizontalPieces_allowance retained
      inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceAllowance,
      (PhysicalBudgetReadback.horizontalPieces_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceTolerance⟩
  · intro position
    exact ⟨(PhysicalBudgetReadback.horizontalJunctions_allowance
      retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionAllowanceBound,
      (PhysicalBudgetReadback.horizontalJunctions_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionTolerance⟩

open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping the forward horizontal word by its original parents preserves both budget bounds for every retained
fragment. -/
theorem horizontal_grouped_budget : ∀ run ∈
  (FragmentGrouping.IndexedGrouping.build items).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound :=
  GroupedBudgets.IndexedGrouping.run_budget
    (FragmentGrouping.IndexedGrouping.build items)
    (SideBudgets.horizontal_items_budget retained inputs outer trace
      blocks sourceFirst sourceLast
      budget owners later original values readback junctionBudget junctionOwners junctionLater
      pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance)

end Horizontal
section Horizontal
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length} {height :
  InverseRootPolynomial.Coordinate}
  {side : Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right
    leftRow rightRow height}
  (trace : side.Trace depth)
  (blocks : ParentBank.ParentBlockBank
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) left false false)
  (sourceFirst : (ParentIndices.occurrenceAt
    prepared.occurrences outer).start.im = height)
  (sourceLast : (ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.im = height)

variable {allowance : InverseRootPolynomial.Coordinate} (budget :
  NoisyPathArea.LengthErrorBudget
  (Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
  NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains.horizontalReverseItems
  retained (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance

/-- Every piece and stationary junction in the reversed horizontal word retains the supplied allowance and tolerance
bounds. -/
theorem horizontal_reverse_items_budget : ∀ item ∈ items,
    item.fragment.allowance ≤ allowanceBound ∧ item.fragment.budget.tolerance ≤ toleranceBound := by
  apply GroupedBudgets.indexedSideFragments_budget
  · intro position
    exact ⟨(PhysicalBudgetReadback.horizontalPieces_allowance retained
      inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceAllowance,
      (PhysicalBudgetReadback.horizontalPieces_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceTolerance⟩
  · intro position
    exact ⟨(PhysicalBudgetReadback.horizontalJunctions_allowance
      retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionAllowanceBound,
      (PhysicalBudgetReadback.horizontalJunctions_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionTolerance⟩

open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping the reversed horizontal word by its original parents preserves both budget bounds for every retained
fragment. -/
theorem horizontal_reverse_grouped_budget : ∀ run ∈
  (FragmentGrouping.IndexedGrouping.build items).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound :=
  GroupedBudgets.IndexedGrouping.run_budget
    (FragmentGrouping.IndexedGrouping.build items)
    (SideBudgets.horizontal_reverse_items_budget retained inputs outer
      trace blocks sourceFirst sourceLast
      budget owners later original values readback junctionBudget junctionOwners junctionLater
      pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance)

end Horizontal
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : InverseRootPolynomial.Coordinate}
  {side : Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth)
  (blocks : ParentBank.ParentBlockBank
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) left true true)
  (sourceFirst : (ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

variable {allowance : InverseRootPolynomial.Coordinate} (budget :
  NoisyPathArea.LengthErrorBudget
  (Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
  NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains.verticalItems
  retained (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance

/-- Every piece and stationary junction in the forward vertical word retains the supplied allowance and tolerance
bounds. -/
theorem vertical_items_budget : ∀ item ∈ items,
    item.fragment.allowance ≤ allowanceBound ∧ item.fragment.budget.tolerance ≤ toleranceBound := by
  apply GroupedBudgets.indexedSideFragments_budget
  · intro position
    exact ⟨(PhysicalBudgetReadback.verticalPieces_allowance retained
      inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceAllowance,
      (PhysicalBudgetReadback.verticalPieces_tolerance retained inputs
        outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceTolerance⟩
  · intro position
    exact ⟨(PhysicalBudgetReadback.verticalJunctions_allowance
      retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionAllowanceBound,
      (PhysicalBudgetReadback.verticalJunctions_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionTolerance⟩

open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping the forward vertical word by its original parents preserves both budget bounds for every retained fragment.
-/
theorem vertical_grouped_budget : ∀ run ∈
  (FragmentGrouping.IndexedGrouping.build items).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound :=
  GroupedBudgets.IndexedGrouping.run_budget
    (FragmentGrouping.IndexedGrouping.build items)
    (SideBudgets.vertical_items_budget retained inputs outer trace
      blocks sourceFirst sourceLast
      budget owners later original values readback junctionBudget junctionOwners junctionLater
      pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance)

end Vertical
section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : InverseRootPolynomial.Coordinate}
  {side : Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth)
  (blocks : ParentBank.ParentBlockBank
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) left true false)
  (sourceFirst : (ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

variable {allowance : InverseRootPolynomial.Coordinate} (budget :
  NoisyPathArea.LengthErrorBudget
  (Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
  NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

local notation "items" =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseVerticalChains.verticalReverseItems retained
  (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance

/-- Every piece and stationary junction in the reversed vertical word retains the supplied allowance and tolerance
bounds. -/
theorem vertical_reverse_items_budget : ∀ item ∈ items,
    item.fragment.allowance ≤ allowanceBound ∧ item.fragment.budget.tolerance ≤ toleranceBound := by
  apply GroupedBudgets.indexedSideFragments_budget
  · intro position
    exact ⟨(PhysicalBudgetReadback.verticalPieces_allowance retained
      inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceAllowance,
      (PhysicalBudgetReadback.verticalPieces_tolerance retained inputs
        outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position).trans_le pieceTolerance⟩
  · intro position
    exact ⟨(PhysicalBudgetReadback.verticalJunctions_allowance
      retained inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionAllowanceBound,
      (PhysicalBudgetReadback.verticalJunctions_tolerance retained
        inputs outer trace blocks sourceFirst sourceLast
        junctionBudget junctionOwners junctionLater original values readback position).trans_le junctionTolerance⟩

open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Grouping the reversed vertical word by its original parents preserves both budget bounds for every retained
fragment. -/
theorem vertical_reverse_grouped_budget : ∀ run ∈
  (FragmentGrouping.IndexedGrouping.build items).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound :=
  GroupedBudgets.IndexedGrouping.run_budget
    (FragmentGrouping.IndexedGrouping.build items)
    (SideBudgets.vertical_reverse_items_budget retained inputs outer
      trace blocks sourceFirst sourceLast
      budget owners later original values readback junctionBudget junctionOwners junctionLater
      pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance)

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideBudgets
