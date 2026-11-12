module
import Purelib.Data.List.Reverse
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideBudgets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalRuns
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Paid fragment budgets on the shared Newton side banks in both orientations. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace SharedHorizontalRuns
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
  (forwardOrdered reverseOrdered)
variable (retained : Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  (ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain (ParentIndices.occurrenceAt
  prepared.occurrences outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstRow secondRow : Fin mesh.partition.y.intervals.length} {height : InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide mesh mesh firstRow secondRow
    height}
  (trace : side.Trace depth) (cache : RegularDomainMeshes.RegularMeshes.Numerics
    domains stage)
  (bank : SharedSideBanks.SharedHorizontalBank.Data (occurrence :=
    ParentIndices.occurrenceAt prepared.occurrences outer) trace
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (sourceFirst : (ParentIndices.occurrenceAt prepared.occurrences
    outer).start.im = height)
  (sourceLast : (ParentIndices.occurrenceAt prepared.occurrences
    outer).finish.im = height)
  {allowance : InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
section Forward
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh false
  true)

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = false)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = true)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The source-ordered shared horizontal runs retain every supplied fragment allowance and tolerance bound. -/
theorem forward_budget : ∀ run ∈ (forwardOrdered retained inputs outer trace cache bank coefficients sourceFirst
  sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound := by
  intro run member
  exact SideBudgets.horizontal_grouped_budget retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
      run member

end Forward
section Reverse
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh false
  false)

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = false)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = false)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The reversed source-ordered shared horizontal runs retain every supplied fragment allowance and tolerance bound. -/
theorem reverse_budget : ∀ run ∈ (reverseOrdered retained inputs outer trace cache bank coefficients sourceFirst
  sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound := by
  intro run member
  exact SideBudgets.horizontal_reverse_grouped_budget retained (data
    := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
      run ((Data.List.Reverse.mem_reverse _).mp member)

end Reverse
end SharedHorizontalRuns
namespace SharedVerticalRuns
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalRuns
  (forwardOrdered reverseOrdered)
variable (retained : Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  (ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain (ParentIndices.occurrenceAt
  prepared.occurrences outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstColumn secondColumn : Fin mesh.partition.x.intervals.length} {width :
    InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide mesh mesh firstColumn
    secondColumn width}
  (trace : side.Trace depth) (cache : RegularDomainMeshes.RegularMeshes.Numerics
    domains stage)
  (bank : SharedSideBanks.SharedVerticalBank.Data (occurrence :=
    ParentIndices.occurrenceAt prepared.occurrences outer) trace
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (sourceFirst : (ParentIndices.occurrenceAt prepared.occurrences
    outer).start.re = width)
  (sourceLast : (ParentIndices.occurrenceAt prepared.occurrences
    outer).finish.re = width)
  {allowance : InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

variable {allowanceBound toleranceBound : InverseRootPolynomial.Coordinate}
  (pieceAllowance : allowance ≤ allowanceBound) (junctionAllowanceBound : junctionAllowance ≤ allowanceBound)
  (pieceTolerance : budget.tolerance ≤ toleranceBound) (junctionTolerance : junctionBudget.tolerance ≤ toleranceBound)

include pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
section Forward
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh true
  true)

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = true)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = true)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The source-ordered shared vertical runs retain every supplied fragment allowance and tolerance bound. -/
theorem forward_budget : ∀ run ∈ (forwardOrdered retained inputs outer trace cache bank coefficients sourceFirst
  sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound := by
  intro run member
  exact SideBudgets.vertical_grouped_budget retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedVerticalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
      run member

end Forward
section Reverse
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh true
  false)

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = true)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = false)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The reversed source-ordered shared vertical runs retain every supplied fragment allowance and tolerance bound. -/
theorem reverse_budget : ∀ run ∈ (reverseOrdered retained inputs outer trace cache bank coefficients sourceFirst
  sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    ∀ fragment ∈ run.fragments,
      fragment.allowance ≤ allowanceBound ∧ fragment.budget.tolerance ≤ toleranceBound := by
  intro run member
  exact SideBudgets.vertical_reverse_grouped_budget retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedVerticalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater pieceAllowance junctionAllowanceBound pieceTolerance junctionTolerance
      run ((Data.List.Reverse.mem_reverse _).mp member)

end Reverse
end SharedVerticalRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets
