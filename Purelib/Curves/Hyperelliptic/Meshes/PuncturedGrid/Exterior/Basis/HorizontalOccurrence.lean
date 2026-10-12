module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceConstant
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets
import Mathlib.Order.Defs.LinearOrder
import Purelib.Algebra.FiniteSum.Fin
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
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly

public section

/-! Attach the actual occurrence direction and fixed coordinate to its cached horizontal bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrence

open Purelib.Data.Rat

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace SharedHorizontalRuns
variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstRow secondRow : Fin mesh.partition.y.intervals.length} {height : Normalization.InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide mesh mesh firstRow secondRow
    height}
  (trace : side.Trace depth) (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage)
  (bank : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.Data (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) trace
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

variable (blocks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceVertical (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
      prepared.occurrences outer).sourceForward)
  (axis : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceVertical = false)
  (fixed : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceConstant = height)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

/-- The source occurrence chooses forward or reversed traversal; both cases
reuse the same retained block assignments, numerical rows and weighted side sample. -/
@[expose] def forOccurrence : PhysicalRunBank retained
  inputs outer coefficients stage depth (2 * mesh.boundaryColumns + 1)
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedHorizontalBank.Data.sample bank
  coefficients).centeredArea
    (max allowance junctionAllowance) (max budget.tolerance junctionBudget.tolerance) := by
  have endpoints := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).source_horizontal_endpoints axis
  have sourceFirst := endpoints.1.trans fixed
  have sourceLast := endpoints.2.trans fixed
  cases direction : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward with
  | false =>
    let selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh
      false false :=
      Eq.mp (congrArg₂ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh)
        axis direction) blocks
    exact PhysicalRunBank.ofReverse
      (SharedHorizontalRuns.reverseOrdered
      retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq) direction
      (SharedHorizontalRuns.reverse_chains
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (SharedHorizontalRuns.reverse_widths
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (SharedHorizontalRuns.reverse_capacity
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns.reverse_budget retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater
        (Fraction.Order.Basic.le_max_left ..) (Fraction.Order.Basic.le_max_right ..) (Fraction.Order.Basic.le_max_left
          ..) (Fraction.Order.Basic.le_max_right ..) selected axis direction boxEq)
      (SharedHorizontalRuns.reverse_area retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
  | true =>
    let selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh
      false true :=
      Eq.mp (congrArg₂ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh)
        axis direction) blocks
    exact PhysicalRunBank.ofForward
      (SharedHorizontalRuns.forwardOrdered
      retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq) direction
      (SharedHorizontalRuns.forward_chains
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (SharedHorizontalRuns.forward_widths
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (SharedHorizontalRuns.forward_capacity
        retained inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedHorizontalRuns.forward_budget retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater
        (Fraction.Order.Basic.le_max_left ..) (Fraction.Order.Basic.le_max_right ..) (Fraction.Order.Basic.le_max_left
          ..) (Fraction.Order.Basic.le_max_right ..) selected axis direction boxEq)
      (SharedHorizontalRuns.forward_area retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
        budget owners later junctionBudget junctionOwners junctionLater selected axis direction boxEq)

end SharedHorizontalRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrence
