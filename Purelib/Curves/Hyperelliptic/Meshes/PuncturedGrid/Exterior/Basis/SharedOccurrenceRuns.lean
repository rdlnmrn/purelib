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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceConstant
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly

public section

/-! Select the retained rectangle side and traversal directly from each occurrence. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

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

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization.RectangularInverseModels

section SharedOccurrenceRuns
variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage : Nat}
  {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position).domain
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) (cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
  (banks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter.Banks (occurrence :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) traces
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- Fix the run request capacity from the mesh before numerical acquisition. -/
@[expose] def sideCapacity : Nat :=
  match (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.side with
  | .bottom | .top => 2 * mesh.boundaryColumns + 1
  | .left | .right => 2 * mesh.boundaryRows + 1

/-- The selected scalar is read from the same four cached weighted side samples
as the perimeter-to-triangle comparison. -/
@[expose] def sideArea : Gaussian :=
  ((banks.sample traces cache coefficients).get traces cache coefficients
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.side).centeredArea

variable {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
  (Paths.RectangularDyadicPairedTrace.dyadicCount mesh.depth) allowance)
  (owners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ stage)
  (blocks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceVertical (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
      prepared.occurrences outer).sourceForward)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

/-- No side, axis, traversal sign or fixed-coordinate evidence is supplied by
an independent caller: all four cases read the retained occurrence geometry. -/
@[expose] def build : PhysicalRunBank retained inputs
  outer coefficients stage mesh.depth
  (sideCapacity outer (mesh
  := mesh))
    (sideArea outer traces
      cache banks coefficients)
    (max allowance junctionAllowance) (max budget.tolerance junctionBudget.tolerance) := by
  cases side : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.side with
  | bottom =>
    have fixed : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceConstant =
        (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0).val]'(Fin.cast mesh.boundaryRows_eq 0).isLt).lower
          := by
      have original : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceConstant =
          (base.faces.regulars[(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
            prepared.occurrences outer).sideOccurrence.position.val]'
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
              outer).sideOccurrence.position.isLt).cell.box.yLower := by
        simp only
          [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceConstant,
          side, -eq_self, -iff_self]
        rfl
      exact original.trans ((congrArg (fun box : Rational.Box => box.yLower) boxEq).symm.trans
        mesh.y_first.symm)
    have selected :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrence.SharedHorizontalRuns.forOccurrence retained
      inputs outer traces.bottom cache banks.bottom coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).bottom_axis side) fixed boxEq
    unfold sideArea
      sideCapacity
    rw [side]
    exact selected
  | top =>
    have fixed : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceConstant =
        (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).val]'(Fin.cast
          mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).isLt).upper := by
      have original : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceConstant =
          (base.faces.regulars[(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
            prepared.occurrences outer).sideOccurrence.position.val]'
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
              outer).sideOccurrence.position.isLt).cell.box.yUpper := by
        simp only
          [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceConstant,
          side, -eq_self, -iff_self]
        rfl
      exact original.trans ((congrArg (fun box : Rational.Box => box.yUpper) boxEq).symm.trans
        mesh.y_last.symm)
    have selected :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrence.SharedHorizontalRuns.forOccurrence retained
      inputs outer traces.top cache banks.top coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).top_axis side) fixed boxEq
    unfold sideArea
      sideCapacity
    rw [side]
    exact selected
  | left =>
    have fixed : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceConstant =
        (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0).val]'(Fin.cast mesh.boundaryColumns_eq
          0).isLt).lower := by
      have original : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceConstant =
          (base.faces.regulars[(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
            prepared.occurrences outer).sideOccurrence.position.val]'
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
              outer).sideOccurrence.position.isLt).cell.box.xLower := by
        simp only
          [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceConstant,
          side, -eq_self, -iff_self]
        rfl
      exact original.trans ((congrArg (fun box : Rational.Box => box.xLower) boxEq).symm.trans
        mesh.x_first.symm)
    have selected :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence.SharedVerticalRuns.forOccurrence retained
      inputs outer traces.left cache banks.left coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).left_axis side) fixed boxEq
    unfold sideArea
      sideCapacity
    rw [side]
    exact selected
  | right =>
    have fixed : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).sourceConstant =
        (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).val]'(Fin.cast
          mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).isLt).upper := by
      have original : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceConstant =
          (base.faces.regulars[(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
            prepared.occurrences outer).sideOccurrence.position.val]'
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
              outer).sideOccurrence.position.isLt).cell.box.xUpper := by
        simp only
          [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceConstant,
          side, -eq_self, -iff_self]
        rfl
      exact original.trans ((congrArg (fun box : Rational.Box => box.xUpper) boxEq).symm.trans
        mesh.x_last.symm)
    have selected :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence.SharedVerticalRuns.forOccurrence retained
      inputs outer traces.right cache banks.right coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).right_axis side) fixed boxEq
    unfold sideArea
      sideCapacity
    rw [side]
    exact selected

end SharedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
