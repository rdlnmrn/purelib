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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalOccurrenceTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Exact physical path readback through the retained rectangle-side selection. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals

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

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace SharedOccurrenceRuns
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

/-- A property holding in each grid-side branch holds for the dependent case split on the retained side. -/
private theorem side_rec_property {side : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide} {T : Sort u}
    (bottom : side = .bottom → T) (right : side = .right → T)
    (top : side = .top → T) (left : side = .left → T) (P : T → Prop)
    (hb : ∀ h, P (bottom h)) (hr : ∀ h, P (right h))
    (ht : ∀ h, P (top h)) (hl : ∀ h, P (left h)) :
    P ((Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.rec (motive := fun t => side = t → T) bottom right top left
      side) rfl) := by
  cases side with
  | bottom => exact hb rfl
  | right => exact hr rfl
  | top => exact ht rfl
  | left => exact hl rfl

/-- Applying a grid-side equality transport agrees with the original value after transporting its argument. -/
private theorem transport_apply {a b : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide} {T : Sort u}
    (value : b = a → T) (equal : a = b) (selfEq : b = b) :
    (Eq.rec (motive := fun x _ => b = x → T) value equal) selfEq = value equal.symm := by
  cases equal
  rfl

/-- Equality transport of side capacity and area preserves the original physical run bank. -/
private theorem physical_side_cast (capacity : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide → Nat) (area :
  Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide → Normalization.InverseRootPolynomial.Gaussian)
    {first last : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide} (equal : first = last)
    (bank : PhysicalRunBank retained inputs outer
      coefficients stage mesh.depth (capacity last) (area last)
      (max allowance junctionAllowance) (max budget.tolerance junctionBudget.tolerance)) :
    (Eq.mpr (congrArg (fun side => PhysicalRunBank
      retained inputs outer coefficients stage mesh.depth
      (capacity side) (area side) (max allowance junctionAllowance)
      (max budget.tolerance junctionBudget.tolerance)) equal) bank).physical = bank.physical := by
  cases equal
  rfl

/-- The actual occurrence builder preserves the selected oriented physical word. -/
theorem build_increments :
    (List.ofFn (SharedOccurrenceRuns.build
      retained inputs outer traces cache banks coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks boxEq).physical).flatten =
      let sample := (banks.sample traces cache coefficients).get traces cache coefficients
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).sideOccurrence.side
      if (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).sourceForward then Path.CenteredPathIncrements.Sample.increments sample
      else Path.PairedAreaReversal.reverseIncrements (Path.CenteredPathIncrements.Sample.increments sample) := by
  unfold SharedOccurrenceRuns.build
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.side_rec_property
    (T := PhysicalRunBank retained inputs outer
    coefficients stage mesh.depth
    (SharedOccurrenceRuns.sideCapacity outer
      (mesh := mesh))
      (SharedOccurrenceRuns.sideArea outer traces
      cache banks coefficients)
    (max allowance junctionAllowance) (max budget.tolerance junctionBudget.tolerance))
    _ _ _ _ (fun bank => (List.ofFn bank.physical).flatten = _)
  · intro side
    dsimp only [Eq.ndrec]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.transport_apply]
    dsimp only [id_eq]
    erw
      [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.physical_side_cast
      (retained := retained) (inputs := inputs) (outer := outer)
      (coefficients := coefficients) (budget := budget) (junctionBudget := junctionBudget) (equal := side)
      (capacity := fun side => match side with
        | .bottom | .top => 2 * mesh.boundaryColumns + 1
        | .left | .right => 2 * mesh.boundaryRows + 1)
      (area := fun side => ((banks.sample traces cache coefficients).get traces cache coefficients side).centeredArea)]
    have words := congrArg (fun chosen =>
      Path.CenteredPathIncrements.Sample.increments ((banks.sample traces cache coefficients).get traces cache
        coefficients chosen)) side
    rw [words]
    exact
      HorizontalOccurrenceTotals.SharedHorizontalRuns.forOccurrence_increments
      retained inputs outer traces.bottom cache banks.bottom coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks _ _ boxEq
  · intro side
    dsimp only [Eq.ndrec]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.transport_apply]
    dsimp only [id_eq]
    erw
      [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.physical_side_cast
      (retained := retained) (inputs := inputs) (outer := outer)
      (coefficients := coefficients) (budget := budget) (junctionBudget := junctionBudget) (equal := side)
      (capacity := fun side => match side with
        | .bottom | .top => 2 * mesh.boundaryColumns + 1
        | .left | .right => 2 * mesh.boundaryRows + 1)
      (area := fun side => ((banks.sample traces cache coefficients).get traces cache coefficients side).centeredArea)]
    have words := congrArg (fun chosen =>
      Path.CenteredPathIncrements.Sample.increments ((banks.sample traces cache coefficients).get traces cache
        coefficients chosen)) side
    rw [words]
    exact
      VerticalOccurrenceTotals.SharedVerticalRuns.forOccurrence_increments
      retained inputs outer traces.right cache banks.right coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks _ _ boxEq
  · intro side
    dsimp only [Eq.ndrec]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.transport_apply]
    dsimp only [id_eq]
    erw
      [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.physical_side_cast
      (retained := retained) (inputs := inputs) (outer := outer)
      (coefficients := coefficients) (budget := budget) (junctionBudget := junctionBudget) (equal := side)
      (capacity := fun side => match side with
        | .bottom | .top => 2 * mesh.boundaryColumns + 1
        | .left | .right => 2 * mesh.boundaryRows + 1)
      (area := fun side => ((banks.sample traces cache coefficients).get traces cache coefficients side).centeredArea)]
    have words := congrArg (fun chosen =>
      Path.CenteredPathIncrements.Sample.increments ((banks.sample traces cache coefficients).get traces cache
        coefficients chosen)) side
    rw [words]
    exact
      HorizontalOccurrenceTotals.SharedHorizontalRuns.forOccurrence_increments
      retained inputs outer traces.top cache banks.top coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks _ _ boxEq
  · intro side
    dsimp only [Eq.ndrec]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.transport_apply]
    dsimp only [id_eq]
    erw
      [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals.SharedOccurrenceRuns.physical_side_cast
      (retained := retained) (inputs := inputs) (outer := outer)
      (coefficients := coefficients) (budget := budget) (junctionBudget := junctionBudget) (equal := side)
      (capacity := fun side => match side with
        | .bottom | .top => 2 * mesh.boundaryColumns + 1
        | .left | .right => 2 * mesh.boundaryRows + 1)
      (area := fun side => ((banks.sample traces cache coefficients).get traces cache coefficients side).centeredArea)]
    have words := congrArg (fun chosen =>
      Path.CenteredPathIncrements.Sample.increments ((banks.sample traces cache coefficients).get traces cache
        coefficients chosen)) side
    rw [words]
    exact
      VerticalOccurrenceTotals.SharedVerticalRuns.forOccurrence_increments
      retained inputs outer traces.left cache banks.left coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks _ _ boxEq

end SharedOccurrenceRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOccurrenceTotals
