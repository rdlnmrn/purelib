module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
import Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring

public section

/-! The shared contact tail pays only joins between retained regular faces.
Physical and excision-interface boundaries are kept in the energy estimate. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ContactEnergy

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary.SynchronizedSurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy.SynchronizedSurfaceRequests
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data.Rat
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
open Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
open Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts.SynchronizedSurfaceRequests
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
open Purelib.Topology.BranchedCover.Double

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (remainingPairedCentered remainingCornerBoundary remainingBoundaryCentered remaining_exterior_eq_corner_boundary)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedEvaluationPartition (pairedEvaluation_bound)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy.SynchronizedSurfaceRequests (contactTarget
  contactTarget_positive contactTarget_paid)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_paid)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests (GlobalContactRequest)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility (Compatible)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (surfaceLowerConstant)
open Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts.SynchronizedSurfaceRequests.PerimeterSamples
  (centered_lifted_error_bound)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (remainingExterior)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest
  (remaining_energy_lower)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (boundaryEnergy_sub_budget_le)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  mul_le_mul_of_nonneg_right_direct)

namespace SynchronizedSurfaceRequests

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error
    : Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace PerimeterSamples

variable {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error}
  {traces : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (samples : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces
    cache coefficients)

/-- The hypothesis is exactly the homogeneous bound supplied by the complete face-side comparison. The finite face count
is paid before taking imaginary parts. -/
theorem remaining_contact_paid {allowance : Fraction.Rational} (positive : 0 < allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.centeredSideSum samples .top first -
        PerimeterSamples.centeredSideSum samples .bottom last) ≤
        (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
          SynchronizedSurfaceRequests.contactTarget genus grid.faces.regulars.length allowance)
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.centeredSideSum samples .right first -
        PerimeterSamples.centeredSideSum samples .left last) ≤
        (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
          SynchronizedSurfaceRequests.contactTarget genus grid.faces.regulars.length allowance) :
    Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.remainingPairedCentered excision samples) ≤ (4 *
      (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
  have bound := SelectedEvaluationPartition.pairedEvaluation_bound
    (ObservationLower.remainingFaceMask excision) (PerimeterSamples.centeredSideSum samples)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (SynchronizedSurfaceRequests.contactTarget_positive positive).le)
        horizontal vertical
  apply bound.trans
  calc
    _ = ((genus : Fraction.Rational) ^ 2 *
        (4 * (grid.faces.regulars.length : Fraction.Rational) ^ 4 * SynchronizedSurfaceRequests.contactTarget genus
          grid.faces.regulars.length allowance)) *
          PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by ring1
    _ ≤ ((genus : Fraction.Rational) ^ 2 * ConjugateRequest.energyAllowanceTarget genus allowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (SynchronizedSurfaceRequests.contactTarget_paid
          positive) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ ≤ (4 * allowance) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (ConjugateRequest.energyAllowanceTarget_paid positive)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = _ := by ring1

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  (mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges grid.faces)

/-- The original sheet-transported contact bounds pay the complete centered paired contribution of the retained
complement. -/
theorem remaining_lifted_contact_paid {allowance : Fraction.Rational} (positive : 0 < allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .bottom ((mesh.locateFace first sheet).lifted.sideFinishSheet .top))
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .left ((mesh.locateFace first sheet).lifted.sideFinishSheet .right))
    (horizontalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).top.centeredArea -
        ((samples.get (horizontal first last matching sheet).sheet).get last).bottom.centeredArea) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        SynchronizedSurfaceRequests.contactTarget genus grid.faces.regulars.length allowance / 4)
    (verticalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).right.centeredArea -
        ((samples.get (vertical first last matching sheet).sheet).get last).left.centeredArea) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        SynchronizedSurfaceRequests.contactTarget genus grid.faces.regulars.length allowance / 4) :
    Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.remainingPairedCentered excision samples) ≤ (4 *
      (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
  apply
    remaining_contact_paid
    excision samples positive
  · intro first last matching
    have bound := PerimeterSamples.centered_lifted_error_bound samples mesh first last .top .bottom
      (horizontal first last matching) (horizontalBound first last matching)
    exact bound.trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  · intro first last matching
    have bound := PerimeterSamples.centered_lifted_error_bound samples mesh first last .right .left
      (vertical first last matching) (verticalBound first last matching)
    exact bound.trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end PerimeterSamples

variable {depth : Nat}
  {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests (fun sheet =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error}
  {compatible : Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions}
  {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges grid.faces} {traces :
    Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}

namespace GlobalContactRequest

variable {allowance : Data.Rat.Fraction.Rational} {floor : Nat}

/-- The acquired global contact request bounds the original remaining-face centered pair sum at every paid stage. -/
theorem remaining_accurate (excision : Excision.AllHoleExcision grid lifted) (request :
  SynchronizedSurfaceRequests.GlobalContactRequest requests compatible mesh traces allowance floor)
    (positive : 0 < allowance) (later : request.index ≤ stage)
    (samples : SynchronizedSurfaceRequests.PerimeterSamples requests traces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.remainingPairedCentered excision samples) ≤
      (4 * (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
  apply
    PerimeterSamples.remaining_lifted_contact_paid
    excision samples mesh positive
    (fun first last _ sheet => HorizontalContact.next (last := last) (mesh.locateFace first sheet))
    (fun first last _ sheet => VerticalContact.next (last := last) (mesh.locateFace first sheet))
  · intro first last matching sheet
    let entry := ((request.horizontal.entries.get first).get last).get sheet
    have contactLater : (entry.contact matching).request.index ≤ stage :=
      (entry.index_eq matching).le.trans ((request.horizontal.entries_le first last sheet).trans
        (request.horizontal_le.trans later))
    exact (entry.contact matching).accurate contactLater cache coefficients
      ((samples.get sheet).get first) ((samples.get _).get last)
  · intro first last matching sheet
    let entry := ((request.vertical.entries.get first).get last).get sheet
    have contactLater : (entry.contact matching).request.index ≤ stage :=
      (entry.index_eq matching).le.trans ((request.vertical.entries_le first last sheet).trans
        (request.vertical_le.trans later))
    exact (entry.contact matching).accurate contactLater cache coefficients
      ((samples.get sheet).get first) ((samples.get _).get last)

end GlobalContactRequest

namespace GlobalEnergyRequest

variable {depth : Nat}
  {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests (fun sheet =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance contactAllowance : Data.Rat.Fraction.Rational}

/-- Only the paid centered contact error is removed from the complete surface lower bound. The surviving corner and
physical terms still require the period bridge. -/
theorem remaining_energy_lower_after_contacts (excision : Excision.AllHoleExcision grid lifted)
    (request : SynchronizedSurfaceRequests.GlobalEnergyRequest requests ownershipAllowance exteriorAllowance
      faceAllowance)
    (later : request.index ≤ stage)
    (readings : Data.Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Attachment.Face)
    {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    {traces : SynchronizedSurfaceRequests.PerimeterTraces requests} (samples :
      SynchronizedSurfaceRequests.PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (positive : 0 < contactAllowance)
    {contactFloor : Nat}
    (contacts : SynchronizedSurfaceRequests.GlobalContactRequest requests compatible mesh traces contactAllowance
      contactFloor)
    (contactLater : contacts.index ≤ stage) :
    (2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) - contactAllowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        (PerimeterSamples.remainingCornerBoundary excision faces + PerimeterSamples.remainingBoundaryCentered excision
          samples neighbors).im / 4 := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Data.Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have difference : PerimeterSamples.remainingExterior excision samples - (PerimeterSamples.remainingCornerBoundary
    excision faces + PerimeterSamples.remainingBoundaryCentered excision samples neighbors) =
      PerimeterSamples.remainingPairedCentered excision samples := by
    rw [PerimeterSamples.remaining_exterior_eq_corner_boundary excision samples faces neighbors]
    ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le (PerimeterSamples.remainingExterior excision
    samples)
    (PerimeterSamples.remainingCornerBoundary excision faces + PerimeterSamples.remainingBoundaryCentered excision
      samples neighbors)
    (contactAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le normNonnegative)
    (by
        rw [difference];
        exact GlobalContactRequest.remaining_accurate excision contacts positive contactLater samples)
  have lower := GlobalEnergyRequest.remaining_energy_lower excision request later readings observationFace faces samples
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := contactAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end GlobalEnergyRequest
end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ContactEnergy
