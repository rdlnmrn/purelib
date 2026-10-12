module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment
import Purelib.Tactic.Ring

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ContactEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
public import Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.TriangleEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnEnergyRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback.SynchronizedSurfaceRequests

public section

/-! The independent observation lower bound reaches the actual sewn Newton
complement, paying a homogeneous sewing allowance and retaining its boundary. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SewnEnergy

open Purelib.Curves
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
    {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage} {coefficients
    : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {depth : Nat}
  {requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests (fun sheet =>
    Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet depth)
    fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance contactAllowance sewingAllowance : Fraction.Rational}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation lifted.cutPolygon domains} {floor
    contactFloor : Nat}
  {compatible : Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions}

/-- The independent observation lower bound holds for the actual sewn Newton complement after paying contacts and
sewing.

The original selected triangle mask, cached coefficient readings and retained complement boundary are shared throughout
the comparison. -/
theorem remaining_sewn_energy_lower (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid
  lifted)
    (request : Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest requests
      ownershipAllowance exteriorAllowance faceAllowance)
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request prepared
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus sewingAllowance)
      floor)
    (surfaceLater : request.index ≤ stage) (sewingLater : sewing.index ≤ stage)
    (surfaceReadings : Data.Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Topology.BranchedCover.Double.Attachment.Face)
    {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
      cache) (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    {traces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests} (samples :
      Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces cache
      coefficients)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank grid.faces) (contactPositive : 0 <
      contactAllowance)
    (contacts : RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests.GlobalContactRequest requests
      compatible lifted.mesh traces contactAllowance contactFloor)
    (contactLater : contacts.index ≤ stage)
    (readings :
      PerimeterSamples.EnergyTriangleReadings
      cache lifted.mesh)
    (surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces lifted.cutPolygon.patch (fun basis =>
      (readings.get basis).values))
    (pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces)
    (selected : Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
        source))))
    (sewingPositive : 0 < sewingAllowance) :
    (2 * (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) -
      contactAllowance - sewingAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        (selected.energy coefficients +
          CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
          excision samples neighbors).im / 4 := open Purelib.Algebra in open Purelib.Data in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have close := Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnEnergyRequest.EnergyPreparation.Request.selected_accurate
    sewing sewingLater readings selected coefficients
  have close' : Gaussian.Norm.Basic.normSq (selected.energy coefficients -
    TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
    excision readings coefficients) ≤
      (genus : Fraction.Rational)^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus sewingAllowance :=
        by
    convert close using 1
    · apply congrArg (fun value => Gaussian.Norm.Basic.normSq (selected.energy coefficients - value))
      unfold
        TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
      apply FiniteSum.Fin.sumFin_congr
      intro source
      split <;> rfl
    · have coefficientIdentity :
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients =
            FiniteSum.Fin.sumFin
              (fun basis : Fin genus => Gaussian.Norm.Basic.normSq (coefficients basis)) := by
            unfold Readings.PreparedObservationCoercivity.coefficientNormSq
            exact FiniteSum.Fin.sumFin_congr
              (fun row => (Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row)).symm)
      rw [coefficientIdentity]
  have squared : Gaussian.Norm.Basic.normSq (selected.energy coefficients -
    TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
    excision readings coefficients) ≤
      (4 * (sewingAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    apply close'.trans
    calc
      _ = ((genus : Fraction.Rational)^2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus sewingAllowance) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 := by ring0
      _ ≤ (4 * sewingAllowance)^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid sewingPositive)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring0
  have difference :
    (TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
    excision readings coefficients +
    CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
    excision samples neighbors) -
      (selected.energy coefficients +
        CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
        excision samples neighbors) =
      -(selected.energy coefficients -
        TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
        excision readings coefficients) := by
    ring0
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le

      (TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remainingTriangleEnergy
      excision readings coefficients +
      CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors)
    (selected.energy coefficients +
      CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingBoundaryCentered
      excision samples neighbors)
    (sewingAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct sewingPositive.le normNonnegative)
    (by rw [difference, Gaussian.Norm.Basic.normSq_neg]; exact squared)
  have lower :=
    ContactEnergy.SynchronizedSurfaceRequests.GlobalEnergyRequest.remaining_energy_lower_after_contacts
    excision request surfaceLater
    surfaceReadings observationFace faces samples neighbors contactPositive contacts contactLater
  rw
    [TriangleEnergy.SynchronizedSurfaceRequests.PerimeterSamples.remaining_cornerBoundary_triangles
    excision readings faces] at lower
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := sewingAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans
      comparison
  exact (le_of_eq (by ring0)).trans paid

end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SewnEnergy
