module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
public import Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Transfer the independent surface lower bound to the actual sewn energy
boundary, paying one coefficient-independent sewing allowance. -/
namespace Purelib.Riemann.Topology.NewtonGlobalSewnEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples
  SheetAssemblies SheetPerimeters SheetFaces)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests (GlobalContactRequest)
open Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (EnergyTriangleReadings triangleEnergy shared_triangle_energy_lower)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (physicalCentered)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility (Compatible)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_paid)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs energyBoundary)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest (EnergyPreparation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_right_direct)

variable {depth : Nat}
  {requests : SynchronizedSurfaceRequests (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance contactAllowance sewingAllowance :
    Rational}
  {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : LiftedMesh vertices edges grid.faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {polygon :
    SinglePolygon forest}
  {prepared : EnergyPreparation polygon domains}
    {floor contactFloor : Nat}
  {compatible : Compatible partitions}

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Topology in
open Purelib.Topology.Surface in
/-- Retain a global energy lower bound after contact and sewing payments.

Compares the actual shared triangle readings with their sewn energy surfaces, subtracts the separate positive contact
and sewing allowances, and preserves the physical centered boundary contribution. -/
theorem sewn_energy_lower
    (request : GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance)
    (sewing : Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request prepared
      (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus sewingAllowance) floor)
    (surfaceLater : request.index ≤ stage) (sewingLater : sewing.index ≤ stage)
    (surfaceReadings : Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Topology.BranchedCover.Double.Attachment.Face)
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    {traces : PerimeterTraces requests} (samples : PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (contactPositive : 0 < contactAllowance)
    (contacts : GlobalContactRequest requests compatible mesh traces contactAllowance contactFloor)
    (contactLater : contacts.index ≤ stage)
    (readings : EnergyTriangleReadings cache mesh)
    (surfaces : Sewing.SewnEnergyCombination.EnergySurfaces polygon.patch (fun basis => (readings.get basis).values))
    (pairs : Sewing.SewnEnergyCombination.EnergyPairs surfaces) (sewingPositive : 0 < sewingAllowance) :
    (2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) -
      contactAllowance - sewingAllowance) * coefficientNormSq coefficients ≤
        (Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + physicalCentered samples neighbors).im / 4
          := by
  have normNonnegative : 0 ≤ coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have close := sewing.accurate sewingLater readings surfaces pairs coefficients
  have same := FiniteSum.Fin.sumFin_congr (fun triangle => show
      Sewing.SewnEnergyCombination.localEnergy
        (fun basis => (readings.get basis).values) coefficients triangle =
        triangleEnergy readings coefficients triangle by rfl)
  rw [same] at close
  have close' : Data.Gaussian.Norm.Basic.normSq (Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients -
    FiniteSum.Fin.sumFin (triangleEnergy readings coefficients)) ≤
      (genus : Fraction.Rational)^2 * coefficientNormSq coefficients^2 *
        Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus sewingAllowance := by
    convert close using 1
    have coefficientIdentity : coefficientNormSq coefficients =
        FiniteSum.Fin.sumFin
          (fun basis : Fin genus => Data.Gaussian.Norm.Basic.normSq (coefficients basis)) := by
      unfold coefficientNormSq
      exact FiniteSum.Fin.sumFin_congr
        (fun basis => (Norm.Basic.normSq_eq_canonical (coefficients basis)).symm)
    rw [coefficientIdentity]
  have squared : Data.Gaussian.Norm.Basic.normSq (Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients -
    FiniteSum.Fin.sumFin (triangleEnergy readings coefficients)) ≤
      (4 * (sewingAllowance * coefficientNormSq coefficients))^2 := by
    apply close'.trans
    calc
      _ = ((genus : Fraction.Rational)^2 * Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget
        genus sewingAllowance) * coefficientNormSq coefficients^2 := by
        ring1
      _ ≤ (4 * sewingAllowance)^2 * coefficientNormSq coefficients^2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid sewingPositive)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have difference : (FiniteSum.Fin.sumFin (triangleEnergy readings coefficients) + physicalCentered samples neighbors) -
      (Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + physicalCentered samples neighbors) =
      -(Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients - FiniteSum.Fin.sumFin (triangleEnergy
        readings coefficients)) := by ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (FiniteSum.Fin.sumFin (triangleEnergy readings coefficients) + physicalCentered samples neighbors)
    (Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + physicalCentered samples neighbors)
    (sewingAllowance * coefficientNormSq coefficients) (Fraction.Order.Arithmetic.mul_nonneg_direct sewingPositive.le
      normNonnegative)
    (by rw [difference, Norm.Basic.normSq_neg]; exact squared)
  have lower := shared_triangle_energy_lower request surfaceLater surfaceReadings observationFace faces samples
    neighbors contactPositive (contacts.accurate contactPositive contactLater samples) readings
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := sewingAllowance * coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end SynchronizedSurfaceRequests
end Purelib.Riemann.Topology.NewtonGlobalSewnEnergy
