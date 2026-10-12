module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

public section

/-! Both retained sheets share one paid request and the actual perimeter
samples. The remaining exterior keeps every boundary edge of the excision. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
open Purelib.Topology.BranchedCover.Double

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (SheetAssemblies SheetPerimeters
  SheetFaces PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (sideSum)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

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

namespace SynchronizedSurfaceRequests

namespace PerimeterSamples

variable {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error}
  {traces : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (samples : Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples requests traces
    cache coefficients)

/-- The signed sum of actual perimeter sides on every unexcised face, retaining both sheets. -/
@[expose] def remainingExterior : Gaussian := FiniteSum.Fin.sumFin fun position =>
  if ObservationLower.remainingFaceMask excision position then
    samples.sideSum .bottom position + samples.sideSum .right position -
      samples.sideSum .top position - samples.sideSum .left position else 0

/-- The sum of both retained sheet-face exteriors equals the actual signed perimeter-sample exterior on the unexcised
faces. -/
theorem remaining_exterior_readback {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache)
  (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters) :
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet : Fin 2 => if
      ObservationLower.remainingFaceMask excision position then ((faces.get sheet).get position).exterior else 0)) =
      remainingExterior
      excision samples := by
  have scalar (position : Fin grid.faces.regulars.length) (sheet : Fin 2) :
      ((faces.get sheet).get position).exterior =
        ((samples.get sheet).get position).bottom.originalArea + ((samples.get sheet).get position).right.originalArea -
          ((samples.get sheet).get position).top.originalArea - ((samples.get sheet).get position).left.originalArea :=
            by
    let reading := (samples.get sheet).get position
    let trace := (traces.get sheet).get position
    calc
      _ = trace.bottom.area (FacePerimeterTraces.ownerValues cache coefficients position) +
          trace.right.area (FacePerimeterTraces.ownerValues cache coefficients position) -
          trace.top.area (FacePerimeterTraces.ownerValues cache coefficients position) -
          trace.left.area (FacePerimeterTraces.ownerValues cache coefficients position) :=
        trace.exterior_eq ((faces.get sheet).get position)
      _ = _ := by
        rw [reading.bottom_area, reading.right_area, reading.top_area, reading.left_area,
          ← reading.bottom.decomposition, ← reading.right.decomposition,
          ← reading.top.decomposition, ← reading.left.decomposition]
  unfold
    remainingExterior
  apply FiniteSum.Fin.sumFin_congr
  intro position
  cases ObservationLower.remainingFaceMask excision position with
  | false =>
      change FiniteSum.Fin.sumFin (fun _ : Fin 2 => (0 : Data.Gaussian.Basic.Canonical)) = 0
      exact FiniteSum.Fin.sumFin_zero
  | true =>
      change FiniteSum.Fin.sumFin (fun sheet : Fin 2 => ((faces.get sheet).get position).exterior) = _
      rw [FiniteSum.Fin.sumFin_congr (scalar position)]
      simp only [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, PerimeterSamples.sideSum, if_pos (rfl : true =
        true), -eq_self, -iff_self]
      rfl

end PerimeterSamples

namespace GlobalEnergyRequest

variable {depth : Nat}
  {requests : Riemann.Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests (fun sheet =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error}
  {ownershipAllowance exteriorAllowance faceAllowance : Data.Rat.Fraction.Rational}

/-- At the paid common stage, the retained unexcised exterior carries both sheets' homogeneous energy lower bound after
the four recorded losses. -/
theorem remaining_energy_lower (excision : Excision.AllHoleExcision grid lifted) (request :
  SynchronizedSurfaceRequests.GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance)
    {stage : Nat} {cache : LocalMeshes.Numerics domains stage} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (later : request.index ≤ stage)
    (readings : Data.Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Attachment.Face)
    {assemblies : SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SynchronizedSurfaceRequests.SheetPerimeters requests assemblies} (faces :
      SynchronizedSurfaceRequests.SheetFaces requests perimeters)
    {traces : SynchronizedSurfaceRequests.PerimeterTraces requests} (samples :
      SynchronizedSurfaceRequests.PerimeterSamples requests traces cache coefficients)
    :
    2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) *
      PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        (PerimeterSamples.remainingExterior
        excision samples).im / 4 := by
  have lower (sheet : Fin 2) := DefectRequest.remaining_energy_lower excision
    (request.entries.get sheet).ownership (request.entries.get sheet).exterior (request.entries.get sheet).faces
    (request.entries.get sheet).ownership_positive (request.entries.get sheet).exterior_positive
    (request.entries.get sheet).face_positive ((request.index_ge sheet).trans later)
    (readings.get sheet) observationFace (faces.get sheet)
  have total :
    PerimeterSamples.remainingExterior
    excision samples =
      FaceAssemblies.remainingExterior excision (faces.get 0) + FaceAssemblies.remainingExterior excision (faces.get 1)
        := by
    rw [←
      PerimeterSamples.remaining_exterior_readback
      excision samples faces, FiniteSum.Fin.sumFin_swap, Algebra.FiniteSum.Gaussian.sumFin_two_gaussian]
    rfl
  rw [total, Data.Gaussian.Basic.add_im]
  have bound := Fraction.Order.Arithmetic.add_le_add_direct (lower 0) (lower 1)
  apply (le_of_eq (by ring1)).trans (bound.trans_eq ?_)
  simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
  ring1

end GlobalEnergyRequest
end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.SurfaceEnergy
