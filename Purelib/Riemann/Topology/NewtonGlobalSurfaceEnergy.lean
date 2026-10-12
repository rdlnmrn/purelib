module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The independently positive observation energy reaches the exact global
paired-plus-physical boundary after paying all internal face defects on both
sheets at a common numerical stage. -/
namespace Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ExteriorRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (DefectRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (SheetAssemblies SheetPerimeters
  SheetFaces PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_swap sumFin_succ)

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
  {depth : Nat} {sheet : Fin 2} {fixed : Preflights domains sheet} {error : Rational}
  {ownershipAllowance exteriorAllowance faceAllowance : Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Three paid comparison requests over one surface energy request.

Retains positive ownership, exterior and face allowances, with the exterior request following ownership and the defect
request retaining that exterior owner. -/
structure PaidFaceRequest (energy : SurfaceRequest partitions (Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes
  partitions domains surfaceCuts sheet depth) fixed error)
    (ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational) where
  /-- Strict positivity of the ownership allowance. -/ ownership_positive : 0 < ownershipAllowance
  /-- Strict positivity of the exterior allowance. -/ exterior_positive : 0 < exteriorAllowance
  /-- Strict positivity of the face allowance. -/ face_positive : 0 < faceAllowance
  /-- Ownership comparison for the exact retained energy request. -/ ownership :
    Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest energy
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus ownershipAllowance)
  /-- Exterior comparison following the retained ownership index. -/ exterior :
    Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest energy
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus exteriorAllowance) ownership.index
  /-- Face defect comparison retaining that exterior request. -/ faces :
    Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest exterior
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus faceAllowance)

constructive_injectivity PaidFaceRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct the three paid requests from positive allowances.

Builds ownership first, uses its index as the exterior floor, then retains that exterior request in the face defect
request. -/
@[expose] def PaidFaceRequest.build (energy : SurfaceRequest partitions
  (Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet depth) fixed error)
    (ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational)
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance) (facePositive : 0 <
      faceAllowance) :
    PaidFaceRequest energy ownershipAllowance exteriorAllowance faceAllowance :=
  let ownership := Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest.build energy _
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive ownershipPositive)
  let exterior := Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.forEnergyAllowance energy exteriorAllowance
    exteriorPositive ownership.index
  ⟨ownershipPositive, exteriorPositive, facePositive, ownership, exterior,
    Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.forEnergyAllowance exterior faceAllowance facePositive⟩

namespace SynchronizedSurfaceRequests

variable {fixedSheets : (sheet : Fin 2) → Preflights domains sheet}
  (requests : SynchronizedSurfaceRequests (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixedSheets error)

open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Paired-sheet energy requests with a common numerical index.

Keeps each sheet-specific paid request and a common index after both the surface request and all retained face requests.
-/
structure GlobalEnergyRequest (ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational) where
  /-- Sheet-indexed bank of paid face requests. -/ entries : Vector.DependentVector (fun sheet : Fin 2 =>
    PaidFaceRequest (requests.entries.get sheet) ownershipAllowance exteriorAllowance faceAllowance)
  /-- Common numerical index for the surface and both face requests. -/ index : Nat
  /-- The retained surface request index lies below the common index. -/ surface_le : requests.index ≤ index
  /-- Each retained face request index lies below the common index. -/ index_ge : ∀ sheet, (entries.get
    sheet).faces.index ≤ index

constructive_injectivity GlobalEnergyRequest

namespace GlobalEnergyRequest

variable {requests}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Construct the paired-sheet energy request and its common index.

Builds the dependent bank of paid requests and takes the maximum of the surface index and all face-request indices. -/
@[expose] def build (requests : SynchronizedSurfaceRequests (fun sheet =>
  Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet depth) fixedSheets error)
    (ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational)
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance) (facePositive : 0 <
      faceAllowance) :
    GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance := by
  let entries := Vector.DependentVector.ofFn fun sheet : Fin 2 => PaidFaceRequest.build (requests.entries.get sheet)
    ownershipAllowance exteriorAllowance faceAllowance ownershipPositive exteriorPositive facePositive
  let maximum := entries.maximum fun _ request => request.faces.index
  exact ⟨entries, max requests.index maximum, Nat.Order.le_max_left _ _, fun sheet =>
    (entries.get_le_maximum (fun _ request => request.faces.index) sheet).trans (Nat.Order.le_max_right _ _)⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- A Gaussian sum over two indices is the sum of its two entries. -/
private theorem sum_two (values : Fin 2 → Basic.Canonical) : FiniteSum.Fin.sumFin values = values 0 + values 1 := by
  rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change values 0 + (values 1 + 0) = _
  rw [add_zero]

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- Lower-bound the global paired and physical boundary energy.

Combines the two sheet coercivity estimates, retaining separate ownership, exterior and face deductions and the exact
exterior readback through the neighbor bank. -/
theorem energy_lower (request : GlobalEnergyRequest requests ownershipAllowance exteriorAllowance faceAllowance)
    {stage : Nat} {cache : Numerics domains stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (later : request.index ≤ stage)
    (readings : Vector.DependentVector (fun sheet : Fin 2 => (requests.entries.get sheet).Readings cache))
    (observationFace : Topology.BranchedCover.Double.Attachment.Face)
    {assemblies : SheetAssemblies requests (cache := cache) (coefficients := coefficients)}
    {perimeters : SheetPerimeters requests assemblies} (faces : SheetFaces requests perimeters)
    {traces : PerimeterTraces requests} (samples : PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    2 * (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance -
      exteriorAllowance - faceAllowance) *
      coefficientNormSq coefficients ≤ (samples.paired + samples.physical neighbors).im / 4 := by
  have lower (sheet : Fin 2) := Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.energy_lower
    (request.entries.get sheet).ownership (request.entries.get sheet).exterior (request.entries.get sheet).faces
    (request.entries.get sheet).ownership_positive (request.entries.get sheet).exterior_positive
    (request.entries.get sheet).face_positive ((request.index_ge sheet).trans later)
    (readings.get sheet) observationFace (faces.get sheet)
  have total : samples.exterior = (faces.get 0).exterior + (faces.get 1).exterior := by
    rw [← samples.exterior_readback faces, FiniteSum.Fin.sumFin_swap, sum_two]
    rfl
  rw [← samples.exterior_eq_paired_add_physical neighbors, total, Basic.add_im]
  have bound := Fraction.Order.Arithmetic.add_le_add_direct (lower 0) (lower 1)
  apply (le_of_eq (by ring1)).trans (bound.trans_eq ?_)
  simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]
  ring1

end GlobalEnergyRequest
end SynchronizedSurfaceRequests
end Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
