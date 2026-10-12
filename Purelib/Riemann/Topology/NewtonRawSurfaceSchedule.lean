module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
public import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts

public section

/-! Acquire one shared exterior/observation surface schedule from the retained
raw-energy grid, with the coefficient-independent allowance already paid. -/
namespace Purelib.Riemann.Topology.NewtonRawSurfaceSchedule

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights CommonCuts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest
  (energyAllowanceTarget energyAllowanceTarget_positive)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceEnergy.SynchronizedSurfaceRequests (GlobalEnergyRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule (PhysicalSurfaceSchedule)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {observations : ProtectedObservations original} {preparation : NewtonPreparation original} {radius :
    Data.Rat.Fraction.Rational}
  (gridData : RawEnergyGrid observations preparation radius)
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Sheet-indexed preflight bank on the retained raw grid domains. -/
@[expose] def SurfacePreflights := Vector.DependentVector (fun sheet : Fin 2 =>
  Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights gridData.domains sheet)

section
open Purelib.Curves.Hyperelliptic
/-- Initial whole-surface request using the shared source cuts.

Keeps the exact sheet preflight bank and raw-energy allowance at mesh depth zero. -/
@[expose] def InitialWhole {preparations : Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular
  gridData.domains}
    (shared : SharedExteriorCuts gridData.partitions preparations) (fixed : SurfacePreflights gridData) :=
  Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build gridData.domains shared.source.cuts sheet
      0)
    (fun sheet => fixed.get sheet) (rawEnergyAllowance observations)

/-- Initial synchronized piece request using the shared surface cuts.

Keeps the same original partitions, sheet preflights and raw-energy allowance at depth zero. -/
@[expose] def InitialPieces {preparations : Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular
  gridData.domains}
    (shared : SharedExteriorCuts gridData.partitions preparations) (fixed : SurfacePreflights gridData) :=
  SynchronizedSurfaceRequests
    (fun sheet => Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes gridData.partitions gridData.domains
      shared.surface sheet 0)
    (fun sheet => fixed.get sheet) (rawEnergyAllowance observations)

end

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Shared surface and energy requests for a raw-energy grid.

Retains canonical exterior preparations, shared cuts and preflights, actual whole and piece requests, their physical
schedule and global energy request with a common index. -/
structure SurfaceSchedule (minimum floor : Nat) where
  /-- Actual canonical exterior basis preparations. -/ preparations :
    Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular gridData.domains
  /-- The retained preparation bank equals its canonical construction. -/ preparations_eq : preparations =
    Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build regular gridData.domains
  /-- Shared source and surface cuts for the retained partitions and preparations. -/ shared : SharedExteriorCuts
    gridData.partitions preparations
  /-- Actual sheet preflight bank. -/ fixed : SurfacePreflights gridData
  /-- Whole-surface request over the retained shared source cuts. -/ whole : InitialWhole gridData regular shared fixed
  /-- Piece request over the retained shared surface cuts. -/ pieces : InitialPieces gridData regular shared fixed
  /-- Physical surface schedule keeping the actual whole and piece requests. -/ schedule : PhysicalSurfaceSchedule
    preparations whole pieces
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations))
      minimum floor
  /-- Global energy request with the original raw allowance for all three deductions. -/ energy : GlobalEnergyRequest
    schedule.surface (rawEnergyAllowance observations)
    (rawEnergyAllowance observations) (rawEnergyAllowance observations)
  /-- Common numerical index for physical and energy requests. -/ index : Nat
  /-- The common index equals the maximum of the two retained indices. -/ index_eq : index = max schedule.index
    energy.index
  /-- The physical schedule index lies below the common index. -/ schedule_le : schedule.index ≤ index
  /-- The global energy request index lies below the common index. -/ energy_le : energy.index ≤ index

constructive_injectivity SurfaceSchedule

namespace SurfaceSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Build the shared raw surface schedule and paid energy requests.

Constructs the common geometry once, reuses it for whole and piece requests, and retains their physical and energy
schedule indices under the exact maximum. -/
@[expose] def build (minimum floor : Nat) : SurfaceSchedule gridData regular minimum floor :=
  let preparations := Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build regular gridData.domains
  let shared := SharedExteriorCuts.build gridData.partitions preparations
    (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts.build gridData.domains)
      (Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts.build gridData.partitions gridData.domains)
  let fixed : SurfacePreflights gridData := Vector.DependentVector.ofFn
    (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.preflights gridData.domains)
  let whole := Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.build
    (fun sheet => Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build gridData.domains shared.source.cuts sheet
      0)
    (fun sheet => fixed.get sheet) (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations)
  let pieces := SynchronizedSurfaceRequests.build
    (fun sheet => Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes gridData.partitions gridData.domains
      shared.surface sheet 0)
    (fun sheet => fixed.get sheet) (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations)
  let schedule := PhysicalSurfaceSchedule.build preparations whole pieces
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations))
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive (rawEnergyAllowance_positive
      observations)) minimum floor
  let energy := GlobalEnergyRequest.build schedule.surface (rawEnergyAllowance observations)
    (rawEnergyAllowance observations) (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations)
    (rawEnergyAllowance_positive observations) (rawEnergyAllowance_positive observations)
  ⟨preparations, rfl, shared, fixed, whole, pieces, schedule, energy,
    max schedule.index energy.index, rfl, Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_right _ _⟩

end SurfaceSchedule
end Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
