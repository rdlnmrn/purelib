module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

public section

/-! Build the shared whole-face and observation meshes for the ramified source comparison. -/
namespace Purelib.Riemann.Topology.NewtonOddSurfaceGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {gridTarget radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation gridTarget radius}
  (observations : ProtectedObservations original) (partitions : SurfacePartitions observations grid)
  {lifted : LiftedPuncturedGrid grid.punctured}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
  (domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Shared whole and piece geometry for odd surface comparisons.

Retains the canonical exterior basis preparations, shared cuts and sheet preflights, with whole-surface and partitioned
requests using the same raw-energy allowance. -/
structure OddSurfaceGeometry where
  /-- Actual exterior basis preparations for the retained regular region and domains. -/ preparations :
    Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains
  /-- The retained preparation bank equals its canonical construction. -/ preparations_eq : preparations =
    Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build regular domains
  /-- Shared exterior cuts for the original partitions and preparations. -/ shared : SharedExteriorCuts partitions
    preparations
  /-- Dependent bank of sheet preflight certificates. -/ fixed : Vector.DependentVector (fun sheet : Fin 2 =>
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet)
  /-- Whole two-sheet request using the shared source cuts and raw-energy allowance. -/ whole :
    Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
    (fun sheet => Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet 0)
    (fun sheet => fixed.get sheet) (NewtonRawEnergyBudget.rawEnergyAllowance observations)
  /-- Synchronized piece requests using the shared surface cuts and same allowance. -/ pieces :
    SynchronizedSurfaceRequests
    (fun sheet => Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet 0)
    (fun sheet => fixed.get sheet) (NewtonRawEnergyBudget.rawEnergyAllowance observations)

constructive_injectivity OddSurfaceGeometry

namespace OddSurfaceGeometry

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
/-- Construct shared odd surface geometry from its original owners.

Builds exterior preparations and common cuts once, then reuses the sheet preflight bank for both whole and piece
requests at the raw-energy target. -/
@[expose] def build : OddSurfaceGeometry observations partitions regular domains :=
  let preparations := Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build regular domains
  let shared := SharedExteriorCuts.build partitions preparations
    (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts.build domains)
      (Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts.build partitions domains)
  let fixed := Vector.DependentVector.ofFn (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.preflights domains)
  let whole := Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.build
    (fun sheet => Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet 0)
    (fun sheet => fixed.get sheet) (NewtonRawEnergyBudget.rawEnergyAllowance observations)
      (NewtonRawEnergyBudget.rawEnergyAllowance_positive observations)
  let pieces := SynchronizedSurfaceRequests.build
    (fun sheet => Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet 0)
    (fun sheet => fixed.get sheet) (NewtonRawEnergyBudget.rawEnergyAllowance observations)
      (NewtonRawEnergyBudget.rawEnergyAllowance_positive observations)
  ⟨preparations, rfl, shared, fixed, whole, pieces⟩

variable {observations partitions regular domains}
  (geometry : OddSurfaceGeometry observations partitions regular domains)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Read one retained exterior preparation as its canonical construction.

Uses the stored preparation-bank equality to recover the exact standard-differential preparation at the selected basis
index. -/
theorem preparation_readback (first : Fin genus) :
    geometry.preparations.get first =
      Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (standardDifferential first) := by
  rw [geometry.preparations_eq]
  exact Vector.DependentVector.ofFn_get _ _

end OddSurfaceGeometry
end Purelib.Riemann.Topology.NewtonOddSurfaceGeometry
