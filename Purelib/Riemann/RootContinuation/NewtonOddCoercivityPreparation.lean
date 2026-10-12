module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SpatialAcquisition
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SynchronizedSourceInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.NewtonOddSurfaceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SurfaceAcquisition
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Compute the ramified coercivity schedule from the retained source and physical meshes. -/
namespace Purelib.Riemann.RootContinuation.NewtonOddCoercivityPreparation

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology.NewtonOddSurfaceGeometry (OddSurfaceGeometry)
open Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation (OddSourcePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns
  (capacities)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns
  (pieceCounts)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
  (SourceSurfaceAcquisition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility (Compatible)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis (CoercivitySchedule)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {gridTarget radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation gridTarget radius}
  (observations : ProtectedObservations original) (partitions : SurfacePartitions observations grid)
  {lifted : LiftedPuncturedGrid grid.punctured}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
  (domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars)

variable (geometry : OddSurfaceGeometry observations partitions regular domains) (first : Fin genus) (floor : Nat)

namespace OddSourcePreparation
variable {observations partitions regular domains geometry first floor}
  (source : OddSourcePreparation observations partitions regular domains geometry first floor)

open Purelib.Curves.Hyperelliptic
/-- Retained piece count for an exterior occurrence and capacity index.

Reads the original shared-source refinement's piece count; the capacity position does not change that occurrence's owner
length. -/
@[expose] def ownerLengths (outer : Fin source.component.prepared.occurrences.length)
    (_position : Fin (Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.capacities
      (geometry.shared.source.select first) source.acquired.geometry.spatial.refined outer)) : Nat :=
  Meshes.PuncturedGrid.Exterior.Basis.RequestedPhysicalComponent.RequestedSurfaceRuns.pieceCounts
    (geometry.shared.source.select first) source.acquired.geometry.spatial.refined outer

/-- Build the odd source's retained coercivity schedule.

Under origin order one, reuses the source acquisition, exact owner lengths, original excision and compatible partitions
at the raw-energy allowance and requested face floor. -/
@[expose] def coercivity (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (compatible : Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions) (faceFloor : Nat)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule geometry.shared source.acquired
      (ownerLengths source) floor faceFloor
      excision compatible (rawEnergyAllowance observations) :=
  Curves.Hyperelliptic.Meshes.Newton.Basis.CoercivitySchedule.build geometry.shared
    source.acquired (ownerLengths source) floor faceFloor
    excision compatible (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations) branch

end OddSourcePreparation
end Purelib.Riemann.RootContinuation.NewtonOddCoercivityPreparation
