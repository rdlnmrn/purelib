module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalHorizontalContactBank
public import Purelib.Riemann.RootContinuation.NewtonGlobalVerticalContactBank
import Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContactEnergy
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! One executable global contact request pays every regular seam on both
sheets, retaining the same complete-surface traces and numerical owners. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest

open Purelib

open Purelib.Data.Rat

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
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (pairedCentered)
open Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContactEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (lifted_contact_paid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility (Compatible)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
open Purelib.Riemann.RootContinuation.NewtonGlobalHorizontalContactBank.SynchronizedSurfaceRequests
open Purelib.Riemann.RootContinuation.NewtonGlobalVerticalContactBank.SynchronizedSurfaceRequests
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : SurfacePartitions observations grid}
  {surfaceCuts : Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
    genus}

namespace SynchronizedSurfaceRequests

variable {depth : Nat}
  (requests : SynchronizedSurfaceRequests (fun sheet =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error)
  (compatible : Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions)
  {vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  (mesh : LiftedMesh vertices edges grid.faces) (traces : PerimeterTraces requests)

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Joint horizontal and vertical contact banks.

Retains both independently constructed banks for the original mesh and traces, with a common numerical index above each
bank. -/
structure GlobalContactRequest (allowance : Fraction.Rational) (floor : Nat) where
  /-- Actual retained horizontal contact bank. -/ horizontal : HorizontalContactBank.Request requests compatible mesh
    traces allowance floor
  /-- Actual retained vertical contact bank. -/ vertical : VerticalContactBank.Request requests compatible mesh traces
    allowance floor
  /-- Common numerical index for both orientations. -/ index : Nat
  /-- The horizontal bank index lies below the common index. -/ horizontal_le : horizontal.index ≤ index
  /-- The vertical bank index lies below the common index. -/ vertical_le : vertical.index ≤ index

constructive_injectivity GlobalContactRequest

namespace GlobalContactRequest

open Purelib.Data.Rat in
/-- Construct both contact banks and take their maximum index.

Uses the same positive allowance, original surface requests, compatible partitions, lifted mesh and stage floor in both
orientations. -/
@[expose] def build (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    GlobalContactRequest requests compatible mesh traces allowance floor :=
  let horizontal := HorizontalContactBank.Request.build requests compatible mesh traces allowance positive floor
  let vertical := VerticalContactBank.Request.build requests compatible mesh traces allowance positive floor
  ⟨horizontal, vertical, max horizontal.index vertical.index, Data.Nat.Order.le_max_left _ _,
    Data.Nat.Order.le_max_right _ _⟩

variable {requests compatible mesh traces} {allowance : Data.Rat.Fraction.Rational} {floor : Nat}

/-- The joint contact index respects the requested floor. -/
theorem floor_le (request : GlobalContactRequest requests compatible mesh traces allowance floor) : floor ≤
  request.index :=
  request.horizontal.floor_le.trans request.horizontal_le

/-- The joint contact index follows the original surface request. -/
theorem surface_le (request : GlobalContactRequest requests compatible mesh traces allowance floor) : requests.index ≤
  request.index :=
  request.horizontal.surface_le.trans request.horizontal_le

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
/-- The retained contact banks pay the global paired-centered error.

After the common index, retrieves each actual conditional contact and transports its cached index bound to the supplied
stage before combining both orientations. -/
theorem accurate (request : GlobalContactRequest requests compatible mesh traces allowance floor)
    (positive : 0 < allowance) (later : request.index ≤ stage)
    (samples : PerimeterSamples requests traces cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (pairedCentered samples) ≤
      (4 * (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
  apply lifted_contact_paid samples mesh positive
    (fun first last _ sheet => Meshes.Newton.Surface.LiftedEntries.HorizontalContact.next (last := last)
      (mesh.locateFace first sheet))
    (fun first last _ sheet => Meshes.Newton.Surface.LiftedEntries.VerticalContact.next (last := last) (mesh.locateFace
      first sheet))
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
end SynchronizedSurfaceRequests
end Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
