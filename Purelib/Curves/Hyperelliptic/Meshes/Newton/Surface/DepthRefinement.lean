module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Data.Vector

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests

public section

/-! Refine both observation sheets to a supplied later spatial depth while
retaining their error budgets and all earlier numerical requirements. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement

open Purelib.Data
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions
    observations grid}
  {coarse : (sheet : Fin 2) → Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains
    sheet}
  {fixed : (sheet : Fin 2) → Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {error : Purelib.Data.Rat.Fraction.Rational}

/-- Refine both retained observation sheets to a common later spatial depth.

The original error requests remain indexed by the same coarse meshes and preflights, and the new numerical stage also
retains every earlier requirement. -/
@[expose] def atDepth (request : NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error)
  (depth : Nat)
    (later : request.depth ≤ depth) : NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error
      := by
  let entries := DependentVector.ofFn fun sheet : Fin 2 =>
    SurfaceRequest.atDepth
      (request.entries.get sheet) depth ((request.depth_eq sheet).trans_le later)
  refine ⟨entries, depth, ?_, max request.index (entries.maximum fun _ entry => entry.index), ?_⟩
  · intro sheet
    dsimp only [entries]
    rw [DependentVector.ofFn_get]
    rfl
  · intro sheet
    exact (entries.get_le_maximum (fun _ entry => entry.index) sheet).trans (Nat.Order.le_max_right _ _)

/-- The refined synchronized request has exactly the supplied spatial depth. -/
theorem atDepth_depth (request : NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error)
  (depth : Nat)
    (later : request.depth ≤ depth) : (Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth request depth
      later).depth = depth := rfl

/-- The refined synchronized request retains or increases the original numerical stage. -/
theorem atDepth_index_ge (request : NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error)
  (depth : Nat)
    (later : request.depth ≤ depth) : request.index ≤
      (Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth request depth later).index :=
      Nat.Order.le_max_left _ _

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement
