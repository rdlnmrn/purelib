module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy

public section

/-! Both sheet occurrences use one spatial depth and one certified numerical
threshold. Refinement reuses the retained piece budgets and face preflights. -/
namespace Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfacePieceRequests
  SurfaceRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}

namespace SurfaceRequest

variable {sheet : Fin 2} {coarse : SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data in
/-- Refine an actual surface request to a supplied later spatial depth.

The retained piece budgets and face preflights are reused; a maximum of the original index and refined model indices
certifies the new numerical threshold. -/
@[expose] def atDepth (request : SurfaceRequest partitions coarse fixed error) (depth : Nat)
    (later : request.depth ≤ depth) : SurfaceRequest partitions coarse fixed error := by
  let entries : Vector.DependentVector (SurfacePieceRequests partitions coarse fixed request.perFace) :=
    Vector.DependentVector.ofFn fun position => Vector.DependentVector.ofFn fun piece =>
      ((request.entries.get position).get piece).refineDepth depth
        ((request.depth_eq position piece).le.trans later)
  let maximum := entries.maximum fun _ row => row.maximum fun _ entry => entry.modelRequest.index
  refine ⟨request.perFace, request.positive, request.paid, entries, depth, ?_,
    max request.index maximum, ?_⟩
  · intro position piece
    dsimp only [entries]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    rfl
  · intro position piece
    exact ((entries.get position).get_le_maximum (fun _ entry => entry.modelRequest.index) piece).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.modelRequest.index) position).trans
        (Nat.Order.le_max_right _ _))

/-- Spatial refinement uses exactly the supplied depth. -/
theorem atDepth_depth (request : SurfaceRequest partitions coarse fixed error) (depth : Nat)
    (later : request.depth ≤ depth) : (atDepth request depth later).depth = depth := rfl

/-- Spatial refinement preserves the original request's numerical index as a lower bound. -/
theorem atDepth_index_ge (request : SurfaceRequest partitions coarse fixed error) (depth : Nat)
    (later : request.depth ≤ depth) : request.index ≤ (atDepth request depth later).index := Nat.Order.le_max_left _ _

/-- Spatial refinement preserves the retained per-face allowance. -/
theorem atDepth_perFace (request : SurfaceRequest partitions coarse fixed error) (depth : Nat)
    (later : request.depth ≤ depth) : (atDepth request depth later).perFace = request.perFace := rfl

end SurfaceRequest

variable (coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet)
  (fixed : (sheet : Fin 2) → Preflights domains sheet) (error : Purelib.Data.Rat.Fraction.Rational)

open Purelib.Data in
/-- The two actual sheet-indexed surface requests on their original coarse meshes and preflights. -/
@[expose] def SheetSurfaceRequests :=
  Vector.DependentVector (fun sheet : Fin 2 => SurfaceRequest partitions (coarse sheet) (fixed sheet) error)

set_option genInjectivity false in
/-- Retain both sheet occurrences at one spatial depth and certified numerical threshold.

The dependent entry vector preserves each sheet's original piece owners and preflights, with exact common-depth and
index-bound certificates. -/
structure SynchronizedSurfaceRequests where
  /-- The actual retained request for each of the two original sheets. -/ entries : SheetSurfaceRequests coarse fixed
    error
  /-- The common spatial depth of both retained sheet requests. -/ depth : Nat
  /-- Each retained sheet request has exactly the common depth. -/ depth_eq : ∀ sheet, (entries.get sheet).depth = depth
  /-- The common certified numerical threshold. -/ index : Nat
  /-- Each retained sheet index is bounded by the common numerical threshold. -/ index_ge : ∀ sheet, (entries.get
    sheet).index ≤ index

constructive_injectivity SynchronizedSurfaceRequests

namespace SynchronizedSurfaceRequests

variable {coarse fixed error}

open Purelib.Riemann in
open Purelib.Data in
/-- Synchronize the two retained sheet requests at their maximum original depth.

Each actual request refines to that depth, and the maximum refined index certifies one common numerical threshold. -/
@[expose] def synchronize (initial : SheetSurfaceRequests coarse fixed error) : SynchronizedSurfaceRequests coarse fixed
  error := by
  let depth := initial.maximum fun _ request => request.depth
  let entries : SheetSurfaceRequests coarse fixed error := Vector.DependentVector.ofFn fun sheet =>
    Topology.NewtonSynchronizedSurfaceRequests.SurfaceRequest.atDepth (initial.get sheet) depth (initial.get_le_maximum
      (fun _ request => request.depth) sheet)
  refine ⟨entries, depth, ?_, entries.maximum (fun _ request => request.index),
    entries.get_le_maximum (fun _ request => request.index)⟩
  intro sheet
  dsimp only [entries]
  rw [Vector.DependentVector.ofFn_get]
  rfl

open Purelib.Data in
/-- Build and synchronize both original sheet requests for a positive error target. -/
@[expose] def build (coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet)
    (fixed : (sheet : Fin 2) → Preflights domains sheet) (error : Rat.Fraction.Rational) (positive : 0 < error) :
    SynchronizedSurfaceRequests coarse fixed error :=
  synchronize (Vector.DependentVector.ofFn fun sheet => SurfaceRequest.build partitions (coarse sheet) (fixed sheet)
    error positive)

open Purelib.Riemann in
open Purelib.Data in
/-- The synchronized threshold is no earlier than either original sheet request. -/
theorem synchronize_index_ge (initial : SheetSurfaceRequests coarse fixed error) (sheet : Fin 2) :
    (initial.get sheet).index ≤ (synchronize initial).index := by
  have retained := (synchronize initial).index_ge sheet
  dsimp only [synchronize] at retained
  rw [Vector.DependentVector.ofFn_get] at retained
  exact (Topology.NewtonSynchronizedSurfaceRequests.SurfaceRequest.atDepth_index_ge (initial.get sheet) _ _).trans
    retained

/-- Every actual piece mesh on either sheet has the same retained spatial depth. -/
theorem mesh_depth_eq (request : SynchronizedSurfaceRequests coarse fixed error)
    (firstSheet lastSheet : Fin 2) (first last : Fin grid.faces.regulars.length)
    (firstPiece : Fin (partitions.get first).cuts.boxes.length)
    (lastPiece : Fin (partitions.get last).cuts.boxes.length) :
    (((request.entries.get firstSheet).meshes.get first).entries.get firstPiece).depth =
      (((request.entries.get lastSheet).meshes.get last).entries.get lastPiece).depth :=
  ((request.entries.get firstSheet).mesh_depth first firstPiece).trans
    ((request.depth_eq firstSheet).trans ((request.depth_eq lastSheet).symm.trans
      ((request.entries.get lastSheet).mesh_depth last lastPiece).symm))

end SynchronizedSurfaceRequests
end Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
