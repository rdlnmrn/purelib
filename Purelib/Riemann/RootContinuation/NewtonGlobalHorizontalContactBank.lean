module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalCompleteContact
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalBoundaryRequest
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BoundaryPieces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Integration.Budget.Surface.Contact
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! All actual regular-face contacts on both sheets are cached under one
finite maximum. Non-neighbor entries retain a vacuous matching contract. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalHorizontalContactBank

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
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility (Compatible)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalCompleteContact
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

namespace SynchronizedSurfaceRequests.HorizontalContactBank

variable {depth : Nat}
  (requests : SynchronizedSurfaceRequests (fun sheet =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error)
  (compatible : Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible partitions)
  {vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  (mesh : LiftedMesh vertices edges grid.faces) (traces : PerimeterTraces requests)

/-- The first regular face matches the second across its top side.

Both boxes are read with the original retained face indices and bounds. -/
@[expose] def Matching (first last : Fin grid.faces.regulars.length) :=
  GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
    (grid.faces.regulars[last.val]'last.isLt).cell.box

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Prepared lifted horizontal contact between the retained face traces.

Keeps the source lift, its actual target sheet, the matching-side and partition-compatibility witnesses, allowance and
numerical floor. -/
@[expose] def Contact (first last : Fin grid.faces.regulars.length) (sheet : Fin 2)
    (matching : Matching (grid := grid) first last) (allowance : Fraction.Rational) (floor : Nat) :=
  Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalCompleteContact.Prepared requests (mesh.locateFace first
    sheet)
    ((traces.get sheet).get first)
    ((traces.get (Meshes.Newton.Surface.LiftedEntries.HorizontalContact.next (last := last) (mesh.locateFace first
      sheet)).sheet).get last)
    matching (compatible.horizontal first last matching) allowance floor

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Cached conditional horizontal contact and request index.

For a fixed face pair and source sheet, retains the prepared contact whenever the side relation holds and its exact
numerical index. -/
structure Entry (first last : Fin grid.faces.regulars.length) (sheet : Fin 2) (allowance : Fraction.Rational) (floor :
  Nat) where
  /-- Cached numerical index of the contact entry or complete bank. -/ index : Nat
  /-- Prepared contact available for every matching-side witness. -/ contact : (matching : Matching (grid := grid) first
    last) → Contact requests compatible mesh traces first last sheet matching allowance floor
  /-- The retained contact request has exactly the cached index. -/ index_eq : ∀ matching, (contact
    matching).request.index = index

constructive_injectivity Entry

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Decide and cache the horizontal contact for a face pair and sheet.

A matching top-to-bottom interface retains the actual prepared contact; a nonmatching pair stores index zero and
eliminates any matching witness. -/
@[expose] def Entry.build (first last : Fin grid.faces.regulars.length) (sheet : Fin 2)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    Entry requests compatible mesh traces first last sheet allowance floor := by
  letI : Decidable (Matching (grid := grid) first last) := by unfold Matching; infer_instance
  by_cases matching : Matching (grid := grid) first last
  · let prepared := Curves.Hyperelliptic.Meshes.Newton.Surface.HorizontalCompleteContact.Prepared.build requests
      (mesh.locateFace first sheet)
      ((traces.get sheet).get first)
      ((traces.get (Meshes.Newton.Surface.LiftedEntries.HorizontalContact.next (last := last) (mesh.locateFace first
        sheet)).sheet).get last)
      matching (compatible.horizontal first last matching) allowance positive floor
    exact ⟨prepared.request.index, fun _ => prepared, fun _ => rfl⟩
  · exact ⟨0, fun h => (matching h).elim, fun h => (matching h).elim⟩

open Purelib.Data in
open Purelib.Data.Rat in
/-- Dependent bank of horizontal contacts indexed by face pair and sheet.

Every entry retains the original surface requests, compatibility data, lifted mesh and perimeter traces. -/
@[expose] def Entries (allowance : Fraction.Rational) (floor : Nat) :=
  Vector.DependentVector (fun first : Fin grid.faces.regulars.length =>
    Vector.DependentVector (fun last : Fin grid.faces.regulars.length =>
      Vector.DependentVector (fun sheet : Fin 2 => Entry requests compatible mesh traces first last sheet allowance
        floor)))

variable {allowance : Data.Rat.Fraction.Rational} {floor : Nat}

/-- All cached contact indices lie below the supplied numerical index. -/
@[expose] def Entries.IndexBound (entries : Entries requests compatible mesh traces allowance floor) (index : Nat) :
  Prop :=
  ∀ first last sheet, (((entries.get first).get last).get sheet).index ≤ index

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Complete horizontal contact bank with a common index.

Retains every face-pair and sheet entry, with an index above the entries, surface request and requested floor. -/
structure Request (allowance : Fraction.Rational) (floor : Nat) where
  /-- Actual bank indexed by both regular faces and the source sheet. -/ entries : Entries requests compatible mesh
    traces allowance floor
  /-- Cached numerical index of the contact entry or complete bank. -/ index : Nat
  /-- Every cached contact index lies below the common index. -/ entries_le : Entries.IndexBound requests compatible
    mesh traces entries index
  /-- The original surface request precedes the common index. -/ surface_le : requests.index ≤ index
  /-- The common index respects the requested floor. -/ floor_le : floor ≤ index

constructive_injectivity Request

open Purelib.Data in
open Purelib.Data.Rat in
/-- Build the horizontal contact bank and its common numerical index.

Constructs every dependent face-pair/sheet entry and takes the maximum with the retained surface index and requested
floor. -/
@[expose] def Request.build (allowance : Fraction.Rational) (positive : 0 < allowance) (floor : Nat) :
    Request requests compatible mesh traces allowance floor := by
  let entries : Entries requests compatible mesh traces allowance floor := Vector.DependentVector.ofFn fun first =>
    Vector.DependentVector.ofFn fun last => Vector.DependentVector.ofFn fun sheet =>
      Entry.build requests compatible mesh traces first last sheet allowance positive floor
  let maximum := entries.maximum fun _ row => row.maximum fun _ sheets => sheets.maximum fun _ entry => entry.index
  refine ⟨entries, max (max requests.index floor) maximum, ?_,
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _), (Data.Nat.Order.le_max_right _ _).trans
      (Data.Nat.Order.le_max_left _ _)⟩
  intro first last sheet
  exact (((entries.get first).get last).get_le_maximum (fun _ entry => entry.index) sheet).trans
    (((entries.get first).get_le_maximum (fun _ sheets => sheets.maximum fun _ entry => entry.index) last).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ sheets => sheets.maximum fun _ entry => entry.index)
        first).trans
        (Data.Nat.Order.le_max_right _ _)))

end SynchronizedSurfaceRequests.HorizontalContactBank
end Purelib.Riemann.RootContinuation.NewtonGlobalHorizontalContactBank
