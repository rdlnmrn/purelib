module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DepthRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

public section

/-! Select one physical depth after both complete-surface requests. The
retained exterior basis schedules and refined observation requests then share
that depth and an explicit numerical threshold. -/
namespace Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule

open Purelib

open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (PhysicalBasisRequest PhysicalMeshRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
  (physicalMeshPieceCounts physicalMesh_pieceCount)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {gridTarget radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation gridTarget radius}
  {observations : ProtectedObservations original} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {wholeCoarse : (sheet : Fin 2) → Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains
    sheet}
  {wholeFixed : (sheet : Fin 2) → Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights
    domains sheet} {wholeTarget : Data.Rat.Fraction.Rational}
  {pieceCoarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {pieceFixed : (sheet : Fin 2) → Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet}
    {pieceTarget : Data.Rat.Fraction.Rational}

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain one physical depth and common numerical floor for whole and observation-piece surface requests.

The original exterior basis preparations determine a shared depth after both initial requests, and the refined requests
keep their original owners and index lower bounds. -/
structure PhysicalSurfaceSchedule (preparations :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains)
    (initialWhole : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest wholeCoarse wholeFixed
      wholeTarget)
    (initialPieces : SynchronizedSurfaceRequests pieceCoarse pieceFixed pieceTarget)
    (target : Rat.Fraction.Rational) (minimum floor : Nat) where
  /-- The retained exterior physical-basis request on the original domains. -/ basis :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest regular domains target minimum
    floor
  /-- The basis request retains exactly the supplied original preparations. -/ preparations_eq : basis.preparations =
    preparations
  /-- The retained physical-mesh request extending the original whole-surface request. -/ physical :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest basis initialWhole
  /-- The refined request on the original observation-piece meshes and preflights. -/ surface :
    SynchronizedSurfaceRequests pieceCoarse pieceFixed pieceTarget
  /-- Whole physical and observation-piece requests share exactly the same depth. -/ same_depth : physical.surface.depth
    = surface.depth
  /-- The refined piece index is no earlier than the original piece request. -/ initialPieces_le : initialPieces.index ≤
    surface.index
  /-- The common numerical floor for physical and piece requests. -/ index : Nat
  /-- The common index is exactly the maximum of the two retained indices. -/ index_eq : index = max physical.index
    surface.index
  /-- The physical request index is at most the common floor. -/ physical_le : physical.index ≤ index
  /-- The observation-piece request index is at most the common floor. -/ surface_le : surface.index ≤ index

constructive_injectivity PhysicalSurfaceSchedule

namespace PhysicalSurfaceSchedule

open Purelib.Curves in
open Purelib.Data in
/-- Synchronize actual physical and observation-piece requests after selecting the exterior basis budget.

The initial depth maximum supplies the basis floor, both original requests refine to the selected physical depth, and
their retained numerical indices determine the common threshold. -/
@[expose] def build (preparations : Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations
  regular domains)
    (initialWhole : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest wholeCoarse wholeFixed
      wholeTarget)
    (initialPieces : SynchronizedSurfaceRequests pieceCoarse pieceFixed pieceTarget)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (minimum floor : Nat) :
    PhysicalSurfaceSchedule preparations initialWhole initialPieces target minimum floor := by
  let lowerDepth := max initialWhole.depth initialPieces.depth
  let counts := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.physicalMeshPieceCounts preparations
    wholeCoarse
  let basis := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest.build preparations
    counts target positive minimum floor lowerDepth
  have lowerLe : lowerDepth ≤ basis.physicalDepth :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest.build_physicalFloor_le
      preparations counts target positive minimum floor lowerDepth
  have wholeLater := (Data.Nat.Order.le_max_left initialWhole.depth initialPieces.depth).trans lowerLe
  have piecesLater := (Data.Nat.Order.le_max_right initialWhole.depth initialPieces.depth).trans lowerLe
  let whole := initialWhole.atDepth basis.physicalDepth wholeLater
  let physical : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest basis initialWhole
    :=
    ⟨whole, rfl, (fun first second i =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.physicalMesh_pieceCount whole ((preparations.get
        first).occurrences[i.val]'i.isLt)).symm),
      initialWhole.atDepth_index_ge _ wholeLater, max basis.index whole.index, rfl,
      Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_right _ _⟩
  let surface := Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth
    initialPieces basis.physicalDepth piecesLater
  exact ⟨basis, rfl, physical, surface, rfl,
    Hyperelliptic.Meshes.Newton.Surface.DepthRefinement.atDepth_index_ge
      initialPieces _ piecesLater,
    max physical.index surface.index, rfl, Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_right _ _⟩

end PhysicalSurfaceSchedule
end Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
