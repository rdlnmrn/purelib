module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Select one face stage for the actual shared piece, junction and parent owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization

open Purelib.Data.Rat

open Purelib.Curves
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

namespace CommonBasisPreparation

open Purelib.Data.Rat.Fraction.Compatibility

namespace ParentRunSchedules
variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {capacities : Fin prepared.occurrences.length → Nat} {requested : Normalization.InverseRootPolynomial.Coordinate}
    {minimum : Nat}
  (schedules :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained inputs capacities requested minimum)

/-- The dependent vector of prepared parent owner banks at the original occurrence capacities and vertex counts. -/
@[expose] def ParentOwners (vertices : (outer : Fin prepared.occurrences.length) → Fin (capacities outer) → Nat) :=
  Data.Vector.DependentVector (fun outer => (schedules.get outer).Owners (vertices outer))

/-- The dependent vector of shared physical-piece, junction and parent owner requests for the original schedules. -/
@[expose] def SharedOwnerBanks (counts : Fin prepared.occurrences.length → Nat)
    (vertices : (outer : Fin prepared.occurrences.length) → Fin (capacities outer) → Nat) :=
  Data.Vector.DependentVector (fun outer =>
    SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.SharedOwners
    (schedules.get outer) (counts outer) (vertices outer))

/-- Compute each occurrence shared-owner bank using its original request schedule and physical vertex counts. -/
@[expose] def prepareSharedOwners (counts : Fin prepared.occurrences.length → Nat)
    (vertices : (outer : Fin prepared.occurrences.length) → Fin (capacities outer) → Nat) :

      SharedOwnerBanks
      schedules counts vertices :=
  Data.Vector.DependentVector.ofFn (fun outer =>
    SharedOwnerSchedule.CommonBasisPreparation.ParentRunSchedule.sharedOwners
    (schedules.get outer) (counts outer) (vertices outer))

variable {schedules} {counts : Fin prepared.occurrences.length → Nat}
  {vertices : (outer : Fin prepared.occurrences.length) → Fin (capacities outer) → Nat}
  (owners :
    SharedOwnerBanks
    schedules counts vertices)

/-- Certify that the retained parent bank at each occurrence is exactly the one stored in its shared-owner bank. -/
@[expose] def ParentReadback (parents :
  ParentOwners
  schedules vertices) : Prop :=
  ∀ outer, parents.get outer = (owners.get outer).parents

set_option genInjectivity false in
/-- Include the surface's existing stage and every owner stage in one finite
maximum. The parent preparations are cached from these very shared owners. -/
structure FaceStage (floor : Nat) where
  /-- The cached dependent vector of parent owner banks taken from the shared-owner banks. -/ parents :
    ParentOwners
    schedules vertices
  /-- Each cached parent bank is exactly the original corresponding shared-owner parent bank. -/ parents_eq :
    ParentReadback
    owners parents
  /-- The common numerical stage paying the surface floor and every retained owner bank. -/ stage : Nat
  /-- The stage is exactly the maximum of the supplied floor and shared-owner thresholds. -/ stage_eq : stage = max
    floor (owners.maximum (fun _ owner => owner.faceIndex))

constructive_injectivity FaceStage

namespace FaceStage

/-- Cache the original parent owner banks and compute the common numerical face stage.

The parent readback records exact ownership, and the finite maximum pays the supplied surface floor and every
shared-owner threshold. -/
@[expose] def build (floor : Nat) :
  ParentRunSchedules.FaceStage
  owners floor :=
  let parents :
    ParentOwners
    schedules vertices := Data.Vector.DependentVector.ofFn (fun outer => (owners.get outer).parents)
  ⟨parents, fun outer => Data.Vector.DependentVector.ofFn_get _ outer,
    max floor (owners.maximum (fun _ owner => owner.faceIndex)), rfl⟩

variable {owners} {floor : Nat} (selected :
  ParentRunSchedules.FaceStage
  owners floor)

/-- The supplied numerical floor is bounded by the selected face stage. -/
theorem floor_le : floor ≤ selected.stage :=
  (Data.Nat.Order.le_max_left ..).trans_eq selected.stage_eq.symm

/-- Every retained shared-owner threshold is bounded by the selected face stage. -/
theorem owner_le (outer : Fin prepared.occurrences.length) : (owners.get outer).faceIndex ≤ selected.stage :=
  (owners.get_le_maximum (fun _ owner => owner.faceIndex) outer).trans
    ((Data.Nat.Order.le_max_right ..).trans_eq selected.stage_eq.symm)

/-- Every cached parent-bank threshold is bounded by the selected face stage. -/
theorem parents_le (outer : Fin prepared.occurrences.length) : (selected.parents.get outer).faceIndex ≤ selected.stage
  :=
  (congrArg
    ParentRunSchedule.Owners.faceIndex
    (selected.parents_eq outer)).trans_le
    ((owners.get outer).parents_le.trans (selected.owner_le outer))

/-- Every retained physical-piece owner threshold is bounded by the selected face stage. -/
theorem piece_le (outer : Fin prepared.occurrences.length) : (owners.get outer).pieceOwner.index ≤ selected.stage :=
  (owners.get outer).piece_le.trans (selected.owner_le outer)

/-- Every retained junction owner threshold is bounded by the selected face stage. -/
theorem junction_le (outer : Fin prepared.occurrences.length) : (owners.get outer).junctionOwner.index ≤ selected.stage
  :=
  (owners.get outer).junction_le.trans (selected.owner_le outer)

end FaceStage

/-- The exact tolerance used to build the physical bank is paid at every parent. -/
theorem shared_tolerance_le (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    max (owners.get outer).piece.budget.tolerance (owners.get outer).junction.budget.tolerance ≤
      ((schedules.get outer).requests.get position).blocks.budget.tolerance :=
  Fraction.Order.Basic.max_le ((owners.get outer).piece_tolerance_le position) ((owners.get outer).junction_tolerance_le
    position)

end ParentRunSchedules
end CommonBasisPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunFaceSynchronization
