module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedOwners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
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

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Synchronize the source and mesh requirements of the retained parent requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Data

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

section CommonBasisPreparation

open Purelib.Data.Rat.Fraction.Compatibility

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)

namespace ParentRunSchedule.CommonBasisPreparation

/-- The dependent vector of run requests for the original parents of one retained occurrence.

Each request uses that parent input, the shared physical capacity, the magnitude-based tolerance and the prescribed
minimum depth. -/
@[expose] def ParentRequests (capacity : Nat) (magnitude requested : Normalization.InverseRootPolynomial.Coordinate)
  (minimum : Nat) :=
  Data.Vector.DependentVector (fun position : Fin
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
        position).sources capacity
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
        prepared outer magnitude requested) minimum)

end ParentRunSchedule.CommonBasisPreparation

set_option genInjectivity false in
/-- Cache the source magnitude and each parent's actual request before selecting
shared stages. The mesh depth also pays the reference refinement requirement. -/
structure ParentRunSchedule (capacity : Nat) (requested : Normalization.InverseRootPolynomial.Coordinate) (minimum :
  Nat) where
  /-- The common source magnitude retained before acquiring the physical runs. -/ magnitude :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The retained magnitude is exactly the value computed from these original parent inputs. -/ magnitude_eq :
    magnitude =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs
  /-- The retained common source magnitude is nonnegative. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- The computed dependent run-request vector for the original occurrence parents. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule.CommonBasisPreparation.ParentRequests retained
    inputs outer capacity magnitude requested minimum
  /-- The common numerical stage paying the input index and all retained source requests. -/ sourceIndex : Nat
  /-- The source stage is the maximum of the input index and the retained request thresholds. -/ source_eq : sourceIndex
    = max index (requests.maximum (fun _ request => request.blocks.queries.sourceMinimum))
  /-- The common refinement depth paying the prescribed minimum and all original requests. -/ depth : Nat
  /-- The refinement depth is the maximum of the minimum and the retained request depths. -/ depth_eq : depth = max
    minimum (requests.maximum (fun _ request => request.refinement.depth))

constructive_injectivity ParentRunSchedule

namespace ParentRunSchedule
variable {retained inputs outer} {capacity minimum : Nat} {requested : Normalization.InverseRootPolynomial.Coordinate}

/-- Compute and retain the parent magnitude, dependent requests and their common numerical and refinement stages.

The source threshold and refinement depth are finite maxima of those exact requests; the expensive request data is
stored once. -/
@[expose] def build (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) (inputs : retained.Inputs index)
    (outer : Fin prepared.occurrences.length) (capacity : Nat)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) (minimum : Nat) :
    ParentRunSchedule
      retained inputs outer capacity requested minimum :=
  let magnitude :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs
  let requests :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule.CommonBasisPreparation.ParentRequests retained
    inputs outer capacity magnitude requested minimum :=
    Data.Vector.DependentVector.ofFn (fun position =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns.RunRequest.build _
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
        position).sources capacity _

        (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget_positive
        outer
        (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude_nonnegative
        retained inputs) positive) minimum)
  ⟨magnitude, rfl,
    SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude_nonnegative
    retained inputs, requests,
    max index (requests.maximum (fun _ request => request.blocks.queries.sourceMinimum)), rfl,
    max minimum (requests.maximum (fun _ request => request.refinement.depth)), rfl⟩

variable (schedule :
  ParentRunSchedule
  retained inputs outer capacity requested minimum)

/-- The original input stage is no later than the retained common source stage. -/
theorem index_le : index ≤ schedule.sourceIndex :=
  (Nat.Order.le_max_left ..).trans_eq schedule.source_eq.symm

/-- Each original parent request threshold is no later than the common source stage. -/
theorem source_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    (schedule.requests.get position).blocks.queries.sourceMinimum ≤ schedule.sourceIndex :=
  (schedule.requests.get_le_maximum (fun _ request => request.blocks.queries.sourceMinimum) position).trans
    ((Nat.Order.le_max_right ..).trans_eq schedule.source_eq.symm)

/-- The prescribed minimum refinement is bounded by the retained common depth. -/
theorem minimum_le : minimum ≤ schedule.depth :=
  (Nat.Order.le_max_left ..).trans_eq schedule.depth_eq.symm

/-- Each original parent request refinement is bounded by the retained common depth. -/
theorem refinement_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    (schedule.requests.get position).refinement.depth ≤ schedule.depth :=
  (schedule.requests.get_le_maximum (fun _ request => request.refinement.depth) position).trans
    ((Nat.Order.le_max_right ..).trans_eq schedule.depth_eq.symm)

/-- Any later physical dyadic depth meets every retained parent's width cap. -/
theorem width_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length)
    {physicalDepth : Nat} (later : schedule.depth ≤ physicalDepth) :
    (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^physicalDepth ≤ (schedule.requests.get
      position).refinement.width := open Purelib.Data.Rat in by
  let extra := physicalDepth - (schedule.requests.get position).refinement.depth
  have equal : physicalDepth = (schedule.requests.get position).refinement.depth + extra :=
    (Nat.Subtraction.add_sub_of_le ((schedule.refinement_le position).trans later)).symm
  rw [equal, pow_add]
  have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1 / 2)
    (by decide : (1 / 2 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1) extra
  rw [one_pow] at bounded
  exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)).trans_eq
    (mul_one _)).trans_eq (schedule.requests.get position).refinement.width_eq.symm

/-- The dependent family of prepared owner banks for the exact retained parent requests and physical vertex counts. -/
@[expose] def OwnerBanks (vertices : Fin capacity → Nat) :=
  Data.Vector.DependentVector (fun position => (schedule.requests.get position).blocks.OwnerPreparation vertices)

set_option genInjectivity false in
/-- Owner preparations are computed after the physical vertex counts are known.
The synchronized face index consumes the cached preparations directly. -/
structure Owners (vertices : Fin capacity → Nat) where
  /-- The prepared owner bank for each original parent request and its physical vertex count. -/ banks :
    schedule.OwnerBanks vertices
  /-- The common stage paying the retained source stage and all prepared owner stages. -/ faceIndex : Nat
  /-- The face stage is exactly the maximum of the retained source stage and owner stages. -/ face_eq : faceIndex =
    banks.maximum (fun _ owners => owners.faceIndex)

constructive_injectivity Owners

/-- Prepare the original parent owner banks once and retain their common face stage.

The vertex counts index those same banks, and their finite maximum determines the stage that pays every retained owner
request. -/
@[expose] def prepareOwners (vertices : Fin capacity → Nat) : schedule.Owners vertices :=
  let banks : schedule.OwnerBanks vertices := Data.Vector.DependentVector.ofFn
    (fun position => (schedule.requests.get position).blocks.prepareOwners vertices)
  ⟨banks, banks.maximum (fun _ owners => owners.faceIndex), rfl⟩

namespace Owners
variable {schedule} {vertices : Fin capacity → Nat} (owners : schedule.Owners vertices)

/-- Each prepared parent owner stage is bounded by the common face stage. -/
theorem face_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    (owners.banks.get position).faceIndex ≤ owners.faceIndex :=
  (owners.banks.get_le_maximum (fun _ bank => bank.faceIndex) position).trans_eq owners.face_eq.symm

/-- The retained common source stage is bounded by the common face stage. -/
theorem query_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    (schedule.requests.get position).blocks.queries.faceIndex ≤ owners.faceIndex :=
  (owners.banks.get position).query_le.trans (owners.face_le position)

/-- The query threshold of every prepared parent owner is bounded by the common face stage. -/
theorem owner_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length)
    (fragment : Fin capacity) :
    OwnerRequest.index
      ((owners.banks.get position).owners.get fragment) ≤ owners.faceIndex :=
  ((owners.banks.get position).owner_le fragment).trans (owners.face_le position)

end Owners
end ParentRunSchedule
end CommonBasisPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
