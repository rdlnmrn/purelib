module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Common owner budgets below every retained parent request tolerance. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule

open Purelib.Data.Rat

open Purelib.Approximation
open Purelib.Curves
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

namespace CommonBasisPreparation.ParentRunSchedule

/-- Compute a common tolerance by taking the finite minimum of the supplied values and one. -/
@[expose] def commonTolerance : List Normalization.InverseRootPolynomial.Coordinate →
  Normalization.InverseRootPolynomial.Coordinate
  | [] => 1
  | value :: rest => min value
    (commonTolerance
    rest)

/-- The common tolerance is positive when every supplied tolerance is positive. -/
theorem commonTolerance_positive (values : List Normalization.InverseRootPolynomial.Coordinate)
    (positive : ∀ value ∈ values, 0 < value) : 0 <
      commonTolerance
      values := by
  induction values with
  | nil => exact (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1)
  | cons value rest ih =>
    exact Fraction.Order.Basic.lt_min (positive value List.mem_cons_self)
      (ih (fun next member => positive next (List.mem_cons_of_mem _ member)))

/-- The common tolerance is no greater than any member of its original tolerance list. -/
private theorem commonTolerance_le {values : List Normalization.InverseRootPolynomial.Coordinate} {value :
  Normalization.InverseRootPolynomial.Coordinate}
    (member : value ∈ values) :
      commonTolerance
      values ≤ value := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases Data.List.Membership.mem_cons.mp member with rfl | tail
    · exact Fraction.Order.Basic.min_le_left ..
    · exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _ (Fraction.Order.Basic.min_le_right ..) (ih tail)

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {capacity minimum : Nat} {requested :
    Normalization.InverseRootPolynomial.Coordinate}
  (schedule :
    ParentRunSchedule
    retained inputs outer capacity requested minimum)

/-- Certify that a stored tolerance list is exactly the list of retained parent-request tolerances. -/
@[expose] def ToleranceReadback (values : List Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  values = List.ofFn (fun position => (schedule.requests.get position).blocks.budget.tolerance)

/-- The owner request for one retained occurrence at the computed physical-piece tolerance. -/
@[expose] def PieceOwner (count : Nat) {target : Normalization.InverseRootPolynomial.Coordinate}
    (piece : Budget.RequestedLengthBudget.Requested count 1 target) :=
  OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    piece.budget.tolerance

/-- The owner request for one retained occurrence at the computed junction tolerance. -/
@[expose] def JunctionOwner {target : Normalization.InverseRootPolynomial.Coordinate} (junction :
  Budget.RequestedLengthBudget.Requested 1 1 target) :=
  OwnerRequest
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
    junction.budget.tolerance

set_option genInjectivity false in
/-- Both physical fragment kinds use one positive cap. Retain the owner requests
and parent preparations so numerical acquisition consumes their computed stages. -/
structure SharedOwners (count : Nat) (vertices : Fin capacity → Nat) where
  /-- The retained list of original parent-request tolerances. -/ tolerances : List
    Normalization.InverseRootPolynomial.Coordinate
  /-- The stored tolerances read back the exact dependent parent-request vector. -/ tolerances_eq :
    ToleranceReadback
    schedule tolerances
  /-- The common positive cap used by both physical fragment kinds. -/ target :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The target is exactly the finite minimum of the retained tolerances and one. -/ target_eq : target =
    commonTolerance
    tolerances
  /-- The common physical-fragment target is positive. -/ positive : 0 < target
  /-- The computed length budget for the requested number of physical pieces. -/ piece :
    Budget.RequestedLengthBudget.Requested count 1 target
  /-- The computed length budget for a single joining increment. -/ junction : Budget.RequestedLengthBudget.Requested 1
    1 target
  /-- The retained numerical owner request for the physical-piece budget. -/ pieceOwner :
    PieceOwner
    (outer := outer) count piece
  /-- The retained numerical owner request for the junction budget. -/ junctionOwner :
    JunctionOwner
    (outer := outer) junction
  /-- The prepared owner banks of the original parent requests and vertex counts. -/ parents : schedule.Owners vertices
  /-- The common stage paying both physical owner requests and all parent banks. -/ faceIndex : Nat
  /-- The face stage is exactly the maximum of the three retained stage requirements. -/ face_eq : faceIndex = max
    parents.faceIndex (max pieceOwner.index junctionOwner.index)

constructive_injectivity SharedOwners

/-- Compute the common tolerance and retain all physical-piece, junction and parent owner requests.

The common face stage is the maximum of these exact computed requests, so later acquisition uses their stored numerical
thresholds. -/
@[expose] def sharedOwners (count : Nat) (vertices : Fin capacity → Nat) :
  SharedOwners
  schedule count vertices := by
  let tolerances := List.ofFn (fun position => (schedule.requests.get position).blocks.budget.tolerance)
  have positive : 0 <
    commonTolerance
    tolerances := by
    apply
      commonTolerance_positive
    intro value member
    obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact (schedule.requests.get position).blocks.budget.tolerance_positive
  let target :=
    commonTolerance
    tolerances
  let piece := Budget.RequestedLengthBudget.requested count 1 target (by decide) positive
  let junction := Budget.RequestedLengthBudget.requested 1 1 target (by decide) positive
  let pieceOwner := OwnerRequest.build
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) _
    piece.budget.tolerance_positive
  let junctionOwner := OwnerRequest.build
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) _
    junction.budget.tolerance_positive
  let parents := schedule.prepareOwners vertices
  exact ⟨tolerances, rfl, target, rfl, positive, piece, junction, pieceOwner, junctionOwner,
    parents, max parents.faceIndex (max pieceOwner.index junctionOwner.index), rfl⟩

namespace SharedOwners
variable {schedule} {count : Nat} {vertices : Fin capacity → Nat}
  (owners :
    ParentRunSchedule.SharedOwners
    schedule count vertices)

/-- The shared target is no greater than each original parent-request tolerance. -/
theorem target_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    owners.target ≤ (schedule.requests.get position).blocks.budget.tolerance := by
  rw [owners.target_eq]
  apply
    commonTolerance_le
  rw [owners.tolerances_eq]
  exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩

/-- The physical-piece tolerance fits every original parent-request tolerance. -/
theorem piece_tolerance_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    owners.piece.budget.tolerance ≤ (schedule.requests.get position).blocks.budget.tolerance :=
  owners.piece.tolerance_le.trans (owners.target_le position)

/-- The junction tolerance fits every original parent-request tolerance. -/
theorem junction_tolerance_le (position : Fin
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
  outer).compared.entered.cache.parents.length) :
    owners.junction.budget.tolerance ≤ (schedule.requests.get position).blocks.budget.tolerance :=
  owners.junction.tolerance_le.trans (owners.target_le position)

/-- The retained parent-bank stage is bounded by the common face stage. -/
theorem parents_le : owners.parents.faceIndex ≤ owners.faceIndex :=
  (Data.Nat.Order.le_max_left ..).trans_eq owners.face_eq.symm

/-- The retained physical-piece owner stage is bounded by the common face stage. -/
theorem piece_le : owners.pieceOwner.index ≤ owners.faceIndex :=
  ((Data.Nat.Order.le_max_left ..).trans (Data.Nat.Order.le_max_right ..)).trans_eq owners.face_eq.symm

/-- The retained junction owner stage is bounded by the common face stage. -/
theorem junction_le : owners.junctionOwner.index ≤ owners.faceIndex :=
  ((Data.Nat.Order.le_max_right ..).trans (Data.Nat.Order.le_max_right ..)).trans_eq owners.face_eq.symm

/-- Each original parent face-query stage is bounded by the common face stage. -/
theorem query_le (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).compared.entered.cache.parents.length) :
    (schedule.requests.get position).blocks.queries.faceIndex ≤ owners.faceIndex :=
  (owners.parents.query_le position).trans owners.parents_le

end SharedOwners
end CommonBasisPreparation.ParentRunSchedule
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedOwnerSchedule
