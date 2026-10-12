module
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseChains
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves

open Purelib

open Purelib.Riemann

public section

/-! Derive reversed side chains from retained local joins and descending order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates

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

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

variable {count : Nat}
  (pieces : Fin (count + 1) → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment
    retained inputs outer data coefficients)
  (junctions : Fin count → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained
    inputs outer data coefficients)

/-- The alternating side word begins with its first physical piece, followed by its retained tail. -/
private theorem indexedSideFragments_cons :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces junctions = pieces
      0 :: (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces
      junctions).tail := by
  cases count <;> rfl

/-- Local reverse joins connect the first physical piece through the complete alternating side tail to parameter zero.
-/
private theorem side_reverse_after
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).ReverseJoined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).ReverseJoined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 0) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseAfter (pieces 0)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces junctions).tail
      := by
  induction count with
  | zero => exact finish
  | succ count ih =>
    refine ⟨pieceJoin 0, ?_⟩
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates.indexedSideFragments_cons]
    exact ⟨nextJoin 0, ih (fun position => pieces position.succ) (fun position => junctions position.succ)
        (fun position => pieceJoin position.succ) (fun position => nextJoin position.succ) finish⟩

/-- Local piece/junction handoffs supply the complete word certificate. -/
theorem indexedSideFragments_reverse_word
    (start : (pieces 0).firstParameter = 1)
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).ReverseJoined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).ReverseJoined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 0) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ReverseWord
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces junctions) :=
      by
  have after := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates.side_reverse_after pieces
    junctions pieceJoin nextJoin finish
  cases count with
  | zero => exact ⟨start, after⟩
  | succ count => exact ⟨start, after⟩

/-- Pointwise decreasing parameter order for every piece and junction is retained by their alternating side word. -/
theorem indexedSideFragments_decreasing
    (pieceOrder : ∀ position, (pieces position).Decreasing)
    (junctionOrder : ∀ position, (junctions position).Decreasing) :
    ∀ item ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces
      junctions, item.Decreasing := by
  induction count with
  | zero =>
    intro item member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact pieceOrder 0
    · cases member
  | succ count ih =>
    intro item member
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact pieceOrder 0
    rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
    · exact junctionOrder 0
    exact ih (fun position => pieces position.succ) (fun position => junctions position.succ)
      (fun position => pieceOrder position.succ) (fun position => junctionOrder position.succ) item member

/-- Grouped side chains are obtained from local physical joins and pointwise
descending parameter order, retaining the original numerical owners and samples. -/
theorem indexedSideFragments_reverse_source_chains
    (start : (pieces 0).firstParameter = 1)
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).ReverseJoined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).ReverseJoined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 0)
    (pieceOrder : ∀ position, (pieces position).Decreasing)
    (junctionOrder : ∀ position, (junctions position).Decreasing) :
    ∀ run ∈ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments pieces
      junctions)).runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0 :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedGrouping.reverse_source_chains
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build _)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates.indexedSideFragments_reverse_word pieces
      junctions start pieceJoin nextJoin finish)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates.indexedSideFragments_decreasing pieces
      junctions pieceOrder junctionOrder)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSideCertificates
