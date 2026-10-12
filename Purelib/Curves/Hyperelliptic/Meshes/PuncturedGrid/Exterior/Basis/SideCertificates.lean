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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments

public section

/-! Derive side grouping certificates from local piece and owner-junction data. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (parentIndex parentIndex_read
  occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock cacheParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks (BlockSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments (IndexedFragment ParentFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping (IndexedRun IndexedGrouping)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback (groupSideFragments
  indexedSideFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

variable {count : Nat}
  (pieces : Fin (count + 1) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
    outer data coefficients)
  (junctions : Fin count →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
    outer data coefficients)

/-- The interleaved original side begins with its retained first physical piece. -/
private theorem indexedSideFragments_cons :
    GroupedSideReadback.indexedSideFragments pieces junctions = pieces 0 :: (GroupedSideReadback.indexedSideFragments
      pieces junctions).tail := by
  cases count <;> rfl

/-- Interleaving original owner junctions preserves successive forward parent positions and the final parent. -/
private theorem side_parent_after
    (junctionParent : ∀ position, (junctions position).parent = (pieces position.castSucc).parent)
    (steps : ∀ position : Fin count,
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val ∨
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val + 1 =
      (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length) :
    IndexedFragment.ParentAfter (pieces 0).parent.val
      (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length
      (GroupedSideReadback.indexedSideFragments pieces junctions).tail := by
  induction count with
  | zero => exact finish
  | succ count ih =>
    refine ⟨Or.inl (congrArg Fin.val (junctionParent 0)), ?_⟩
    rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_cons]
    refine ⟨?_, ih (fun position => pieces position.succ) (fun position => junctions position.succ)
        (fun position => junctionParent position.succ) (fun position => steps position.succ) finish⟩
    rw [junctionParent 0]
    exact steps 0

/-- Owner junctions repeat the preceding parent's position and cannot create an extra parent or skip one in the
exhaustive forward traversal. -/
theorem indexedSideFragments_parentWord
    (junctionParent : ∀ position, (junctions position).parent = (pieces position.castSucc).parent)
    (start : (pieces 0).parent.val = 0)
    (steps : ∀ position : Fin count,
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val ∨
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val + 1 =
      (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length) :
    IndexedFragment.ParentWord (GroupedSideReadback.indexedSideFragments pieces junctions) := by
  have after := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.side_parent_after pieces
    junctions junctionParent steps finish
  cases count with
  | zero => exact ⟨start, after⟩
  | succ count => exact ⟨start, after⟩

/-- Interleaving original owner junctions preserves descending parent positions and the terminal parent zero. -/
private theorem side_reverse_parent_after
    (junctionParent : ∀ position, (junctions position).parent = (pieces position.castSucc).parent)
    (steps : ∀ position : Fin count,
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val ∨
      (pieces position.castSucc).parent.val = (pieces position.succ).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val = 0) :
    IndexedFragment.ReverseParentAfter (pieces 0).parent.val
      (GroupedSideReadback.indexedSideFragments pieces junctions).tail := by
  induction count with
  | zero => exact finish
  | succ count ih =>
    refine ⟨Or.inl (congrArg Fin.val (junctionParent 0)), ?_⟩
    rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_cons]
    refine ⟨?_, ih (fun position => pieces position.succ) (fun position => junctions position.succ)
        (fun position => junctionParent position.succ) (fun position => steps position.succ) finish⟩
    rw [junctionParent 0]
    exact steps 0

/-- Original piece and junction parent certificates give the complete descending parent word. -/
theorem indexedSideFragments_reverseParentWord
    (junctionParent : ∀ position, (junctions position).parent = (pieces position.castSucc).parent)
    (start : (pieces 0).parent.val + 1 =
      (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length)
    (steps : ∀ position : Fin count,
      (pieces position.succ).parent.val = (pieces position.castSucc).parent.val ∨
      (pieces position.castSucc).parent.val = (pieces position.succ).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val = 0) :
    IndexedFragment.ReverseParentWord (GroupedSideReadback.indexedSideFragments pieces junctions) := by
  have after := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.side_reverse_parent_after
    pieces junctions junctionParent steps finish
  cases count with
  | zero => exact ⟨start, after⟩
  | succ count => exact ⟨start, after⟩

/-- Local original piece and junction handoffs retain every forward parameter join through the terminal parameter one.
-/
private theorem side_after
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).Joined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).Joined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 1) :
    IndexedFragment.After (pieces 0) (GroupedSideReadback.indexedSideFragments pieces junctions).tail := by
  induction count with
  | zero => exact finish
  | succ count ih =>
    refine ⟨pieceJoin 0, ?_⟩
    rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_cons]
    exact ⟨nextJoin 0, ih (fun position => pieces position.succ) (fun position => junctions position.succ)
        (fun position => pieceJoin position.succ) (fun position => nextJoin position.succ) finish⟩

/-- Local piece/junction handoffs supply the complete word certificate. -/
theorem indexedSideFragments_word
    (start : (pieces 0).firstParameter = 0)
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).Joined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).Joined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 1) :
    IndexedFragment.Word (GroupedSideReadback.indexedSideFragments pieces junctions) := by
  have after := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.side_after pieces junctions
    pieceJoin nextJoin finish
  cases count with
  | zero => exact ⟨start, after⟩
  | succ count => exact ⟨start, after⟩

/-- Every interleaved original piece and junction has nondecreasing source parameters when each retained entry does. -/
theorem indexedSideFragments_increasing
    (pieceOrder : ∀ position, (pieces position).Increasing)
    (junctionOrder : ∀ position, (junctions position).Increasing) :
    ∀ item ∈ GroupedSideReadback.indexedSideFragments pieces junctions, item.Increasing := by
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

/-- Grouped side chains are obtained from local physical joins and pointwise parameter order, retaining the original
numerical owners and samples. -/
theorem indexedSideFragments_source_chains
    (start : (pieces 0).firstParameter = 0)
    (pieceJoin : ∀ position : Fin count, (pieces position.castSucc).Joined (junctions position))
    (nextJoin : ∀ position : Fin count, (junctions position).Joined (pieces position.succ))
    (finish : (pieces (Fin.last count)).lastParameter = 1)
    (pieceOrder : ∀ position, (pieces position).Increasing)
    (junctionOrder : ∀ position, (junctions position).Increasing) :
    ∀ run ∈ (IndexedGrouping.build (GroupedSideReadback.indexedSideFragments pieces junctions)).runs,
      SourceChains.SourceChain run.fragments 0 1 :=
  IndexedGrouping.source_chains (IndexedGrouping.build _)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_word pieces
      junctions start pieceJoin nextJoin finish)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_increasing pieces
      junctions pieceOrder junctionOrder)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates
