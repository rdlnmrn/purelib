module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

/-! Descending certificates for the original interleaved fragment sequence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping (IndexedOwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily (interleaveIndexed)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.JoinedFragmentFamily (indexedItems
  pieceStart pieceFinish)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment (ReverseJoined
  ReverseFineEnough)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains.IndexedOwnedFragment
  (firstParameter lastParameter)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

/-- Interleaving the original pieces and same-parent junctions preserves descending parent positions through the first
retained parent. -/
private theorem IndexedReverseFamily.interleave_parent_after {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (same : ∀ i, (junctions i).parent = (pieces i.castSucc).parent)
    (steps : ∀ i : Fin count, (pieces i.succ).parent.val = (pieces i.castSucc).parent.val ∨
      (pieces i.castSucc).parent.val = (pieces i.succ).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val = 0)
    (before : Nat) (advance : (pieces 0).parent.val = before ∨ before = (pieces 0).parent.val + 1) :
    IndexedOwnedFragment.ReverseParentAfter before (IndexedFragmentFamily.interleaveIndexed pieces junctions) := by
  induction count generalizing before with
  | zero => exact ⟨advance, finish⟩
  | succ count ih =>
    refine ⟨advance, Or.inl (congrArg Fin.val (same 0)), ?_⟩
    apply ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => same i.succ) (fun i => steps i.succ) finish
    have next := steps 0
    have joint := congrArg Fin.val (same 0)
    exact next.elim (fun equal => Or.inl (equal.trans joint.symm))
      (fun equal => Or.inr (joint.trans equal))

/-- Interleaving the original pieces and owner junctions preserves their retained reverse joins and terminal parameter
zero. -/
private theorem IndexedReverseFamily.interleave_after {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (into : ∀ i, IndexedOwnedFragment.ReverseJoined (pieces i.castSucc) (junctions i))
    (out : ∀ i, IndexedOwnedFragment.ReverseJoined (junctions i) (pieces i.succ))
    (finish : IndexedOwnedFragment.lastParameter (pieces (Fin.last count)) = 0)
    (before : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) (joined :
      IndexedOwnedFragment.ReverseJoined before (pieces 0)) :
    IndexedOwnedFragment.ReverseAfter before (IndexedFragmentFamily.interleaveIndexed pieces junctions) := by
  induction count generalizing before with
  | zero => exact ⟨joined, finish⟩
  | succ count ih =>
    exact ⟨joined, into 0, ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => into i.succ) (fun i => out i.succ) finish (junctions 0) (out 0)⟩

/-- The original interleaved physical family forms a complete reverse parameter word from one to zero. -/
private theorem IndexedReverseFamily.interleave_word {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (into : ∀ i, IndexedOwnedFragment.ReverseJoined (pieces i.castSucc) (junctions i))
    (out : ∀ i, IndexedOwnedFragment.ReverseJoined (junctions i) (pieces i.succ))
    (start : IndexedOwnedFragment.firstParameter (pieces 0) = 1) (finish : IndexedOwnedFragment.lastParameter (pieces
      (Fin.last count)) = 0) :
    IndexedOwnedFragment.ReverseWord (IndexedFragmentFamily.interleaveIndexed pieces junctions) := by
  cases count with
  | zero => exact ⟨start, finish⟩
  | succ count =>
    exact ⟨start, into 0, Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily.interleave_after (fun
      i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => into i.succ) (fun i => out i.succ) finish (junctions 0) (out 0)⟩

/-- A property of each original indexed piece and junction holds throughout their ordered interleaving.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
private theorem IndexedReverseFamily.interleave_property {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (property : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData → Prop)
    (pieceProof : ∀ i, property (pieces i)) (junctionProof : ∀ i, property (junctions i)) :
    ∀ item ∈ IndexedFragmentFamily.interleaveIndexed pieces junctions, property item := by
  induction count with
  | zero =>
    intro item member
    have same := Membership.mem_singleton.mp member
    exact same ▸ pieceProof 0
  | succ count ih =>
    intro item member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact pieceProof 0
    rcases Membership.mem_cons.mp member with rfl | member
    · exact junctionProof 0
    exact ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => pieceProof i.succ) (fun i => junctionProof i.succ) item member

namespace FragmentFamilies.JoinedFragmentFamily

variable {Vertex : Type} {count : Nat} {values : Vertex → Purelib.Topology.Polygon.Stokes.PrimitivePoint}
  {traces : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace Vertex}

/-- The family's original parent indices form a complete descending parent word, retaining the same index on each
following owner junction. -/
theorem
  indexedItems_reverse_parent_word
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (start : (parents 0).val + 1 = evaluated.retained.length)
    (steps : ∀ i : Fin count, (parents i.succ).val = (parents i.castSucc).val ∨
      (parents i.castSucc).val = (parents i.succ).val + 1)
    (finish : (parents (Fin.last count)).val = 0) :
    IndexedOwnedFragment.ReverseParentWord (JoinedFragmentFamily.indexedItems family parents pieceOwners junctionOwners)
      := by
  let pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i, (family.pieces.get i).fragment, pieceOwners i⟩
  let junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i.castSucc, (family.junctions.get i).fragment, junctionOwners i⟩
  have after := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily.interleave_parent_after pieces
    junctions (fun _ => rfl) steps finish (parents 0).val (Or.inl rfl)
  cases count with
  | zero => exact ⟨start, after.2⟩
  | succ count => exact ⟨start, after.2⟩

/-- The original interleaved family forms a reverse parameter word when same-parent joins and changed-parent endpoint
handoffs agree. -/
theorem
  indexedItems_reverse_word
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (start : JoinedFragmentFamily.pieceStart family 0 = 1) (finish : JoinedFragmentFamily.pieceFinish family (Fin.last
      count) = 0)
    (junctions : ∀ i vertex, (family.junctions.get i).fragment.parameters vertex = JoinedFragmentFamily.pieceFinish
      family i.castSucc)
    (same : ∀ i : Fin count, parents i.castSucc = parents i.succ → JoinedFragmentFamily.pieceFinish family i.castSucc =
      JoinedFragmentFamily.pieceStart family i.succ)
    (handoff : ∀ i : Fin count, parents i.castSucc ≠ parents i.succ → JoinedFragmentFamily.pieceFinish family i.castSucc
      = 0 ∧ JoinedFragmentFamily.pieceStart family i.succ = 1) :
    IndexedOwnedFragment.ReverseWord (JoinedFragmentFamily.indexedItems family parents pieceOwners junctionOwners) := by
  let pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i, (family.pieces.get i).fragment, pieceOwners i⟩
  let joints : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i.castSucc, (family.junctions.get i).fragment, junctionOwners i⟩
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily.interleave_word pieces joints _ _ start
    finish
  · intro i
    exact ⟨fun _ => (junctions i 0).symm, fun different => (different rfl).elim⟩
  · intro i
    constructor
    · intro equal
      exact (junctions i (Fin.last (family.junctions.get i).fragment.count)).trans (same i equal)
    · intro different
      have ends := handoff i different
      exact ⟨(junctions i (Fin.last (family.junctions.get i).fragment.count)).trans ends.1, ends.2⟩

/-- The original piece and junction step bounds hold for every indexed fragment of their retained reverse family. -/
theorem
  indexedItems_reverse_fine_enough
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (width : InverseRootPolynomial.Coordinate)
    (pieces : ∀ i, let fragment := (family.pieces.get i).fragment
      (∀ edge : Fin fragment.count, fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc) ∧
      ∀ edge : Fin fragment.count, fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ width)
    (junctions : ∀ i, let fragment := (family.junctions.get i).fragment
      (∀ edge : Fin fragment.count, fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc) ∧
      ∀ edge : Fin fragment.count, fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ width) :
    ∀ item ∈ JoinedFragmentFamily.indexedItems family parents pieceOwners junctionOwners,
      IndexedOwnedFragment.ReverseFineEnough item width :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily.interleave_property _ _ (fun item =>
    IndexedOwnedFragment.ReverseFineEnough item width) pieces junctions

end FragmentFamilies.JoinedFragmentFamily
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
