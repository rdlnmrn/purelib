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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
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

/-! Attach the retained parent positions to cached piece and junction
samples in their existing interleaved family order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison (interleaveFragments)
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

/-- Interleave the original indexed physical pieces and their retained intervening owner junctions in traversal order.

There is one more physical piece than owner junction. The recursion retains the piece-junction order and shifts both
finite input functions through their original successor indices. -/
@[expose]
def interleaveIndexed : {count : Nat} →
    (Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) →
    (Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) → List
      (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      interleaveIndexed (fun i =>
        pieces i.succ) (fun i => junctions i.succ)

/-- Removing retained parent indices commutes with the original piece-junction interleaving. -/
private theorem interleave_fragments {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) :
    (interleaveIndexed pieces junctions).map
      IndexedOwnedFragment.fragment =
      JoinedFragmentComparison.interleaveFragments (fun i => (pieces i).fragment) (fun i => (junctions i).fragment) :=
        by
  induction count with
  | zero => rfl
  | succ count ih =>
    exact congrArg (List.cons (pieces 0).fragment)
      (congrArg (List.cons (junctions 0).fragment) (ih (fun i => pieces i.succ) (fun i => junctions i.succ)))

/-- The original piece-parent steps and preceding-parent junction assignments preserve the complete parent handoff
chain. -/
private theorem interleave_parent_after {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (same : ∀ i, (junctions i).parent = (pieces i.castSucc).parent)
    (steps : ∀ i : Fin count, (pieces i.succ).parent.val = (pieces i.castSucc).parent.val ∨
      (pieces i.succ).parent.val = (pieces i.castSucc).parent.val + 1)
    (finish : (pieces (Fin.last count)).parent.val + 1 = evaluated.retained.length)
    (before : Nat) (advance : (pieces 0).parent.val = before ∨ (pieces 0).parent.val = before + 1) :
    IndexedOwnedFragment.ParentAfter before evaluated.retained.length
      (interleaveIndexed pieces junctions) :=
      by
  induction count generalizing before with
  | zero => exact ⟨advance, finish⟩
  | succ count ih =>
    refine ⟨advance, Or.inl (congrArg Fin.val (same 0)), ?_⟩
    apply ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => same i.succ) (fun i => steps i.succ) finish
    have next := steps 0
    have joint := congrArg Fin.val (same 0)
    exact next.elim (fun equal => Or.inl (equal.trans joint.symm))
      (fun equal => Or.inr (equal.trans (congrArg (· + 1) joint.symm)))

/-- Original piece-to-junction and junction-to-piece parameter joins preserve the complete interleaved tail chain. -/
private theorem interleave_after {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (into : ∀ i, (IndexedOwnedFragment.Joined (pieces i.castSucc) (junctions i)))
    (out : ∀ i, (IndexedOwnedFragment.Joined (junctions i) (pieces i.succ)))
    (finish : (IndexedOwnedFragment.lastParameter (pieces (Fin.last count))) = 1)
    (before : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) (joined :
      (IndexedOwnedFragment.Joined before) (pieces 0)) :
    IndexedOwnedFragment.After before
      (interleaveIndexed pieces junctions) :=
      by
  induction count generalizing before with
  | zero => exact ⟨joined, finish⟩
  | succ count ih =>
    exact ⟨joined, into 0, ih (fun i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => into i.succ) (fun i => out i.succ) finish (junctions 0) (out 0)⟩

/-- The original start, finish and local piece-junction joins certify the complete interleaved source parameter word. -/
private theorem interleave_word {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (into : ∀ i, (IndexedOwnedFragment.Joined (pieces i.castSucc) (junctions i)))
    (out : ∀ i, (IndexedOwnedFragment.Joined (junctions i) (pieces i.succ)))
    (start : (IndexedOwnedFragment.firstParameter (pieces 0)) = 0) (finish : (IndexedOwnedFragment.lastParameter (pieces
      (Fin.last count))) = 1) :
    IndexedOwnedFragment.Word
      (interleaveIndexed pieces junctions) :=
      by
  cases count with
  | zero => exact ⟨start, finish⟩
  | succ count =>
    exact ⟨start, into 0, interleave_after (fun
      i => pieces i.succ) (fun i => junctions i.succ)
      (fun i => into i.succ) (fun i => out i.succ) finish (junctions 0) (out 0)⟩

/-- A property of every original indexed piece and junction holds for their full interleaved word.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
private theorem interleave_property {count : Nat}
    (pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (property : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData → Prop)
    (pieceProof : ∀ i, property (pieces i)) (junctionProof : ∀ i, property (junctions i)) :
    ∀ item ∈ interleaveIndexed pieces
      junctions, property item := by
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

namespace JoinedFragmentFamily

variable {Vertex : Type} {count : Nat} {values : Vertex → Purelib.Topology.Polygon.Stokes.PrimitivePoint}
  {traces : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace Vertex}

/-- Read the existing banks; the physical junction retains its preceding piece's parent index, including at a handoff to
a different next parent.

The interleaved list retains each physical piece and intervening owner junction together with its original parent index
and comparison evidence. -/
@[expose]
def indexedItems (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData :=
  otherData) values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc)) :
    List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.interleaveIndexed (fun i => ⟨parents i,
    (family.pieces.get i).fragment, pieceOwners i⟩)
    (fun i => ⟨parents i.castSucc, (family.junctions.get i).fragment, junctionOwners i⟩)

/-- Removing parent indices from the retained indexed family returns its exact cached fragment list. -/
theorem indexedItems_readback
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc)) :
    ((indexedItems family)
      parents pieceOwners junctionOwners).map IndexedOwnedFragment.fragment = family.fragments :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.interleave_fragments _ _).trans
    family.fragments_eq.symm

/-- The duplicated parent at every owner junction is a stationary step; the piece bank alone supplies the initial,
successor and final index evidence. -/
theorem indexedItems_parent_word
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (start : (parents 0).val = 0)
    (steps : ∀ i : Fin count, (parents i.succ).val = (parents i.castSucc).val ∨
      (parents i.succ).val = (parents i.castSucc).val + 1)
    (finish : (parents (Fin.last count)).val + 1 = evaluated.retained.length) :
    IndexedOwnedFragment.ParentWord
      ((indexedItems
      family) parents pieceOwners junctionOwners) := by
  let pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i, (family.pieces.get i).fragment, pieceOwners i⟩
  let junctions : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i.castSucc, (family.junctions.get i).fragment, junctionOwners i⟩
  have after := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.interleave_parent_after pieces
    junctions (fun _ => rfl) steps finish (parents 0).val (Or.inl rfl)
  cases count with
  | zero => exact ⟨start, after.2⟩
  | succ count => exact ⟨start, after.2⟩

/-- Read the actual initial source parameter of the retained physical piece fragment. -/
@[expose]
def pieceStart (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData :=
  otherData) values traces)
    (i : Fin (count + 1)) : Coordinate := (family.pieces.get i).fragment.parameters 0

/-- Read the actual terminal source parameter of the retained physical piece fragment. -/
@[expose]
def pieceFinish (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData :=
  otherData) values traces)
    (i : Fin (count + 1)) : Coordinate :=
  let fragment := (family.pieces.get i).fragment
  fragment.parameters (Fin.last fragment.count)

/-- Stationary owner junctions and physical parent handoffs assemble the whole parameter word without discarding the
junction samples. -/
theorem indexedItems_word
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (start : (pieceStart
      family) 0 = 0) (finish :
      (pieceFinish family)
      (Fin.last count) = 1)
    (junctions : ∀ i vertex, (family.junctions.get i).fragment.parameters vertex =
      (pieceFinish family)
      i.castSucc)
    (same : ∀ i : Fin count, parents i.castSucc = parents i.succ →
      (pieceFinish family)
      i.castSucc =
      (pieceStart family)
      i.succ)
    (handoff : ∀ i : Fin count, parents i.castSucc ≠ parents i.succ →
      (pieceFinish family)
      i.castSucc = 1 ∧
      (pieceStart family)
      i.succ = 0) :
    IndexedOwnedFragment.Word
      ((indexedItems
      family) parents pieceOwners junctionOwners) := by
  let pieces : Fin (count + 1) → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i, (family.pieces.get i).fragment, pieceOwners i⟩
  let joints : Fin count → IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData :=
    fun i => ⟨parents i.castSucc, (family.junctions.get i).fragment, junctionOwners i⟩
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.interleave_word pieces joints _ _ start
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

/-- Local bounds on both cached banks cover every interleaved item. -/
theorem indexedItems_fine_enough
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (parents : Fin (count + 1) → Fin evaluated.retained.length)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents i))
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (parents
      i.castSucc))
    (width : InverseRootPolynomial.Coordinate)
    (pieces : ∀ i, let fragment := (family.pieces.get i).fragment
      fragment.forward = true ∧ ∀ edge : Fin fragment.count,
        fragment.parameters edge.succ - fragment.parameters edge.castSucc ≤ width)
    (junctions : ∀ i, let fragment := (family.junctions.get i).fragment
      fragment.forward = true ∧ ∀ edge : Fin fragment.count,
        fragment.parameters edge.succ - fragment.parameters edge.castSucc ≤ width) :
    ∀ item ∈ (indexedItems
      family) parents pieceOwners junctionOwners, (IndexedOwnedFragment.FineEnough item width) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.interleave_property _ _ (fun item =>
    (IndexedOwnedFragment.FineEnough item width)) pieces junctions

end JoinedFragmentFamily
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
