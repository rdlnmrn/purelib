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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc
import Init.Data.List.Lemmas
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! Derive descending parent-run certificates from the original indexed word.
The existing grouping preserves the physical order and every cached junction. -/
section

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping (IndexedOwnedFragment
  IndexedOwnedRun IndexedOwnedGrouping)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns (ReverseSourceFragmentChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc (ReverseGroupedSourceFragments)
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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment

/-- Adjacent descending fragments meet within the identical retained parent or pass from parameter zero to one when the
parent position changes. -/
@[expose] def ReverseJoined (before after : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) :
  Prop :=
  (before.parent = after.parent → (IndexedOwnedFragment.lastParameter before) = (IndexedOwnedFragment.firstParameter
    after)) ∧
  (before.parent ≠ after.parent → (IndexedOwnedFragment.lastParameter before) = 0 ∧ (IndexedOwnedFragment.firstParameter
    after) = 1)

/-- The original descending fragment tail retains every parameter handoff and ends at zero. -/
@[expose] def ReverseAfter (before : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) : List
  (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) → Prop
  | [] => (IndexedOwnedFragment.lastParameter before) = 0
  | after :: rest =>
    ReverseJoined before
    after ∧
    ReverseAfter
    after rest

/-- The original descending fragment word starts at one, retains every parent handoff and finishes at zero. -/
@[expose] def ReverseWord : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) → Prop
  | [] => True
  | first :: rest => (IndexedOwnedFragment.firstParameter first) = 1 ∧
    ReverseAfter first rest

/-- Every original retained source step is descending and has magnitude at most the supplied width. -/
@[expose] def ReverseFineEnough (item : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) (width :
  InverseRootPolynomial.Coordinate) : Prop :=
  (∀ edge : Fin item.fragment.count, item.fragment.parameters edge.succ ≤ item.fragment.parameters edge.castSucc) ∧
    ∀ edge : Fin item.fragment.count,
      item.fragment.parameters edge.castSucc - item.fragment.parameters edge.succ ≤ width

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment
  (ReverseFineEnough)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains

/-- The supplied parent position differs from the next original indexed fragment's parent, when present. -/
private def apart (parent : Fin evaluated.retained.length) : List (IndexedFragmentGrouping.IndexedOwnedFragment
  evaluated data otherData) → Prop
  | [] => True
  | item :: _ => parent ≠ item.parent

/-- A complete retained same-parent descending run forms a chain ending at zero and leaves a correctly initialized
descending word.

The original parameter handoffs, parent separation and bounded descending steps provide the chain certificates. -/
private theorem finish_run (parent : Fin evaluated.retained.length) (width : InverseRootPolynomial.Coordinate)
    (first : IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData)
    (rest after : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData))
    (firstParent : first.parent = parent) (restParent : ∀ item ∈ rest, item.parent = parent)
    (ends : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseAfter
      first (rest ++ after)) (separate : apart
      parent after)
    (fineEnough : ∀ item ∈ first :: rest,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated parent) width
      ((first :: rest).map IndexedOwnedFragment.fragment) (IndexedOwnedFragment.firstParameter first) 0 ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord after :=
        by
  induction rest generalizing first with
  | nil =>
    have last : (IndexedOwnedFragment.lastParameter first) = 0 ∧
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord after :=
      by
      cases after with
      | nil => exact ⟨ends, True.intro⟩
      | cons next tail =>
        have different : first.parent ≠ next.parent := fun same => separate (firstParent.symm.trans same)
        have joined := ends.1.2 different
        exact ⟨joined.1, joined.2, ends.2⟩
    have fine := fineEnough first List.mem_cons_self
    refine ⟨ReverseSourceFragmentChain.cons first.fragment
      (first.entry_eq.trans (congrArg (IndexedSourceSplits.indexedEntry evaluated) firstParent)) fine.1 fine.2 ?_,
        last.2⟩
    change ReverseFragmentRuns.ReverseSourceFragmentChain _ _ [] (IndexedOwnedFragment.lastParameter first) 0
    rw [last.1]
    exact .nil 0
  | cons next rest ih =>
    have nextParent := restParent next List.mem_cons_self
    have result := ih next nextParent (fun item member => restParent item (List.mem_cons_of_mem _ member)) ends.2
      (fun item member => fineEnough item (List.mem_cons_of_mem _ member))
    have joined := ends.1.1 (firstParent.trans nextParent.symm)
    have fine := fineEnough first List.mem_cons_self
    refine ⟨ReverseSourceFragmentChain.cons first.fragment
      (first.entry_eq.trans (congrArg (IndexedSourceSplits.indexedEntry evaluated) firstParent)) fine.1 fine.2 ?_,
        result.2⟩
    change ReverseFragmentRuns.ReverseSourceFragmentChain _ _ _ (IndexedOwnedFragment.lastParameter first) 0
    rw [joined]
    exact result.1

/-- Every maximal run of the original fine descending fragment word is a complete source chain from one to zero. -/
private theorem runs_chains (runs : List (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData)) (width :
  InverseRootPolynomial.Coordinate)
    (separated : IndexedOwnedRun.separated runs)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      (runs.map IndexedOwnedRun.items).flatten)
    (fineEnough : ∀ item ∈ (runs.map IndexedOwnedRun.items).flatten,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    ∀ run ∈ runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated run.parent)
      width run.fragments 1 0 := by
  induction runs with
  | nil => intro _ member; cases member
  | cons run rest ih =>
    have separate : apart run.parent (rest.map
      IndexedOwnedRun.items).flatten := by
      cases rest with
      | nil => trivial
      | cons next tail =>
        exact fun same => separated.1 (same.trans next.first_parent)
    have result := finish_run run.parent width
      run.first run.rest (rest.map IndexedOwnedRun.items).flatten
      run.first_parent run.rest_parent word.2 separate
      (fun item member => fineEnough item (Membership.mem_append.mpr (Or.inl member)))
    have firstChain : ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0 := by
      have chain := result.1
      rw [word.1] at chain
      exact chain
    have tailChains := ih separated.2 result.2
      (fun item member => fineEnough item (Membership.mem_append.mpr (Or.inr member)))
    intro selected member
    rcases Membership.mem_cons.mp member with rfl | member
    · exact firstChain
    · exact tailChains selected member

/-- Package each original descending run with its identical source entry, fragments, common width and complete reverse
chain. -/
@[expose] def certifyReverseRuns (width : InverseRootPolynomial.Coordinate) :
    (runs : List (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData)) →
    (∀ run ∈ runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0) →
    List (ReverseOwnedCapArc.ReverseGroupedSourceFragments evaluated data otherData)
  | [], _ => []
  | run :: rest, chains =>
    ⟨indexedEntry evaluated run.parent, run.fragments, width, chains run List.mem_cons_self⟩ ::
      certifyReverseRuns width rest (fun
        run member => chains run (List.mem_cons_of_mem _ member))

/-- Certifying the original descending runs preserves their exact fragment lists. -/
theorem certifyReverseRuns_fragments (width : InverseRootPolynomial.Coordinate) (runs : List
  (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    (chains : ∀ run ∈ runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0) :
    (certifyReverseRuns width runs chains).map
      ReverseGroupedSourceFragments.fragments = runs.map IndexedOwnedRun.fragments := by
  induction runs with
  | nil => rfl
  | cons run rest ih => exact congrArg (List.cons run.fragments) (ih _)

/-- Certifying the original descending runs preserves their retained source entries in physical order. -/
theorem certifyReverseRuns_parents (width : InverseRootPolynomial.Coordinate) (runs : List
  (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    (chains : ∀ run ∈ runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0) :
    (certifyReverseRuns width runs chains).map
      ReverseGroupedSourceFragments.entry =
      runs.map (fun run => IndexedSourceSplits.indexedEntry evaluated run.parent) := by
  induction runs with
  | nil => rfl
  | cons run rest ih => exact congrArg (List.cons (IndexedSourceSplits.indexedEntry evaluated run.parent)) (ih _)

/-- Every certified original descending run retains the supplied common parameter width. -/
theorem certifyReverseRuns_widths (width : InverseRootPolynomial.Coordinate) (runs : List
  (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    (chains : ∀ run ∈ runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0) :
    ∀ group ∈ certifyReverseRuns width runs
      chains, group.width = width := by
  induction runs with
  | nil => intro _ member; cases member
  | cons run rest ih =>
    intro group member
    rcases Membership.mem_cons.mp member with rfl | member
    · rfl
    · exact ih _ group member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains

variable {items : List
  (IndexedOwnedFragment evaluated
  data otherData)}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedGrouping

/-- Complete parent chains follow from the original word's physical joins and endpoint handoffs, together with the
grouping's maximal-run certificate. -/
theorem reverse_source_chains (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
  (width : InverseRootPolynomial.Coordinate)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      items) (fineEnough : ∀ item ∈ items,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    ∀ run ∈ grouped.runs, ReverseFragmentRuns.ReverseSourceFragmentChain (IndexedSourceSplits.indexedEntry evaluated
      run.parent) width run.fragments 1 0 := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.runs_chains grouped.runs width
    grouped.separated
  · rw [grouped.flattened]
    exact word
  · rw [grouped.flattened]
    exact fineEnough

/-- Package each maximal run with its derived complete parameter chain. Only existing source entries and fragment
samples are retained. -/
@[expose] def certify_reverse (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
  (width : InverseRootPolynomial.Coordinate)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      items) (fineEnough : ∀ item ∈ items,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    List (ReverseOwnedCapArc.ReverseGroupedSourceFragments evaluated data otherData) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.certifyReverseRuns width grouped.runs
    (reverse_source_chains
    grouped width word fineEnough)

/-- Flattening the certified descending groups returns the exact original owned fragment word. -/
theorem certify_reverse_partition (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData
  items) (width : InverseRootPolynomial.Coordinate)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      items) (fineEnough : ∀ item ∈ items,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    ((certify_reverse
      grouped width word fineEnough).map ReverseGroupedSourceFragments.fragments).flatten =
      items.map IndexedOwnedFragment.fragment :=
  (congrArg List.flatten
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.certifyReverseRuns_fragments width
    grouped.runs _)).trans grouped.fragments_eq

/-- The certified descending groups retain the original grouped parent entries in physical order. -/
theorem certify_reverse_parents (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
  (width : InverseRootPolynomial.Coordinate)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      items) (fineEnough : ∀ item ∈ items,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    (certify_reverse
      grouped width word fineEnough).map ReverseGroupedSourceFragments.entry =
      grouped.runs.map (fun run => IndexedSourceSplits.indexedEntry evaluated run.parent) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.certifyReverseRuns_parents width grouped.runs
    _

/-- Every certified descending group retains the original common parameter-width bound. -/
theorem certify_reverse_widths (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
  (width : InverseRootPolynomial.Coordinate)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseWord
      items) (fineEnough : ∀ item ∈ items,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment.ReverseFineEnough
      item width) :
    ∀ group ∈
      certify_reverse
      grouped width word fineEnough, group.width = width :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.certifyReverseRuns_widths width grouped.runs _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedGrouping

end
