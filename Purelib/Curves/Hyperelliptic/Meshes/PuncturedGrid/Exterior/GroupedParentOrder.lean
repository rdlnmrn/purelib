module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
import Purelib.Data.List.OfFn.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! Remove stationary parent steps using maximal grouping. Start, successor
handoffs and finish then identify the exact retained parent enumeration. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison
open Purelib.Data.List
open Purelib.Data.Rat
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OwnedCapArcComparison (GroupedSourceFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine
    index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other
    target minimum}

variable {evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
  sample otherSample fine}
  {data : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData
    : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}

namespace IndexedOwnedFragment

/-- The remaining original fragment parent positions stay fixed or advance by one and finish at the final retained
parent. -/
@[expose] def ParentAfter (before count : Nat) : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) → Prop
  | [] => before + 1 = count
  | next :: rest => (next.parent.val = before ∨ next.parent.val = before + 1) ∧
      ParentAfter
        next.parent.val count rest

/-- The original fragment parent positions cover the retained bank from zero to its last entry, allowing repeated
consecutive positions. -/
@[expose] def ParentWord : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) → Prop
  | [] => evaluated.retained.length = 0
  | first :: rest => first.parent.val = 0 ∧
    ParentAfter
    first.parent.val evaluated.retained.length rest

end IndexedOwnedFragment

/-- The remaining natural positions advance by exactly one and finish at the supplied count. -/
private def strictTail (before count : Nat) : List Nat → Prop
  | [] => before + 1 = count
  | next :: rest => next = before + 1 ∧ strictTail
    next count rest

/-- A strict successor chain is exactly its consecutive range and determines the final count. -/
private theorem strict_range (first count : Nat) (rest : List Nat)
    (steps : strictTail first count rest) :
    first :: rest = List.range' first (rest.length + 1) ∧ count = first + (rest.length + 1) := by
  induction rest generalizing first with
  | nil => exact ⟨rfl, steps.symm⟩
  | cons next rest ih =>
    have tail := ih next steps.2
    have step : next = first + 1 := steps.1
    constructor
    · exact congrArg (List.cons first) (tail.1.trans
        (congrArg (fun start => List.range' start (rest.length + 1)) step))
    · rw [tail.2, step]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1, -eq_self, -iff_self]
      rfl

/-- Removing an initial run of the same retained parent preserves the remaining parent handoff certificate. -/
private theorem skip_same (parent count : Nat)
    (before after : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData))
    (same : ∀ item ∈ before, item.parent.val = parent)
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter
      parent count (before ++ after)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter parent count
      after := by
  induction before with
  | nil => exact steps
  | cons item rest ih =>
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter index count
      (rest ++ after))
      (same item List.mem_cons_self)).mp steps.2
    exact ih (fun found member => same found (List.mem_cons_of_mem _ member)) remaining

/-- Maximal grouping removes stationary parent steps and leaves strict successive retained parent positions. -/
private theorem strict_parents (rest : List (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    (run : IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData) (count : Nat)
    (apart : IndexedOwnedRun.separated (run :: rest))
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter
      run.parent.val count (run.rest ++ (rest.map IndexedOwnedRun.items).flatten)) :
    strictTail run.parent.val count (rest.map (fun
      run => run.parent.val)) := by
  induction rest generalizing run with
  | nil =>
    exact skip_same run.parent.val count run.rest
      []
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
  | cons next rest ih =>
    have boundary := skip_same run.parent.val
      count run.rest ((next :: rest).map IndexedOwnedRun.items).flatten
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
    have nextEq := congrArg Fin.val next.first_parent
    have different : next.first.parent.val ≠ run.parent.val := by
      intro equal
      exact apart.1 ((Fin.ext equal).symm.trans next.first_parent)
    have step : next.first.parent.val = run.parent.val + 1 := boundary.1.resolve_left different
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter index count
      (next.rest ++ (rest.map IndexedOwnedRun.items).flatten)) nextEq).mp boundary.2
    exact ⟨nextEq.symm.trans step, ih next apart.2 remaining⟩

/-- Equal lists of underlying natural values identify the original bounded-index lists. -/
private theorem fin_values_injective {count : Nat} (first last : List (Fin count))
    (equal : first.map Fin.val = last.map Fin.val) : first = last := by
  induction first generalizing last with
  | nil => cases last with
    | nil => rfl
    | cons => cases equal
  | cons head rest ih => cases last with
    | nil => cases equal
    | cons next tail =>
      have parts := List.cons.inj equal
      exact congrArg₂ List.cons (Fin.ext parts.1) (ih tail parts.2)

/-- Enumerating offset bounded positions yields the corresponding consecutive natural range. -/
private theorem indices_range (count offset : Nat) :
    List.ofFn (fun i : Fin count => offset + i.val) = List.range' offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    change offset :: List.ofFn (fun i : Fin count => offset + (i.val + 1)) = _
    have tail : List.ofFn (fun i : Fin count => offset + (i.val + 1)) =
        List.ofFn (fun i : Fin count => (offset + 1) + i.val) := by
      apply OfFn.Basic.ofFn_congr
      intro i
      rw [Nat.add_assoc, Nat.add_comm 1]
    rw [tail, ih]
    rfl

/-- Reading every original bounded list position reconstructs the exact list. -/
private theorem ofFn_read {Item : Type u} (items : List Item) :
    List.ofFn (fun i : Fin items.length => items[i.val]'i.isLt) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact congrArg (List.cons head) ih

namespace IndexedOwnedGrouping
variable {items : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping.IndexedOwnedFragment
  evaluated data otherData)}

/-- The grouped original run positions enumerate the entire retained parent range in order. -/
theorem parent_values (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentWord items)
      :
    grouped.runs.map (fun run => run.parent.val) = List.range' 0 evaluated.retained.length := by
  rw [← grouped.flattened] at word
  cases runsEq : grouped.runs with
  | nil =>
    rw [runsEq] at word
    change evaluated.retained.length = 0 at word
    change ([] : List Nat) = List.range' 0 evaluated.retained.length
    rw [word]
    rfl
  | cons run rest =>
    rw [runsEq] at word
    have firstEq : run.parent.val = 0 := (congrArg Fin.val run.first_parent).symm.trans word.1
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentAfter index
      evaluated.retained.length
      (run.rest ++ (rest.map IndexedOwnedRun.items).flatten)) (congrArg Fin.val run.first_parent)).mp word.2
    have strict := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.strict_parents rest run
      evaluated.retained.length
      ((congrArg IndexedOwnedRun.separated runsEq).mp grouped.separated) remaining
    have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.strict_range run.parent.val
      evaluated.retained.length (rest.map (fun run => run.parent.val)) strict
    rw [firstEq, Nat.zero_add] at ranged
    change run.parent.val :: _ = _
    rw [firstEq]
    exact ranged.1.trans (congrArg (List.range' 0) ranged.2.symm)

/-- The actual retained entries, including their order and multiplicity, are recovered from the grouped parent indices
without comparing payloads. -/
theorem parent_entries (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
    (word : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentWord items)
      :
    grouped.runs.map (fun run => IndexedSourceSplits.indexedEntry evaluated run.parent) = evaluated.retained := by
  have indices : grouped.runs.map IndexedOwnedRun.parent = List.ofFn (fun i : Fin evaluated.retained.length => i) := by
    apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.fin_values_injective
    rw [Data.List.Map.map_map, OfFn.Basic.map_ofFn]
    have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.indices_range
      evaluated.retained.length 0
    have equal : List.ofFn (fun i : Fin evaluated.retained.length => i.val) =
        List.ofFn (fun i : Fin evaluated.retained.length => 0 + i.val) :=
      OfFn.Basic.ofFn_congr (fun i => (Nat.zero_add i.val).symm)
    exact (parent_values
      grouped word).trans (equal.trans ranged).symm
  have entries := congrArg (List.map (IndexedSourceSplits.indexedEntry evaluated)) indices
  rw [Data.List.Map.map_map, OfFn.Basic.map_ofFn] at entries
  exact entries.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.ofFn_read
    evaluated.retained)

/-- The certified complete source groups retain every original parent entry in its exact bank order. -/
theorem certify_parent_order (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
  (width : InverseRootPolynomial.Coordinate)
    (word : IndexedOwnedFragment.Word items) (fineEnough : ∀ item ∈ items, IndexedOwnedFragment.FineEnough item width)
    (parentWord : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder.IndexedOwnedFragment.ParentWord
      items) :
    (IndexedOwnedGrouping.certify grouped width word fineEnough).map GroupedSourceFragments.entry = evaluated.retained
      :=
  (IndexedOwnedGrouping.certify_parents grouped width word fineEnough).trans
    (parent_entries grouped
    parentWord)

end IndexedOwnedGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
