module
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
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

/-! Descending parent handoffs certify exhaustive source order after reversal. -/
section

open Purelib.Data.List

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseOwnedCapArc
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping (IndexedOwnedFragment
  IndexedOwnedRun IndexedOwnedGrouping)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment

/-- The original fragment parent positions stay fixed or decrease by one, ending at the first retained parent. -/
@[expose] def ReverseParentAfter (before : Nat) : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data
  otherData) → Prop
  | [] => before = 0
  | next :: rest => (next.parent.val = before ∨ before = next.parent.val + 1) ∧

        ReverseParentAfter
        next.parent.val rest

/-- A complete descending word of original parent positions, starting at the last retained parent and ending at the
first. -/
@[expose] def ReverseParentWord : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData) → Prop
  | [] => evaluated.retained.length = 0
  | first :: rest => first.parent.val + 1 = evaluated.retained.length ∧
    ReverseParentAfter
    first.parent.val rest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder

/-- The remaining natural positions decrease by exactly one at every step and finish at zero. -/
private def strictTail (before : Nat) : List Nat → Prop
  | [] => before = 0
  | next :: rest => before = next + 1 ∧
    strictTail next rest

/-- Reversing a complete strictly descending position list recovers its ascending initial natural range. -/
private theorem strict_range (first : Nat) (rest : List Nat) (steps :
  strictTail first rest) :
    (first :: rest).reverse = List.range' 0 (first + 1) := by
  induction rest generalizing first with
  | nil => rw [show first = 0 from steps]; rfl
  | cons next rest ih =>
    rw [Reverse.reverse_cons, ih next steps.2, steps.1]
    simpa only [Nat.zero_add, -eq_self, -iff_self] using (Range.Basic.range'_succ 0 (next + 1)).symm

/-- Removing an initial run of equal original parent positions preserves the remaining descending parent chain. -/
private theorem skip_same (parent : Nat)
    (before after : List (IndexedFragmentGrouping.IndexedOwnedFragment evaluated data otherData))
    (same : ∀ item ∈ before, item.parent.val = parent)
    (steps :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      parent (before ++ after)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      parent after := by
  induction before with
  | nil => exact steps
  | cons item rest ih =>
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      index (rest ++ after))
      (same item List.mem_cons_self)).mp steps.2
    exact ih (fun found member => same found (List.mem_cons_of_mem _ member)) remaining

/-- Maximal grouping turns the original stationary-or-decreasing parent word into a strictly descending run-parent list.
-/
private theorem strict_parents (rest : List (IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData))
    (run : IndexedFragmentGrouping.IndexedOwnedRun evaluated data otherData)
    (apart : IndexedOwnedRun.separated (run :: rest))
    (steps :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      run.parent.val (run.rest ++ (rest.map IndexedOwnedRun.items).flatten)) :
    strictTail run.parent.val (rest.map (fun run
      => run.parent.val)) := by
  induction rest generalizing run with
  | nil =>
    exact skip_same run.parent.val run.rest []
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
  | cons next rest ih =>
    have boundary := skip_same run.parent.val
      run.rest ((next :: rest).map IndexedOwnedRun.items).flatten
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
    have nextEq := congrArg Fin.val next.first_parent
    have different : next.first.parent.val ≠ run.parent.val := by
      intro equal
      exact apart.1 ((Fin.ext equal).symm.trans next.first_parent)
    have step : run.parent.val = next.first.parent.val + 1 := boundary.1.resolve_left different
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      index
      (next.rest ++ (rest.map IndexedOwnedRun.items).flatten)) nextEq).mp boundary.2
    exact ⟨step.trans (congrArg (fun n => n + 1) nextEq), ih next apart.2 remaining⟩

/-- Lists of bounded original positions are equal when their natural-value lists are equal. -/
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

/-- Reading an offset bounded-index enumeration gives the corresponding consecutive natural range. -/
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

/-- Enumerating every bounded position reconstructs the exact original list in order. -/
private theorem ofFn_read {Item : Type u} (items : List Item) :
    List.ofFn (fun i : Fin items.length => items[i.val]'i.isLt) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact congrArg (List.cons head) ih

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder

variable {items : List
  (IndexedOwnedFragment evaluated
  data otherData)}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedGrouping

/-- The reversed grouped run-parent values enumerate every original retained parent position in ascending order. -/
theorem reverse_parent_values (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
    (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentWord
      items) :
    grouped.runs.reverse.map (fun run => run.parent.val) = List.range' 0 evaluated.retained.length := by
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
    have firstEq : run.parent.val + 1 = evaluated.retained.length :=
      (congrArg (fun i : Fin evaluated.retained.length => i.val + 1) run.first_parent).symm.trans word.1
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentAfter
      index
      (run.rest ++ (rest.map IndexedOwnedRun.items).flatten)) (congrArg Fin.val run.first_parent)).mp word.2
    have strict := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.strict_parents rest run
      ((congrArg IndexedOwnedRun.separated runsEq).mp grouped.separated) remaining
    have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.strict_range run.parent.val
      (rest.map (fun run => run.parent.val)) strict
    rw [Reverse.map_reverse]
    exact ranged.trans (congrArg (List.range' 0) firstEq)

/-- Reversing the certified physical run order recovers every retained source entry in its original order, including
repeated payloads. -/
theorem reverse_parent_entries (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData items)
    (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentWord
      items) :
    grouped.runs.reverse.map (fun run => IndexedSourceSplits.indexedEntry evaluated run.parent) = evaluated.retained :=
      by
  have indices : grouped.runs.reverse.map IndexedOwnedRun.parent = List.ofFn (fun i : Fin evaluated.retained.length =>
    i) := by
    apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.fin_values_injective
    rw [Map.map_map, OfFn.Basic.map_ofFn]
    have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.indices_range
      evaluated.retained.length 0
    have equal : List.ofFn (fun i : Fin evaluated.retained.length => i.val) =
        List.ofFn (fun i : Fin evaluated.retained.length => 0 + i.val) :=
      OfFn.Basic.ofFn_congr (fun i => (Nat.zero_add i.val).symm)
    exact
      (reverse_parent_values
      grouped word).trans (equal.trans ranged).symm
  have entries := congrArg (List.map (IndexedSourceSplits.indexedEntry evaluated)) indices
  rw [Map.map_map, OfFn.Basic.map_ofFn] at entries
  exact entries.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.ofFn_read
    evaluated.retained)

/-- The certified reverse groups recover the complete original retained parent bank in its exact order. -/
theorem certify_reverse_parent_order (grouped : IndexedFragmentGrouping.IndexedOwnedGrouping evaluated data otherData
  items) (width : InverseRootPolynomial.Coordinate)
    (word : IndexedOwnedFragment.ReverseWord items) (fineEnough : ∀ item ∈ items, IndexedOwnedFragment.ReverseFineEnough
      item width)
    (parentWord :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedFragment.ReverseParentWord
      items) :
    (IndexedOwnedGrouping.certify_reverse grouped width word fineEnough).reverse.map ReverseGroupedSourceFragments.entry
      = evaluated.retained := by
  rw [Reverse.map_reverse, IndexedOwnedGrouping.certify_reverse_parents grouped, ← Reverse.map_reverse]
  exact
    reverse_parent_entries
    grouped parentWord

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder.IndexedOwnedGrouping

end
