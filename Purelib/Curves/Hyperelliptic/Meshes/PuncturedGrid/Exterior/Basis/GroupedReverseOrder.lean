module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping

open Purelib.Data.List

public section

/-! Recover retained parent order from maximal common-basis fragment groups. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder

open Purelib.Data
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

namespace IndexedFragment

/-- The retained fragment parent positions stay fixed or decrease by one, ending at original parent zero. -/
@[expose] def ReverseParentAfter (before : Nat) : List (IndexedFragments.IndexedFragment retained inputs outer data
  coefficients) → Prop
  | [] => before = 0
  | next :: rest => (next.parent.val = before ∨ before = next.parent.val + 1) ∧

        ReverseParentAfter
        next.parent.val rest

/-- The original indexed fragments traverse all retained parent positions from the last to the first. -/
@[expose] def ReverseParentWord : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients) → Prop
  | [] => (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length = 0
  | first :: rest => first.parent.val + 1 = (ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length ∧
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
    first.parent.val rest

end IndexedFragment

/-- The remaining parent positions decrease by exactly one and end at zero. -/
private def strictTail (before : Nat) : List Nat → Prop
  | [] => before = 0
  | next :: rest => before = next + 1 ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.strictTail next rest

/-- Reversing a strict descending parent chain gives its complete initial natural range. -/
private theorem strict_range (first : Nat) (rest : List Nat) (steps :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.strictTail first rest) :
    (first :: rest).reverse = List.range' 0 (first + 1) := by
  induction rest generalizing first with
  | nil => rw [show first = 0 from steps]; rfl
  | cons next rest ih =>
    rw [List.Reverse.reverse_cons, ih next steps.2, steps.1]
    simpa only [-eq_self, -iff_self, Nat.zero_add] using (List.Range.Basic.range'_succ 0 (next + 1)).symm

/-- Skipping original fragments of one parent preserves the remaining descending parent certificate. -/
private theorem skip_same (parent : Nat)
    (before after : List (IndexedFragments.IndexedFragment retained inputs outer data coefficients))
    (same : ∀ item ∈ before, item.parent.val = parent)
    (steps :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      parent (before ++ after)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      parent after := by
  induction before with
  | nil => exact steps
  | cons item rest ih =>
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      index (rest ++ after))
      (same item List.mem_cons_self)).mp steps.2
    exact ih (fun found member => same found (List.mem_cons_of_mem _ member)) remaining

/-- Maximal grouping removes stationary steps and retains strict descending original-parent positions. -/
private theorem strict_parents (rest : List (FragmentGrouping.IndexedRun retained inputs outer data coefficients))
    (run : FragmentGrouping.IndexedRun retained inputs outer data coefficients)
    (apart : IndexedRun.separated (run :: rest))
    (steps :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      run.parent.val (run.rest ++ (rest.map IndexedRun.items).flatten)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.strictTail run.parent.val (rest.map
      (fun run => run.parent.val)) := by
  induction rest generalizing run with
  | nil =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.skip_same run.parent.val run.rest
      []
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
  | cons next rest ih =>
    have boundary := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.skip_same
      run.parent.val run.rest ((next :: rest).map IndexedRun.items).flatten
      (fun item member => congrArg Fin.val (run.rest_parent item member)) steps
    have nextEq := congrArg Fin.val next.first_parent
    have different : next.first.parent.val ≠ run.parent.val := by
      intro equal
      exact apart.1 ((Fin.ext equal).symm.trans next.first_parent)
    have step : run.parent.val = next.first.parent.val + 1 := boundary.1.resolve_left different
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      index
      (next.rest ++ (rest.map IndexedRun.items).flatten)) nextEq).mp boundary.2
    exact ⟨step.trans (congrArg (fun n => n + 1) nextEq), ih next apart.2 remaining⟩

/-- Equality of natural-value lists identifies the complete original bounded-index lists. -/
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

/-- The offset bounded-index enumeration equals its consecutive natural range. -/
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

/-- Enumerating every bounded position reconstructs the exact original retained list. -/
private theorem ofFn_read {Item : Type u} (items : List Item) :
    List.ofFn (fun i : Fin items.length => items[i.val]'i.isLt) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact congrArg (List.cons head) ih

namespace IndexedGrouping
variable {items : List
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained inputs
  outer data coefficients)}

/-- The reversed grouped run-parent values enumerate every original occurrence parent once in ascending order. -/
theorem reverse_parent_values (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients items)
    (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentWord
      items) :
    grouped.runs.reverse.map (fun run => run.parent.val) = List.range' 0 (ParentIndices.occurrenceAt
      prepared.occurrences outer).compared.entered.cache.parents.length := by
  rw [← grouped.flattened] at word
  cases runsEq : grouped.runs with
  | nil =>
    rw [runsEq] at word
    change (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length = 0 at word
    change ([] : List Nat) = List.range' 0 (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length
    rw [word]
    rfl
  | cons run rest =>
    rw [runsEq] at word
    have firstEq : run.parent.val + 1 = (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length :=
      (congrArg (fun i : Fin (ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length => i.val + 1) run.first_parent).symm.trans word.1
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentAfter
      index
      (run.rest ++ (rest.map IndexedRun.items).flatten)) (congrArg Fin.val run.first_parent)).mp word.2
    have strict := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.strict_parents rest run
      ((congrArg IndexedRun.separated runsEq).mp grouped.separated) remaining
    have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.strict_range
      run.parent.val (rest.map (fun run => run.parent.val)) strict
    rw [List.Reverse.map_reverse]
    exact ranged.trans (congrArg (List.range' 0) firstEq)

/-- Recover source positions themselves, even when parent payloads repeat. -/
theorem reverse_parent_indices (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients
  items)
    (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentWord
      items) :
    grouped.runs.reverse.map IndexedRun.parent = List.ofFn (fun i : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length => i) := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.fin_values_injective
  rw [List.Map.map_map, OfFn.Basic.map_ofFn]
  have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.indices_range
    (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents.length 0
  have equal : List.ofFn (fun i : Fin (ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length => i.val) =
      List.ofFn (fun i : Fin (ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length => 0 + i.val) :=
    OfFn.Basic.ofFn_congr (fun i => (Nat.zero_add i.val).symm)
  exact
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedGrouping.reverse_parent_values
    grouped word).trans (equal.trans ranged).symm

/-- Reversing the certified physical run order recovers every retained source entry in its original order, including
repeated payloads. -/
theorem reverse_parent_entries (grouped : FragmentGrouping.IndexedGrouping retained inputs outer data coefficients
  items)
    (word :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentWord
      items) :
    grouped.runs.reverse.map (fun run => ParentBlocks.cacheParent (ParentIndices.occurrenceAt prepared.occurrences
      outer) run.parent) = (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents := by
  have indices :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedGrouping.reverse_parent_indices
    grouped word
  have entries := congrArg (List.map (ParentBlocks.cacheParent (ParentIndices.occurrenceAt prepared.occurrences outer)))
    indices
  rw [List.Map.map_map, OfFn.Basic.map_ofFn] at entries
  exact entries.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.ofFn_read
    (ParentIndices.occurrenceAt prepared.occurrences outer).compared.entered.cache.parents)

end IndexedGrouping

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
