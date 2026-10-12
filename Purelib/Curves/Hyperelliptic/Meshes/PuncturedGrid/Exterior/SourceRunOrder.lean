module
import Purelib.Data.Nat.Addition
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunEndpoints
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

public section

/-! The maximal physical runs enumerate the original parent block exactly,
in the orientation retained by the occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
open Purelib.Data.List
open Purelib.Data.Rat

/-- The next original parent position advances by one in the retained traversal direction. -/
private def parentStep (forward : Bool) (before after : Nat) : Prop :=
  if forward then after = before + 1 else before = after + 1

/-- The remaining parent positions take strict oriented unit steps and finish at the supplied last position. -/
private def strictParentTail (forward : Bool) (before last : Nat) : List Nat → Prop
  | [] => before = last
  | next :: rest => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentStep forward before next ∧
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.strictParentTail forward next last rest

/-- The oriented first and last retained parent positions bound the exact requested offset range. -/
@[expose] def parentAnchors (forward : Bool) (first last offset count : Nat) : Prop :=
  if forward then first = offset ∧ last + 1 = offset + count
  else last = offset ∧ first + 1 = offset + count

/-- A list of strict oriented parent steps is the corresponding ascending or reversed consecutive natural range. -/
private theorem strict_range (forward : Bool) (first last : Nat) (rest : List Nat)
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.strictParentTail forward first last
      rest) :
    if forward then first :: rest = List.range' first (rest.length + 1) ∧ last = first + rest.length
    else first :: rest = (List.range' last (rest.length + 1)).reverse ∧ first = last + rest.length := by
  induction rest generalizing first with
  | nil =>
    cases forward with
    | true => exact ⟨rfl, steps.symm⟩
    | false => exact ⟨congrArg (fun n => [n]) steps, steps⟩
  | cons next rest ih =>
    have tail := ih next steps.2
    cases forward with
    | true =>
      have step : next = first + 1 := steps.1
      constructor
      · exact congrArg (List.cons first) (tail.1.trans
          (congrArg (fun start => List.range' start (rest.length + 1)) step))
      · exact tail.2.trans ((congrArg (fun n => n + rest.length) step).trans
          ((Nat.add_assoc _ _ _).trans (congrArg (Nat.add first) (Nat.add_comm 1 rest.length))))
    | false =>
      have step : first = next + 1 := steps.1
      have distance : first = last + (rest.length + 1) :=
        step.trans ((congrArg (fun n => n + 1) tail.2).trans (Nat.add_assoc _ _ _))
      constructor
      · have reverse : (List.range' last ((rest.length + 1) + 1)).reverse =
            (last + (rest.length + 1)) :: (List.range' last (rest.length + 1)).reverse := by
          rw [Range.Basic.range'_succ, Data.List.Reverse.reverse_append]
          rfl
        exact (congrArg₂ List.cons distance tail.1).trans reverse.symm
      · exact distance

/-- The original endpoint anchors identify the strict parent list with the exact offset range in its retained
orientation. -/
private theorem anchored_range (forward : Bool) (first last offset count : Nat) (rest : List Nat)
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.strictParentTail forward first last
      rest) (anchors : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentAnchors forward first
      last offset count) :
    first :: rest = if forward then List.range' offset count else (List.range' offset count).reverse := by
  have ranged := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.strict_range forward first last rest
    steps
  cases forward with
  | true =>
    have length : rest.length + 1 = count := Data.Nat.Addition.add_left_cancel
      (((Nat.add_assoc offset rest.length 1).symm.trans
        (congrArg (fun n => n + 1) ((congrArg (fun n => n + rest.length) anchors.1.symm).trans ranged.2.symm))).trans
          anchors.2)
    exact ranged.1.trans (congrArg₂ (fun start count => List.range' start count) anchors.1 length)
  | false =>
    have length : rest.length + 1 = count := Data.Nat.Addition.add_left_cancel
      (((Nat.add_assoc offset rest.length 1).symm.trans
        (congrArg (fun n => n + 1) ((congrArg (fun n => n + rest.length) anchors.1.symm).trans ranged.2.symm))).trans
          anchors.2)
    exact ranged.1.trans (congrArg List.reverse (congrArg₂ (fun start count => List.range' start count) anchors.1
      length))

/-- Equality of natural-value lists identifies the complete original bounded-index lists. -/
private theorem fin_values_injective {count : Nat} (first last : List (Fin count))
    (equal : first.map Fin.val = last.map Fin.val) : first = last := by
  induction first generalizing last with
  | nil => cases last with
    | nil => rfl
    | cons => cases equal
  | cons first rest ih =>
    cases last with
    | nil => cases equal
    | cons last tail =>
      have parts := List.cons.inj equal
      exact congrArg₂ List.cons (Fin.ext parts.1) (ih tail parts.2)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {comparison : prepared.ClosedBoundaryComparison other requested minimum} {vertical : Bool}

/-- The retained chord parent positions stay fixed or advance one position in the supplied orientation, ending at the
designated parent. -/
private def sourceParentTail (forward : Bool) (before last : Nat) : List (SourceChordRuns.StoredSourceChord comparison
  vertical) → Prop
  | [] => before = last
  | next :: rest => (next.2.index.val = before ∨
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentStep forward before next.2.index.val) ∧
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward
        next.2.index.val last rest

/-- Skipping original chords of the same parent preserves the remaining oriented parent-step certificate. -/
private theorem sourceParentTail_skip (forward : Bool) (parent last : Nat)
    (before after : List (SourceChordRuns.StoredSourceChord comparison vertical))
    (same : ∀ chord ∈ before, chord.2.index.val = parent)
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward parent last
      (before ++ after)) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward
      parent last after := by
  induction before with
  | nil => exact steps
  | cons chord rest ih =>
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward index last (rest ++
      after))
      (same chord List.mem_cons_self)).mp steps.2
    exact ih (fun found member => same found (List.mem_cons_of_mem chord member)) remaining

/-- The adjacent steps of an original indexed chord bank certify its complete oriented parent tail. -/
private theorem sourceParentTail_ofFn {n : Nat} (forward : Bool) (source : Fin (n + 1) →
  SourceChordRuns.StoredSourceChord comparison vertical)
    (steps : ∀ i : Fin n, (source i.succ).2.index.val = (source i.castSucc).2.index.val ∨
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentStep forward (source
        i.castSucc).2.index.val (source i.succ).2.index.val) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward (source 0).2.index.val
      (source (Fin.last n)).2.index.val
      (List.ofFn (fun i : Fin n => source i.succ)) := by
  induction n with
  | zero => exact rfl
  | succ n ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨steps 0, ih (fun i => source i.succ) (fun i => steps i.succ)⟩

/-- A step between distinct retained positions must use the nonstationary alternative. -/
private theorem remove_stationary {before after : Nat} {step : Prop}
    (different : after ≠ before) (next : after = before ∨ step) : step :=
  next.elim (fun same => (different same).elim) id

namespace SourceChordRun

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun in
/-- Maximal grouping of the original chord word gives strict oriented steps between its retained run parents. -/
private theorem strict_parents (rest : List (SourceChordRuns.SourceChordRun comparison vertical)) (run :
  SourceChordRuns.SourceChordRun comparison vertical)
    (forward : Bool) (last : Nat) (apart : SourceChordRun.separated (run :: rest))
    (steps : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward run.parent.val
      last (run.rest ++ (rest.map chords).flatten)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.strictParentTail forward run.parent.val last
      (rest.map (fun run => run.parent.val)) := by
  induction rest generalizing run with
  | nil =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail_skip forward
      run.parent.val last run.rest []
      (fun chord member => congrArg Fin.val (run.rest_parent chord member)) steps
  | cons next rest ih =>
    have boundary := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail_skip forward
      run.parent.val last run.rest ((next :: rest).map chords).flatten
      (fun chord member => congrArg Fin.val (run.rest_parent chord member)) steps
    have nextEq := congrArg Fin.val next.first_parent
    have different : next.first.2.index.val ≠ run.parent.val := by
      intro equal
      exact apart.1 ((Fin.ext equal).symm.trans next.first_parent)
    have strict := (congrArg (fun index => Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentStep
      forward run.parent.val index) nextEq).mp
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.remove_stationary different boundary.1)
    have remaining := (congrArg (fun index =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward index last
      (next.rest ++ (rest.map chords).flatten)) nextEq).mp boundary.2
    exact ⟨strict, ih next apart.2 remaining⟩

end SourceChordRun

namespace SourceChordGrouping

/-- The grouped original indexed chord bank enumerates the exact anchored parent range in its retained orientation. -/
theorem parent_order_ofFn {n : Nat} {source : Fin (n + 1) → SourceChordRuns.StoredSourceChord comparison vertical}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical (List.ofFn source)) (forward : Bool) (offset
      count : Nat)
    (steps : ∀ i : Fin n, (source i.succ).2.index = (source i.castSucc).2.index ∨
      if forward then (source i.succ).2.index.val = (source i.castSucc).2.index.val + 1
      else (source i.castSucc).2.index.val = (source i.succ).2.index.val + 1)
    (anchors : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentAnchors forward (source
      0).2.index.val (source (Fin.last n)).2.index.val offset count) :
    grouped.runs.map (fun run => run.parent.val) =
      if forward then List.range' offset count else (List.range' offset count).reverse := by
  have word := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail_ofFn forward source
    (fun i =>
    (steps i).elim (fun same => Or.inl (congrArg Fin.val same)) Or.inr)
  have flattened := grouped.flattened.trans (OfFn.Basic.ofFn_succ (function := source))
  cases runsEq : grouped.runs with
  | nil =>
    rw [runsEq] at flattened
    cases flattened
  | cons run rest =>
    rw [runsEq] at flattened
    have heads := List.cons.inj flattened
    have firstEq := (congrArg Fin.val run.first_parent).symm.trans
      (congrArg (fun chord : SourceChordRuns.StoredSourceChord comparison vertical => chord.2.index.val) heads.1)
    have remaining := (congrArg₂ (fun index chords =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.sourceParentTail forward index (source
        (Fin.last n)).2.index.val chords)
      firstEq.symm heads.2.symm).mp word
    have strict := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.strict_parents rest
      run forward (source (Fin.last n)).2.index.val
      ((congrArg SourceChordRun.separated runsEq).mp grouped.separated) remaining
    have runAnchors := (congrArg (fun first =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.parentAnchors forward first (source (Fin.last
      n)).2.index.val offset count)
      firstEq.symm).mp anchors
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.anchored_range forward run.parent.val
      (source (Fin.last n)).2.index.val offset count
      (rest.map (fun run => run.parent.val)) strict runAnchors

/-- The grouped run parents equal the original bounded parent-index bank in forward or reversed order. -/
theorem parent_indices_order {chords : List (SourceChordRuns.StoredSourceChord comparison vertical)}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical chords) (forward : Bool)
    (indices : List (Fin comparison.original.plans.length)) {offset count : Nat}
    (values : indices.map Fin.val = List.range' offset count)
    (order : grouped.runs.map (fun run => run.parent.val) =
      if forward then List.range' offset count else (List.range' offset count).reverse) :
    grouped.runs.map SourceChordRun.parent = if forward then indices else indices.reverse := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns.fin_values_injective
  rw [Data.List.Map.map_map]
  cases forward with
  | true => exact order.trans values.symm
  | false =>
    exact order.trans ((congrArg List.reverse values.symm).trans (Data.List.Reverse.map_reverse Fin.val indices).symm)

/-- Reading the grouped run increments preserves the exact retained oriented parent-index order. -/
theorem parent_increments_order {chords : List (SourceChordRuns.StoredSourceChord comparison vertical)}
    (grouped : SourceChordRuns.SourceChordGrouping comparison vertical chords) (forward : Bool)
    (indices : List (Fin comparison.original.plans.length))
    (order : grouped.runs.map SourceChordRun.parent = if forward then indices else indices.reverse) :
    grouped.runs.map (fun run => run.parentIncrement forward) =
      (if forward then indices else indices.reverse).map (SourceChordRuns.sourceParentIncrement comparison forward) :=
        by
  have mapped := congrArg (List.map (SourceChordRuns.sourceParentIncrement comparison forward)) order
  rw [Data.List.Map.map_map] at mapped
  exact mapped

end SourceChordGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
